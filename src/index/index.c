/*
* Copyright 2018-2019 Redis Labs Ltd. and Contributors
*
* This file is available under the Apache License, Version 2.0,
* modified with the Commons Clause restriction.
*/

#include "index.h"
#include "index_type.h"

RedisModuleKey* _index_LookupKey(RedisModuleCtx *ctx, const char *graph, const char *label, const char *property, bool write_access) {
  char *strKey;
  int keylen = asprintf(&strKey, "%s_%s_%s_%s", INDEX_PREFIX, graph, label, property);

  RedisModuleString *rmIndexId = RedisModule_CreateString(ctx, strKey, keylen);
  free(strKey);

  int mode = write_access ? REDISMODULE_WRITE : REDISMODULE_READ;
  RedisModuleKey *key = RedisModule_OpenKey(ctx, rmIndexId, mode);
  RedisModule_FreeString(ctx, rmIndexId);

  return key;
}

/* Memory management and comparator functions that get attached to
 * string and numeric skiplists as function pointers. */
int compareNodes(NodeID a, NodeID b) {
  return a - b;
}

int compareStrings(SIValue *a, SIValue *b) {
  return strcmp(a->stringval, b->stringval);
}

int compareNumerics(SIValue *a, SIValue *b) {
  return a->doubleval - b->doubleval;
}

/* The index must maintain its own copy of the indexed SIValue
 * so that it becomes outdated but not broken by updates to the property. */
void cloneKey(SIValue **property) {
  SIValue *clone = *property;
  *clone = SI_Clone(*clone);
}

void freeKey(SIValue *key) {
  SIValue_Free(key);
}

/* Construct key and retrieve index from Redis keyspace */
Index* Index_Get(RedisModuleCtx *ctx, const char *graph, const char *label, const char *property) {
  Index *idx = NULL;
  // Open key with read-only access
  RedisModuleKey *key = _index_LookupKey(ctx, graph, label, property, false);

  if (RedisModule_ModuleTypeGetType(key) == IndexRedisModuleType) {
    idx = RedisModule_ModuleTypeGetValue(key);
  }

  RedisModule_CloseKey(key);

  return idx;
}

int Index_Delete(RedisModuleCtx *ctx, const char *graphName, const char *label, const char *prop) {
  // Open key with write access
  RedisModuleKey *key = _index_LookupKey(ctx, graphName, label, prop, true);
  if (RedisModule_ModuleTypeGetType(key) != IndexRedisModuleType) {
    // Reply with error if this key does not exist or does not correspond to an index object
    RedisModule_CloseKey(key);
    return INDEX_FAIL;
  }

  Index *idx = RedisModule_ModuleTypeGetValue(key);

  // The DeleteKey routine will free the index and skiplists
  RedisModule_DeleteKey(key);
  return INDEX_OK;
}

void initializeSkiplists(Index *index) {
  index->string_sl = skiplistCreate(compareStrings, compareNodes, cloneKey, freeKey);
  index->numeric_sl = skiplistCreate(compareNumerics, compareNodes, cloneKey, freeKey);
}

/* buildIndex allocates an Index object and populates it with a label-property pair
 * by traversing a label matrix with a TuplesIter. */
Index* buildIndex(Graph *g, const GrB_Matrix label_matrix, const char *label, const char *prop_str) {
  Index *index = malloc(sizeof(Index));

  index->label = strdup(label);
  index->property = strdup(prop_str);

  initializeSkiplists(index);

  TuplesIter *it = TuplesIter_new(label_matrix);

  Node *node;
  EntityProperty *prop;

  skiplist *sl;
  NodeID node_id;
  int found;
  int prop_index = 0;
  while(TuplesIter_next(it, NULL, &node_id) != TuplesIter_DEPLETED) {
    node = Graph_GetNode(g, node_id);
    // If the sought property is at a different offset than it occupied in the previous node,
    // then seek and update
    if (strcmp(prop_str, node->properties[prop_index].name)) {
      found = 0;
      for (int i = 0; i < node->prop_count; i ++) {
        prop = node->properties + i;
        if (!strcmp(prop_str, prop->name)) {
          prop_index = i;
          found = 1;
          break;
        }
      }
    } else {
      found = 1;
    }
    // The targeted property does not exist on this node
    if (!found) continue;

    prop = node->properties + prop_index;
    // This value will be cloned within the skiplistInsert routine if necessary
    SIValue *key = &prop->value;

    assert(key->type == T_STRING || key->type & SI_NUMERIC);
    sl = (key->type & SI_NUMERIC) ? index->numeric_sl: index->string_sl;
    skiplistInsert(sl, key, node_id);
  }

  TuplesIter_free(it);

  return index;
}

// Create and populate index for specified property
// (This function will create separate string and numeric indices if property has mixed types)
int Index_Create(RedisModuleCtx *ctx, const char *graphName, Graph *g, const char *label, const char *prop_str) {
  // Open key with write access
  RedisModuleKey *key = _index_LookupKey(ctx, graphName, label, prop_str, true);
  // Do nothing if this key already exists
  if (RedisModule_ModuleTypeGetType(key) != REDISMODULE_KEYTYPE_EMPTY) {
    RedisModule_CloseKey(key);
    return INDEX_FAIL;
  }

  LabelStore *store = LabelStore_Get(ctx, STORE_NODE, graphName, label);
  assert(store);
  const GrB_Matrix label_matrix = Graph_GetLabelMatrix(g, store->id);

  Index *idx = buildIndex(g, label_matrix, label, prop_str);
  RedisModule_ModuleTypeSetValue(key, IndexRedisModuleType, idx);
  RedisModule_CloseKey(key);

  return INDEX_OK;
}

/* Output text for EXPLAIN calls */
const char* Index_OpPrint(AST_IndexNode *indexNode) {
  switch(indexNode->operation) {
    case CREATE_INDEX:
      return "Create Index";
    default:
      return "Drop Index";
  }
}

/* Generate an iterator with no lower or upper bound. */
IndexIter* IndexIter_Create(Index *idx, SIType type) {
  skiplist *sl = type == T_STRING ? idx->string_sl : idx->numeric_sl;
  return skiplistIterateAll(sl);
}

/* Apply a filter to an iterator, modifying the appropriate bound if
 * it narrows the iterator range.
 * Returns 1 if the filter was a comparison type that can be translated into a bound
 * (effectively, any type but '!='), which indicates that it is now redundant. */
bool IndexIter_ApplyBound(IndexIter *iter, FT_PredicateNode *filter) {
  return skiplistIter_UpdateBound(iter, &filter->constVal, filter->op);
}

NodeID* IndexIter_Next(IndexIter *iter) {
  return skiplistIterator_Next(iter);
}

void IndexIter_Reset(IndexIter *iter) {
  skiplistIterate_Reset(iter);
}

void IndexIter_Free(IndexIter *iter) {
  skiplistIterate_Free(iter);
}

void Index_Free(Index *idx) {
  skiplistFree(idx->string_sl);
  skiplistFree(idx->numeric_sl);
  free(idx->label);
  free(idx->property);
  free(idx);
}

