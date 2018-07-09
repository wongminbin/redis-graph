#include <assert.h>
#include "../value.h"
#include "filter_tree.h"
#include "../parser/grammar.h"
#include "../query_executor.h"
#include "../rmutil/vector.h"

// TODO allows for better printing, but may not belong here
// Lookup map for converting op numbers to strings
const char* ops[] = {"", "OR", "AND", "ADD", "DASH", "MUL", "DIV", "EQ", "GT", "GE", "LT", "LE"};

int static inline IsNodeConstantPredicate(const FT_FilterNode *node) {
    return (node->t == FT_N_PRED && node->pred.t == FT_N_CONSTANT);
}

int static inline IsNodeVaryingPredicate(const FT_FilterNode *node) {
    return (node->t == FT_N_PRED && node->pred.t == FT_N_VARYING);
}

int static inline IsNodePredicate(const FT_FilterNode *node) {
    return node->t == FT_N_PRED;
}

FT_FilterNode* CreateVaryingFilterNode(const char *LAlias, const char *LProperty, const char *RAlias, const char *RProperty, int op) {
    // At the moment only numerical comparison is supported
    // Assuming compared data is double.
    // TODO: support all types of possible SIValues.
    CmpFunc compareFunc = cmp_double;
    FT_FilterNode* filterNode = (FT_FilterNode*)malloc(sizeof(FT_FilterNode));

    // Create predicate node
    filterNode->t = FT_N_PRED;
    filterNode->pred.t = FT_N_VARYING;

    filterNode->pred.Lop.alias = strdup(LAlias);
    filterNode->pred.Lop.property = strdup(LProperty);
    filterNode->pred.Lop.e = NULL;
    filterNode->pred.Rop.alias = strdup(RAlias);
    filterNode->pred.Rop.property = strdup(RProperty);
    filterNode->pred.Rop.e = NULL;

    filterNode->pred.op = op;
    filterNode->pred.cf = compareFunc;
    return filterNode;
}

FT_FilterNode* CreateConstFilterNode(const char *alias, const char *property, int op, SIValue val) {
    CmpFunc compareFunc = NULL;
    FT_FilterNode* filterNode = (FT_FilterNode*)malloc(sizeof(FT_FilterNode));

    // Find out which compare function should we use.
    switch(val.type) {
        case T_STRING:
            compareFunc = cmp_string;
            break;
        case T_INT32:
            compareFunc = cmp_int;
            break;
        case T_INT64:
            compareFunc = cmp_long;
            break;
        case T_UINT:
            compareFunc = cmp_uint;
            break;
        case T_BOOL:
            compareFunc = cmp_int;
            break;
        case T_FLOAT:
            compareFunc = cmp_float;
            break;
        case T_DOUBLE:
            compareFunc = cmp_double;
            break;
        default:
            compareFunc = NULL;
            break;
    }

    // Couldn't figure out which compare function to use.
    if(compareFunc == NULL) {
        // ERROR.
        return NULL;
    }

    // Create predicate node
    filterNode->t = FT_N_PRED;
    filterNode->pred.t = FT_N_CONSTANT;

    filterNode->pred.Lop.alias = strdup(alias);
    filterNode->pred.Lop.property = strdup(property);
    filterNode->pred.Lop.e = NULL;

    filterNode->pred.op = op;
    filterNode->pred.constVal = val;
    filterNode->pred.cf = compareFunc;
    return filterNode;
}

FT_FilterNode* CreateConditionNode(int op) {
  FT_FilterNode *n = malloc(sizeof(FT_FilterNode));

  n->t = FT_N_COND;
  n->cond.allocated_count = 2;
  n->cond.children = malloc(2 * sizeof(FT_FilterNode));
  n->cond.child_count = 0;
  n->cond.op = op;

  return n;
}

void FT_AddPredicate(const AST_FilterNode *root, FT_FilterNode *ft) {
  assert(ft && ft->t == FT_N_COND);
  if (ft->cond.allocated_count <= ft->cond.child_count) {
    ft->cond.allocated_count *= 2;
    realloc(ft->cond.children, ft->cond.allocated_count * sizeof(FT_FilterNode*));
  }

  FT_FilterNode *n = malloc(sizeof(FT_FilterNode));
  n->t = N_PRED;

  if(root->pn.t == N_CONSTANT) {
    n = CreateConstFilterNode(root->pn.alias, root->pn.property,
        root->pn.op, root->pn.constVal);
  } else {
    n = CreateVaryingFilterNode(root->pn.alias, root->pn.property,
        root->pn.nodeVal.alias, root->pn.nodeVal.property, root->pn.op);
  }
  ft->cond.children[ft->cond.child_count] = n;
  ft->cond.child_count ++;
}

FT_FilterNode* BuildFiltersTree(const AST_FilterNode *root, FT_FilterNode *ft) {
  /* TODO This approach always has a node of type cond as the root.
     If there is only one filter, it will be an AND with that single predicate
     as a child.
     I feel like that may allow for simpler traversals, but it may not, in which case
     this approach should be updated.
   */
  if (ft == NULL) {
    // TODO make real UNSET op type
    ft = CreateConditionNode(0);
  }

  if(root->t == N_PRED) {
    if (ft->cond.op == 0) ft->cond.op = AND;
    FT_AddPredicate(root, ft);
    return ft;
  }

  if (ft->cond.op == 0) ft->cond.op = root->cn.op;

  if (root->cn.op == ft->cond.op) {
    // Broaden the current node while the operation (AND/OR) is same
    BuildFiltersTree(root->cn.left, ft);
    BuildFiltersTree(root->cn.right, ft);
  } else {
    // Deepen the tree when operation differs
    FT_FilterNode *new_internal = CreateConditionNode(root->cn.op);
    /* TODO:
     * The OpenCypher docs are not very explicit about filter operation precedence.
     * This link provides good experimental rules for Neo4j:
     * https://stackoverflow.com/questions/39239723/neo4j-cypher-query-language-order-of-operations-for-boolean-expressions
     * Fundamentally, without parentheses (which we don't yet support), AND operations are of higher precedence than OR,
     * and precedence is otherwise set by query order.
     * Currently, this approach considers AND and OR to be of equal precedence, and exclusively sets by query order.
     * Should add parens support and break ties in favor of ANDs
     */
    BuildFiltersTree(root->cn.left, new_internal);
    BuildFiltersTree(root->cn.right, new_internal);
    ft->cond.children[ft->cond.child_count++] = new_internal;
    // TODO When parens and AND precedence are in play, we must be able to demote children to lower level
    /*
     * if (new_internal->cond.child_count > 1) { // not quite like this, because we build conditionals before preds
     *   FT_MigrateChild(new_internal, ft, ft->cond.child_count - 1);
     * }
     */

  }

  return ft;
}

/* Applies a single filter to a single result.
 * Compares given values, tests if values maintain desired relation (op) */
int _applyFilter(SIValue* aVal, SIValue* bVal, CmpFunc f, int op) {
    /* TODO: Make sure values are of the same type
     * TODO: Make sure values type confirms with compare function. */
    int rel = f(aVal, bVal);

    switch(op) {
        case EQ:
        return rel == 0;

        case GT:
        return rel > 0;

        case GE:
        return rel >= 0;

        case LT:
        return rel < 0;

        case LE:
        return rel <= 0;

        case NE:
        return rel != 0;

        default:
        /* Op should be enforced by AST. */
        assert(0);
    }
    /* We shouldn't reach this point. */
    return 0;
}

int _applyPredicateFilters(const FT_FilterNode* root) {
    /* A op B
     * Extract both A and B values. */
    GraphEntity *entity;
    SIValue *aVal;
    SIValue *bVal;

    if(IsNodeConstantPredicate(root)) {
        bVal = (SIValue *)&root->pred.constVal;
    } else {
        entity = *root->pred.Rop.e;
        assert (entity && entity->id != INVALID_ENTITY_ID);
        bVal = GraphEntity_Get_Property(entity, root->pred.Rop.property);
    }

    entity = *root->pred.Lop.e;
    assert(entity && entity->id != INVALID_ENTITY_ID);
    aVal = GraphEntity_Get_Property(entity, root->pred.Lop.property);

    return _applyFilter(aVal, bVal, root->pred.cf, root->pred.op);
}

int FilterTree_applyFilters(const FT_FilterNode* root) {
    /* Handle predicate node. */
    if(IsNodePredicate(root)) {
        return _applyPredicateFilters(root);
    }

    /* root->t == FT_N_COND, visit left subtree. */
    int pass = FilterTree_applyFilters(LeftChild(root));
    
    if(root->cond.op == AND && pass == 1) {
        /* Visit right subtree. */
        pass *= FilterTree_applyFilters(RightChild(root));
    }

    if(root->cond.op == OR && pass == 0) {
        /* Visit right subtree. */
        pass = FilterTree_applyFilters(RightChild(root));
    }

    return pass;
}

void FilterTree_bindEntities(FT_FilterNode* root, const QueryGraph *g) {
    switch(root->t) {
        case FT_N_COND:
            FilterTree_bindEntities(root->cond.left, g);
            FilterTree_bindEntities(root->cond.right, g);
            break;
        case FT_N_PRED:
            root->pred.Lop.e = QueryGraph_GetEntityRef(g, root->pred.Lop.alias);
            if(root->pred.t == FT_N_VARYING) {
                root->pred.Rop.e = QueryGraph_GetEntityRef(g, root->pred.Rop.alias);
            }
            break;
        default:
            assert(0);
            break;
    }
}

void _FilterTree_CollectAliases(const FT_FilterNode *root, TrieMap *aliases) {
    if(root == NULL) return;

    switch(root->t) {
        case FT_N_COND:
        {
            for (int i = 0; i < root->cond.child_count; i ++) {
                _FilterTree_CollectAliases(root->cond.children[i], aliases);
            }
            break;
        }
        case FT_N_PRED:
        {
            // Add alias to triemap.
            char *alias = root->pred.Lop.alias;
            TrieMap_Add(aliases, alias, strlen(alias), NULL, NULL);
            if(root->pred.t == FT_N_VARYING) {
                alias = root->pred.Rop.alias;
                TrieMap_Add(aliases, alias, strlen(alias), NULL, NULL);
            }
            break;
        }
        default:
        {
            assert(0);
            break;
        }
    }
}

Vector *FilterTree_CollectAliases(const FT_FilterNode *root) {
    TrieMap *t = NewTrieMap();
    _FilterTree_CollectAliases(root, t);

    Vector *aliases = NewVector(char*, t->cardinality);
    TrieMapIterator *it = TrieMap_Iterate(t, "", 0);
    
    char *ptr;
    tm_len_t len;
    void *value;

    while(TrieMapIterator_Next(it, &ptr, &len, &value)) {
        Vector_Push(aliases, strdup(ptr));
    }

    TrieMap_Free(t, NULL);
    return aliases;
}

void _FilterTree_Print(const FT_FilterNode *root, int indent) {
    if (root == NULL) return;

    printf("%*s", indent, "");
    if(IsNodeConstantPredicate(root)) {
        char value[64] = {0};
        SIValue_ToString(root->pred.constVal, value, 64);
        printf("%s.%s %s %s\n",
            root->pred.Lop.alias,
            root->pred.Lop.property,
            ops[root->pred.op],
            value);
        return;
    }
    if(IsNodeVaryingPredicate(root)) {
        printf("%s.%s %s %s.%s\n",
            root->pred.Lop.alias,
            root->pred.Lop.property,
            ops[root->pred.op],
            root->pred.Rop.alias,
            root->pred.Rop.property);
        return;
    }

    // conditional node
    FT_ConditionNode in = root->cond;
    printf("%s\n", ops[in.op]);
    for (int i = 0; i < in.child_count; i ++) {
        _FilterTree_Print(in.children[i], indent + 4);
    }
}

void FilterTree_Print(const FT_FilterNode *root) {
    if(root == NULL) {
        printf("empty filter tree\n");
        return; 
    }
    _FilterTree_Print(root, 0);
}

void _FreeVaryingFilterNode(FT_PredicateNode node) {
    free(node.Lop.alias);
    free(node.Lop.property);
    free(node.Rop.alias);
    free(node.Rop.property);
}

void _FreeConstFilterNode(FT_PredicateNode node) {
    free(node.Lop.alias);
    free(node.Lop.property);
}

void _FilterTree_FreePredNode(FT_PredicateNode node) {
    if(node.t == FT_N_CONSTANT) {
        _FreeConstFilterNode(node);
    } else {
        _FreeVaryingFilterNode(node);
    }
}

void FilterTree_Free(FT_FilterNode *root) {
    if(root == NULL) { return; }
    if(IsNodePredicate(root)) {
        _FilterTree_FreePredNode(root->pred);
    } else {
        for (int i = 0; i < root->cond.child_count; i ++) {
            FilterTree_Free(root->cond.children[i]);
            free(root->cond.children);
        }
    }

    free(root);
}
