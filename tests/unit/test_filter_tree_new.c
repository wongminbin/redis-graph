#include <stdio.h>
#include <string.h>
#include "assert.h"
// #include "../../src/rmutil/vector.h"
// #include "../../src/parser/grammar.h"
#include "../../src/filter_tree/filter_tree.h"
#include "../../src/parser/ast.h"
#include "../../src/query_executor.h"

extern FT_Node* NewBuildFiltersTree(const AST_FilterNode *root, FT_Node *ft);
extern void FT_Print(FT_Node *root, int indent);

AST_Query* build_ast(char *query) {
  char *errMsg = NULL;
  AST_Query *ast = ParseQuery(query, strlen(query), &errMsg);
  assert(ast != NULL);

  return ast;
}

void execute(char *query) {
  printf("%s\n\n", query);
  AST_Query *ast = build_ast(query);
  
  printf("New tree:\n");
  FT_Node *new_tree = NewBuildFiltersTree(ast->whereNode->filters, NULL);
  FT_Print(new_tree, 0);

  printf("\nOld tree:\n");
  FT_FilterNode *old_tree = BuildFiltersTree(ast->whereNode->filters);
  FilterTree_Print(old_tree);

}

void run_queries() {
  char *query = "MATCH (p:person) WHERE p.age < 55";
  execute(query);

  query = "MATCH (p:person) WHERE p.age < 55 AND p.name = 'Rawr'";
  execute(query);

  query = "MATCH (p:person) WHERE p.age < 55 OR p.name = 'Rawr'";
  execute(query);

  query = "MATCH (p:person) WHERE p.age < 55 AND p.age < 70 OR p.name = 'Rawr'";
  execute(query);

  query = "MATCH (p:person) WHERE p.age < 55 AND p.age < 70 AND p.name = 'Rawr' AND p.name = 'eek'";
  execute(query);

  query = "MATCH (p:person) WHERE p.age < 55 AND p.age < 70 OR p.name = 'Rawr' OR p.name = 'eek'";
  execute(query);

  query = "MATCH (p:person) WHERE p.age < 55 AND p.age < 70 OR p.name = 'Rawr' AND p.name = 'eek'";
  execute(query);

  // TODO I'm not sure if this one is being built properly
  query = "MATCH (p:person) WHERE p.age < 55 OR p.age < 70 AND p.name = 'Rawr' OR p.name = 'eek'";
  execute(query);

  // varying (largely untested)
  query = "MATCH (p:person) WHERE p.age < p.name AND p.age < 70 OR p.name = 'Rawr' AND p.name = 'eek'";
  execute(query);

}

int main() {
  printf("\n\n");
  run_queries();
  printf("\n\n");
}
