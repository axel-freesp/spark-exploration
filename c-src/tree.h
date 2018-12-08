#pragma once

#include "free_list.h"
#define TREE_CAPACITY FREE_LIST_CAPACITY

typedef int KEY_TYPE;
typedef int VALUE_TYPE;

struct Node_Type {
	KEY_TYPE key;
	VALUE_TYPE value;
	struct Node_Type *left;
	struct Node_Type *right;
	struct Node_Type *parent;
};

struct Tree_Type {
	struct Free_List_Type free_list;
	struct Node_Type nodes[TREE_CAPACITY];
	struct Node_Type *root_node;
};

enum Tree_Status_Type {
	Ok,
	Out_Of_Memory
};

void Tree_Initialize(struct Tree_Type *tree);
enum Tree_Status_Type Tree_Insert(struct Tree_Type *tree, KEY_TYPE key, VALUE_TYPE value);

static inline int Tree_IsEmpty(const struct Tree_Type *tree) {
	return tree->root_node == 0;
}
