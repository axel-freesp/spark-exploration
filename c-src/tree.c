#include "tree.h"

void Tree_Initialize(struct Tree_Type *tree){
	FreeList_Initialize(&tree->free_list);
	tree->root_node = 0;
}

struct Node_Type *Allocate_Node(struct Tree_Type *tree, KEY_TYPE key, VALUE_TYPE value) {
	FREE_LIST_POINTER_TYPE node_idx = FreeList_Allocate(&tree->free_list);
	struct Node_Type *node = &tree->nodes[node_idx];
	node->key = key;
	node->value = value;
	node->left = 0;
	node->right = 0;
	node->parent = 0;
	return node;
}

static void Insert_Node(struct Tree_Type *tree, struct Node_Type *node) {
	struct Node_Type *parent = tree->root_node;
	for (;;) {
		if (node->key < parent->key) {
			if (parent->left == 0) {
				parent->left = node;
				node->parent = parent;
				break;
			} else {
				parent = parent->left;
			}
		} else {
			if (parent->right == 0) {
				parent->right = node;
				node->parent = parent;
			} else {
				parent = parent->right;
			}
		}
	}
}

enum Tree_Status_Type Tree_Insert(struct Tree_Type *tree, KEY_TYPE key, VALUE_TYPE value) {
	enum Tree_Status_Type ret = Out_Of_Memory;
	if (! FreeList_IsEmpty(&tree->free_list)) {
		struct Node_Type *node = Allocate_Node(tree, key, value);
		if (tree->root_node == 0) {
			tree->root_node = node;
		} else {
			Insert_Node(tree, node);
		}
		ret = Ok;
	}
	return ret;
}

