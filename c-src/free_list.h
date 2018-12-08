#pragma once

#ifndef FREE_LIST_CAPACITY
#error Missing FREE_LIST_CAPACITY
#endif

#define FREE_LIST_INVALID_POINTER (-1)
#define FREE_LIST_IS_VALID_POINTER(p) (0 <= (p) && (p) < FREE_LIST_CAPACITY)

typedef int FREE_LIST_POINTER_TYPE;

struct Free_List_Type {
	FREE_LIST_POINTER_TYPE top;
	FREE_LIST_POINTER_TYPE next[FREE_LIST_CAPACITY];
};

void FreeList_Initialize (struct Free_List_Type *fl);

FREE_LIST_POINTER_TYPE FreeList_Allocate(struct Free_List_Type *fl);

static inline int FreeList_IsEmpty(const struct Free_List_Type *list) {
	return list->top == FREE_LIST_INVALID_POINTER;
}
