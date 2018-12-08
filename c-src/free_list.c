#include "free_list.h"

void FreeList_Initialize (struct Free_List_Type *fl) {
	FREE_LIST_POINTER_TYPE i;
	fl->top = 0;
	for (i=0; i<FREE_LIST_CAPACITY-1; ++i) {
		fl->next[i] = i + 1;
	}
	fl->next[FREE_LIST_CAPACITY-1] = FREE_LIST_INVALID_POINTER;
}

FREE_LIST_POINTER_TYPE  FreeList_Allocate   (struct Free_List_Type *fl) {
	FREE_LIST_POINTER_TYPE ret = fl->top;
	if (ret != FREE_LIST_INVALID_POINTER) {
		fl->top       = fl->next[ret];
		fl->next[ret] = FREE_LIST_INVALID_POINTER;
	}
	return ret;
}


