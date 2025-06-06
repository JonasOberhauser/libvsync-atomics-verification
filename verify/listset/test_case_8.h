/*
 * Copyright (C) Huawei Technologies Co., Ltd. 2024-2025. All rights reserved.
 * SPDX-License-Identifier: MIT
 */


#ifndef VSYNC_TEST_CASE_H
#define VSYNC_TEST_CASE_H
/* goal:
 * removing from head, middle, tail
 */
const vsize_t g_lst_idx = 0;
void
pre(void)
{
    ASSERT(lst_add(MAIN_TID, g_lst_idx, 1));
}
void
t0(vsize_t tid)
{
    /* add existing value */
    ASSERT(!lst_add(tid, g_lst_idx, 1));
}
void
t1(vsize_t tid)
{
    /* add non exisitng value at the head */
    ASSERT(lst_add(tid, g_lst_idx, 0));
    ASSERT(lst_con(tid, g_lst_idx, 0));
}
void
t2(vsize_t tid)
{
    /* remove non existing value */
    ASSERT(!lst_rem(tid, g_lst_idx, 2));
    lst_clean(tid);
}
void
post(void)
{
    lst_verify_traces(g_lst_idx);
}
#endif
