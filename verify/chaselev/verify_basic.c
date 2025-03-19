/*
 * Copyright (C) Huawei Technologies Co., Ltd. 2025. All rights reserved.
 * SPDX-License-Identifier: MIT
 */

#include <stdlib.h>
#include <pthread.h>
#include <vsync/atomic.h>
#include <vsync/common/assert.h>
#include <vsync/queue/chaselev.h>
#include <test/thread_launcher.h>
#include <vsync/utils/math.h>

#define ARRAY_SIZE  1U
#define NUM_THREADS 4U

/* Tests the validity of deque operations enqueue, dequeue and steal by
 * asserting the correct status and correct indices after certain operations.
 * In the owner thread, enqueue will be executed first, therefore it checks for
 * OK status. The test also provides occasional noise, i.e. steal operations
 * from other threads. */

vdeque_t g_vdeque;
vdeque_array_t *g_arr;

static void
run_owner(void)
{
    vsize_t old_bottom, old_top, new_bottom, v = 1;
    vdeque_state_t status;
    void *r = NULL;

    // Owner enqueues first to assert OK status
    status = vdeque_push_bottom(&g_vdeque, &v);
    ASSERT(status == VDEQUE_STATE_OK);

    // Owner checks validity of enqueue
    old_bottom = vatomicsz_read_rlx(&g_vdeque.bottom);
    old_top    = vatomicsz_read_rlx(&g_vdeque.top);
    status     = vdeque_push_bottom(&g_vdeque, &v);
    new_bottom = vatomicsz_read_rlx(&g_vdeque.bottom);
    if (status == VDEQUE_STATE_OK) {
        ASSERT(new_bottom == old_bottom + 1);
    } else {
        ASSERT(new_bottom == old_bottom);
    }

    // Owner checks validity of dequeue
    old_bottom = vatomicsz_read_rlx(&g_vdeque.bottom);
    old_top    = vatomicsz_read_rlx(&g_vdeque.top);
    status     = vdeque_pop_bottom(&g_vdeque, &r);
    new_bottom = vatomicsz_read_rlx(&g_vdeque.bottom);

    if (status == VDEQUE_STATE_OK) {
        if (old_top == old_bottom - 1) {
            ASSERT(new_bottom == old_bottom);
        } else {
            ASSERT(new_bottom == old_bottom - 1);
        }
    } else {
        ASSERT(new_bottom == old_bottom);
    }
}

static void
run_stealer_check(void)
{
    vsize_t old_top, new_top;
    vdeque_state_t status;
    void *v1 = NULL;

    // Checks validity of dequeue - steal
    old_top = vatomicsz_read_rlx(&g_vdeque.top);
    status  = vdeque_steal(&g_vdeque, &v1);
    new_top = vatomicsz_read_rlx(&g_vdeque.top);
    if (status == VDEQUE_STATE_OK) {
        ASSERT(new_top > old_top);
    }
}

static void
run_stealer_noise(void)
{
    void *v = NULL;
    // Noise functionality
    vdeque_steal(&g_vdeque, &v);
    vdeque_steal(&g_vdeque, &v);
}

static void *
run(void *args)
{
    vsize_t tid = (vsize_t)(vuintptr_t)args;
    ASSERT(tid < NUM_THREADS);
    switch (tid) {
        case 0:
            // Only one thread is owner
            run_owner();
            break;
        default:
            if (VIS_ODD(tid)) {
                // Every other thread checks validity of dequeue
                run_stealer_check();
            } else {
                run_stealer_noise();
            }
            break;
    }
    return NULL;
}

/* Initializes global chase-lev deque */
static void
init(void)
{
    vsize_t array_size = vdeque_memsize(ARRAY_SIZE);
    g_arr              = (vdeque_array_t *)malloc(array_size);
    vdeque_init(&g_vdeque, g_arr, ARRAY_SIZE);
}

/* Checks validity of global chase-lev deque */
static void
pre(void)
{
    vsize_t b = vatomicsz_read_rlx(&g_vdeque.bottom);
    vsize_t t = vatomicsz_read_rlx(&g_vdeque.top);
    ASSERT(t == 0);
    ASSERT(b == 0);
}

int
main(void)
{
    init();
    pre();
    // Launch threads
    launch_threads(NUM_THREADS, run);
    free(g_arr);
    g_arr = NULL;
    return 0;
}
