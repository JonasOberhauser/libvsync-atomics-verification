/*
 * Copyright (C) Huawei Technologies Co., Ltd. 2023-2024. All rights reserved.
 * SPDX-License-Identifier: MIT
 */

/* !!!Warning: File generated by tmpl; DO NOT EDIT.!!! */
#include <vsync/atomic.h>
#include <vsync/common/assert.h>
#include <vsync/common/dbg.h>
#include <test/thread_launcher.h>
#define N  5
#define IT 10
vatomic64_t g_shared;
/*****************************************************************************
 * MultiThreadedTest: vatomic64_inc
 *****************************************************************************/
static inline void *
mt_atomic_inc_run(void *args)
{
	vsize_t tid = (vsize_t)(vuintptr_t)args;
	for (vsize_t i = 0; i < IT; i++) {
		vatomic64_inc(&g_shared);
	}
	V_UNUSED(tid);
	return NULL;
}
static inline void
mt_atomic_inc(void)
{
	vuint64_t init = VUINT32_MAX;
	vatomic64_init(&g_shared, init);
	launch_threads(N, mt_atomic_inc_run);
	/* calculate the expected value */
	vuint64_t expected = init + (N * IT);
	vuint64_t val	   = vatomic64_read(&g_shared);
	ASSERT(expected == val);
	V_UNUSED(expected, val);
}
/*****************************************************************************
 * MultiThreadedTest: vatomic64_dec
 *****************************************************************************/
static inline void *
mt_atomic_dec_run(void *args)
{
	vsize_t tid = (vsize_t)(vuintptr_t)args;
	for (vsize_t i = 0; i < IT; i++) {
		vatomic64_dec(&g_shared);
	}
	V_UNUSED(tid);
	return NULL;
}
static inline void
mt_atomic_dec(void)
{
	vuint64_t init = VUINT32_MAX;
	vatomic64_init(&g_shared, init);
	launch_threads(N, mt_atomic_dec_run);
	/* calculate the expected value */
	vuint64_t expected = init - (N * IT);
	vuint64_t val	   = vatomic64_read(&g_shared);
	ASSERT(expected == val);
	V_UNUSED(expected, val);
}
/*****************************************************************************
 * MultiThreadedTest: vatomic64_inc_rel
 *****************************************************************************/
static inline void *
mt_atomic_inc_rel_run(void *args)
{
	vsize_t tid = (vsize_t)(vuintptr_t)args;
	for (vsize_t i = 0; i < IT; i++) {
		vatomic64_inc_rel(&g_shared);
	}
	V_UNUSED(tid);
	return NULL;
}
static inline void
mt_atomic_inc_rel(void)
{
	vuint64_t init = VUINT32_MAX;
	vatomic64_init(&g_shared, init);
	launch_threads(N, mt_atomic_inc_rel_run);
	/* calculate the expected value */
	vuint64_t expected = init + (N * IT);
	vuint64_t val	   = vatomic64_read(&g_shared);
	ASSERT(expected == val);
	V_UNUSED(expected, val);
}
/*****************************************************************************
 * MultiThreadedTest: vatomic64_dec_rel
 *****************************************************************************/
static inline void *
mt_atomic_dec_rel_run(void *args)
{
	vsize_t tid = (vsize_t)(vuintptr_t)args;
	for (vsize_t i = 0; i < IT; i++) {
		vatomic64_dec_rel(&g_shared);
	}
	V_UNUSED(tid);
	return NULL;
}
static inline void
mt_atomic_dec_rel(void)
{
	vuint64_t init = VUINT32_MAX;
	vatomic64_init(&g_shared, init);
	launch_threads(N, mt_atomic_dec_rel_run);
	/* calculate the expected value */
	vuint64_t expected = init - (N * IT);
	vuint64_t val	   = vatomic64_read(&g_shared);
	ASSERT(expected == val);
	V_UNUSED(expected, val);
}
/*****************************************************************************
 * MultiThreadedTest: vatomic64_inc_rlx
 *****************************************************************************/
static inline void *
mt_atomic_inc_rlx_run(void *args)
{
	vsize_t tid = (vsize_t)(vuintptr_t)args;
	for (vsize_t i = 0; i < IT; i++) {
		vatomic64_inc_rlx(&g_shared);
	}
	V_UNUSED(tid);
	return NULL;
}
static inline void
mt_atomic_inc_rlx(void)
{
	vuint64_t init = VUINT32_MAX;
	vatomic64_init(&g_shared, init);
	launch_threads(N, mt_atomic_inc_rlx_run);
	/* calculate the expected value */
	vuint64_t expected = init + (N * IT);
	vuint64_t val	   = vatomic64_read(&g_shared);
	ASSERT(expected == val);
	V_UNUSED(expected, val);
}
/*****************************************************************************
 * MultiThreadedTest: vatomic64_dec_rlx
 *****************************************************************************/
static inline void *
mt_atomic_dec_rlx_run(void *args)
{
	vsize_t tid = (vsize_t)(vuintptr_t)args;
	for (vsize_t i = 0; i < IT; i++) {
		vatomic64_dec_rlx(&g_shared);
	}
	V_UNUSED(tid);
	return NULL;
}
static inline void
mt_atomic_dec_rlx(void)
{
	vuint64_t init = VUINT32_MAX;
	vatomic64_init(&g_shared, init);
	launch_threads(N, mt_atomic_dec_rlx_run);
	/* calculate the expected value */
	vuint64_t expected = init - (N * IT);
	vuint64_t val	   = vatomic64_read(&g_shared);
	ASSERT(expected == val);
	V_UNUSED(expected, val);
}
/*****************************************************************************
 * MultiThreadedTest: vatomic64_sub
 *****************************************************************************/
static inline void *
mt_atomic_sub_run(void *args)
{
	vsize_t tid = (vsize_t)(vuintptr_t)args;
	for (vsize_t i = 0; i < IT; i++) {
		vatomic64_sub(&g_shared, 0xFFFULL);
	}
	V_UNUSED(tid);
	return NULL;
}
static inline void
mt_atomic_sub(void)
{
	vuint64_t init = VUINT32_MAX;
	vatomic64_init(&g_shared, init);
	launch_threads(N, mt_atomic_sub_run);
	/* calculate the expected value */
	vuint64_t expected = init - (N * IT * 0xFFFULL);
	vuint64_t val	   = vatomic64_read(&g_shared);
	ASSERT(expected == val);
	V_UNUSED(expected, val);
}
/*****************************************************************************
 * MultiThreadedTest: vatomic64_add
 *****************************************************************************/
static inline void *
mt_atomic_add_run(void *args)
{
	vsize_t tid = (vsize_t)(vuintptr_t)args;
	for (vsize_t i = 0; i < IT; i++) {
		vatomic64_add(&g_shared, 0xFFFULL);
	}
	V_UNUSED(tid);
	return NULL;
}
static inline void
mt_atomic_add(void)
{
	vuint64_t init = VUINT32_MAX;
	vatomic64_init(&g_shared, init);
	launch_threads(N, mt_atomic_add_run);
	/* calculate the expected value */
	vuint64_t expected = init + (N * IT * 0xFFFULL);
	vuint64_t val	   = vatomic64_read(&g_shared);
	ASSERT(expected == val);
	V_UNUSED(expected, val);
}
/*****************************************************************************
 * MultiThreadedTest: vatomic64_sub_rel
 *****************************************************************************/
static inline void *
mt_atomic_sub_rel_run(void *args)
{
	vsize_t tid = (vsize_t)(vuintptr_t)args;
	for (vsize_t i = 0; i < IT; i++) {
		vatomic64_sub_rel(&g_shared, 0xFFFULL);
	}
	V_UNUSED(tid);
	return NULL;
}
static inline void
mt_atomic_sub_rel(void)
{
	vuint64_t init = VUINT32_MAX;
	vatomic64_init(&g_shared, init);
	launch_threads(N, mt_atomic_sub_rel_run);
	/* calculate the expected value */
	vuint64_t expected = init - (N * IT * 0xFFFULL);
	vuint64_t val	   = vatomic64_read(&g_shared);
	ASSERT(expected == val);
	V_UNUSED(expected, val);
}
/*****************************************************************************
 * MultiThreadedTest: vatomic64_add_rel
 *****************************************************************************/
static inline void *
mt_atomic_add_rel_run(void *args)
{
	vsize_t tid = (vsize_t)(vuintptr_t)args;
	for (vsize_t i = 0; i < IT; i++) {
		vatomic64_add_rel(&g_shared, 0xFFFULL);
	}
	V_UNUSED(tid);
	return NULL;
}
static inline void
mt_atomic_add_rel(void)
{
	vuint64_t init = VUINT32_MAX;
	vatomic64_init(&g_shared, init);
	launch_threads(N, mt_atomic_add_rel_run);
	/* calculate the expected value */
	vuint64_t expected = init + (N * IT * 0xFFFULL);
	vuint64_t val	   = vatomic64_read(&g_shared);
	ASSERT(expected == val);
	V_UNUSED(expected, val);
}
/*****************************************************************************
 * MultiThreadedTest: vatomic64_sub_rlx
 *****************************************************************************/
static inline void *
mt_atomic_sub_rlx_run(void *args)
{
	vsize_t tid = (vsize_t)(vuintptr_t)args;
	for (vsize_t i = 0; i < IT; i++) {
		vatomic64_sub_rlx(&g_shared, 0xFFFULL);
	}
	V_UNUSED(tid);
	return NULL;
}
static inline void
mt_atomic_sub_rlx(void)
{
	vuint64_t init = VUINT32_MAX;
	vatomic64_init(&g_shared, init);
	launch_threads(N, mt_atomic_sub_rlx_run);
	/* calculate the expected value */
	vuint64_t expected = init - (N * IT * 0xFFFULL);
	vuint64_t val	   = vatomic64_read(&g_shared);
	ASSERT(expected == val);
	V_UNUSED(expected, val);
}
/*****************************************************************************
 * MultiThreadedTest: vatomic64_add_rlx
 *****************************************************************************/
static inline void *
mt_atomic_add_rlx_run(void *args)
{
	vsize_t tid = (vsize_t)(vuintptr_t)args;
	for (vsize_t i = 0; i < IT; i++) {
		vatomic64_add_rlx(&g_shared, 0xFFFULL);
	}
	V_UNUSED(tid);
	return NULL;
}
static inline void
mt_atomic_add_rlx(void)
{
	vuint64_t init = VUINT32_MAX;
	vatomic64_init(&g_shared, init);
	launch_threads(N, mt_atomic_add_rlx_run);
	/* calculate the expected value */
	vuint64_t expected = init + (N * IT * 0xFFFULL);
	vuint64_t val	   = vatomic64_read(&g_shared);
	ASSERT(expected == val);
	V_UNUSED(expected, val);
}
/*****************************************************************************
 * MultiThreadedTest: vatomic64_cmpxchg
 *****************************************************************************/
static inline void *
mt_atomic_cmpxchg_run(void *args)
{
	vsize_t tid	  = (vsize_t)(vuintptr_t)args;
	vuint64_t cur = 0;
	vuint64_t old = 0;
	for (vsize_t i = 0; i < IT; i++) {
		do {
			cur = vatomic64_read(&g_shared);
			old = vatomic64_cmpxchg(&g_shared, cur, cur + 1);
		} while (cur != old);
	}
	V_UNUSED(tid);
	return NULL;
}
static inline void
mt_atomic_cmpxchg(void)
{
	vuint64_t init = VUINT32_MAX;
	vatomic64_init(&g_shared, init);
	launch_threads(N, mt_atomic_cmpxchg_run);
	/* calculate the expected value */
	vuint64_t expected = init + (N * IT);
	vuint64_t val	   = vatomic64_read(&g_shared);
	ASSERT(expected == val);
	V_UNUSED(expected, val);
}
/*****************************************************************************
 * MultiThreadedTest: vatomic64_cmpxchg_rel
 *****************************************************************************/
static inline void *
mt_atomic_cmpxchg_rel_run(void *args)
{
	vsize_t tid	  = (vsize_t)(vuintptr_t)args;
	vuint64_t cur = 0;
	vuint64_t old = 0;
	for (vsize_t i = 0; i < IT; i++) {
		do {
			cur = vatomic64_read(&g_shared);
			old = vatomic64_cmpxchg_rel(&g_shared, cur, cur + 1);
		} while (cur != old);
	}
	V_UNUSED(tid);
	return NULL;
}
static inline void
mt_atomic_cmpxchg_rel(void)
{
	vuint64_t init = VUINT32_MAX;
	vatomic64_init(&g_shared, init);
	launch_threads(N, mt_atomic_cmpxchg_rel_run);
	/* calculate the expected value */
	vuint64_t expected = init + (N * IT);
	vuint64_t val	   = vatomic64_read(&g_shared);
	ASSERT(expected == val);
	V_UNUSED(expected, val);
}
/*****************************************************************************
 * MultiThreadedTest: vatomic64_cmpxchg_acq
 *****************************************************************************/
static inline void *
mt_atomic_cmpxchg_acq_run(void *args)
{
	vsize_t tid	  = (vsize_t)(vuintptr_t)args;
	vuint64_t cur = 0;
	vuint64_t old = 0;
	for (vsize_t i = 0; i < IT; i++) {
		do {
			cur = vatomic64_read(&g_shared);
			old = vatomic64_cmpxchg_acq(&g_shared, cur, cur + 1);
		} while (cur != old);
	}
	V_UNUSED(tid);
	return NULL;
}
static inline void
mt_atomic_cmpxchg_acq(void)
{
	vuint64_t init = VUINT32_MAX;
	vatomic64_init(&g_shared, init);
	launch_threads(N, mt_atomic_cmpxchg_acq_run);
	/* calculate the expected value */
	vuint64_t expected = init + (N * IT);
	vuint64_t val	   = vatomic64_read(&g_shared);
	ASSERT(expected == val);
	V_UNUSED(expected, val);
}
/*****************************************************************************
 * MultiThreadedTest: vatomic64_cmpxchg_rlx
 *****************************************************************************/
static inline void *
mt_atomic_cmpxchg_rlx_run(void *args)
{
	vsize_t tid	  = (vsize_t)(vuintptr_t)args;
	vuint64_t cur = 0;
	vuint64_t old = 0;
	for (vsize_t i = 0; i < IT; i++) {
		do {
			cur = vatomic64_read(&g_shared);
			old = vatomic64_cmpxchg_rlx(&g_shared, cur, cur + 1);
		} while (cur != old);
	}
	V_UNUSED(tid);
	return NULL;
}
static inline void
mt_atomic_cmpxchg_rlx(void)
{
	vuint64_t init = VUINT32_MAX;
	vatomic64_init(&g_shared, init);
	launch_threads(N, mt_atomic_cmpxchg_rlx_run);
	/* calculate the expected value */
	vuint64_t expected = init + (N * IT);
	vuint64_t val	   = vatomic64_read(&g_shared);
	ASSERT(expected == val);
	V_UNUSED(expected, val);
}
/*****************************************************************************
 * MultiThreadedTest: vatomic64_xchg
 *****************************************************************************/
static inline void *
mt_atomic_xchg_run(void *args)
{
	vsize_t tid = (vsize_t)(vuintptr_t)args;
	for (vsize_t i = 0; i < IT; i++) {
		(void)vatomic64_xchg(&g_shared, (vuint64_t)tid);
	}
	V_UNUSED(tid);
	return NULL;
}
static inline void
mt_atomic_xchg(void)
{
	vuint64_t init = VUINT32_MAX;
	vatomic64_init(&g_shared, init);
	launch_threads(N, mt_atomic_xchg_run);
	vuint64_t val = vatomic64_read(&g_shared);
	for (vsize_t i = 0; i < N; i++) {
		if (val == (vuint64_t)i) {
			return;
		}
	}
	ASSERT(0 && "value is none of the expected");
}
/*****************************************************************************
 * MultiThreadedTest: vatomic64_xchg_acq
 *****************************************************************************/
static inline void *
mt_atomic_xchg_acq_run(void *args)
{
	vsize_t tid = (vsize_t)(vuintptr_t)args;
	for (vsize_t i = 0; i < IT; i++) {
		(void)vatomic64_xchg_acq(&g_shared, (vuint64_t)tid);
	}
	V_UNUSED(tid);
	return NULL;
}
static inline void
mt_atomic_xchg_acq(void)
{
	vuint64_t init = VUINT32_MAX;
	vatomic64_init(&g_shared, init);
	launch_threads(N, mt_atomic_xchg_acq_run);
	vuint64_t val = vatomic64_read(&g_shared);
	for (vsize_t i = 0; i < N; i++) {
		if (val == (vuint64_t)i) {
			return;
		}
	}
	ASSERT(0 && "value is none of the expected");
}
/*****************************************************************************
 * MultiThreadedTest: vatomic64_xchg_rel
 *****************************************************************************/
static inline void *
mt_atomic_xchg_rel_run(void *args)
{
	vsize_t tid = (vsize_t)(vuintptr_t)args;
	for (vsize_t i = 0; i < IT; i++) {
		(void)vatomic64_xchg_rel(&g_shared, (vuint64_t)tid);
	}
	V_UNUSED(tid);
	return NULL;
}
static inline void
mt_atomic_xchg_rel(void)
{
	vuint64_t init = VUINT32_MAX;
	vatomic64_init(&g_shared, init);
	launch_threads(N, mt_atomic_xchg_rel_run);
	vuint64_t val = vatomic64_read(&g_shared);
	for (vsize_t i = 0; i < N; i++) {
		if (val == (vuint64_t)i) {
			return;
		}
	}
	ASSERT(0 && "value is none of the expected");
}
/*****************************************************************************
 * MultiThreadedTest: vatomic64_xchg_rlx
 *****************************************************************************/
static inline void *
mt_atomic_xchg_rlx_run(void *args)
{
	vsize_t tid = (vsize_t)(vuintptr_t)args;
	for (vsize_t i = 0; i < IT; i++) {
		(void)vatomic64_xchg_rlx(&g_shared, (vuint64_t)tid);
	}
	V_UNUSED(tid);
	return NULL;
}
static inline void
mt_atomic_xchg_rlx(void)
{
	vuint64_t init = VUINT32_MAX;
	vatomic64_init(&g_shared, init);
	launch_threads(N, mt_atomic_xchg_rlx_run);
	vuint64_t val = vatomic64_read(&g_shared);
	for (vsize_t i = 0; i < N; i++) {
		if (val == (vuint64_t)i) {
			return;
		}
	}
	ASSERT(0 && "value is none of the expected");
}
/*****************************************************************************
 * MultiThreadedTest: vatomic64_max
 *****************************************************************************/
static inline void *
mt_atomic_max_run(void *args)
{
	vsize_t tid = (vsize_t)(vuintptr_t)args;
	for (vsize_t i = 0; i < IT; i++) {
		vatomic64_max(&g_shared, (vuint64_t)tid);
	}
	V_UNUSED(tid);
	return NULL;
}
static inline void
mt_atomic_max(void)
{
	vuint64_t init = 0;
	vatomic64_init(&g_shared, init);
	launch_threads(N, mt_atomic_max_run);
	vuint64_t val = vatomic64_read(&g_shared);
	ASSERT(val == (N - 1));
	V_UNUSED(val);
}
/*****************************************************************************
 * MultiThreadedTest: vatomic64_max_rel
 *****************************************************************************/
static inline void *
mt_atomic_max_rel_run(void *args)
{
	vsize_t tid = (vsize_t)(vuintptr_t)args;
	for (vsize_t i = 0; i < IT; i++) {
		vatomic64_max_rel(&g_shared, (vuint64_t)tid);
	}
	V_UNUSED(tid);
	return NULL;
}
static inline void
mt_atomic_max_rel(void)
{
	vuint64_t init = 0;
	vatomic64_init(&g_shared, init);
	launch_threads(N, mt_atomic_max_rel_run);
	vuint64_t val = vatomic64_read(&g_shared);
	ASSERT(val == (N - 1));
	V_UNUSED(val);
}
/*****************************************************************************
 * MultiThreadedTest: vatomic64_max_rlx
 *****************************************************************************/
static inline void *
mt_atomic_max_rlx_run(void *args)
{
	vsize_t tid = (vsize_t)(vuintptr_t)args;
	for (vsize_t i = 0; i < IT; i++) {
		vatomic64_max_rlx(&g_shared, (vuint64_t)tid);
	}
	V_UNUSED(tid);
	return NULL;
}
static inline void
mt_atomic_max_rlx(void)
{
	vuint64_t init = 0;
	vatomic64_init(&g_shared, init);
	launch_threads(N, mt_atomic_max_rlx_run);
	vuint64_t val = vatomic64_read(&g_shared);
	ASSERT(val == (N - 1));
	V_UNUSED(val);
}
/*****************************************************************************
 * MultiThreadedTest: vatomic64_and
 *****************************************************************************/
static inline void *
mt_atomic_and_run(void *args)
{
	vsize_t tid	   = (vsize_t)(vuintptr_t)args;
	vuint64_t mask = 0xF0F0F0F0F0F0F0F0ULL;

	for (vsize_t i = 0; i < IT; i++) {
		mask = mask << (i * tid);
		vatomic64_and(&g_shared, mask);
	}
	V_UNUSED(tid);
	return NULL;
}
static inline void
mt_atomic_and(void)
{
	vuint64_t init	   = VUINT32_MAX;
	vuint64_t mask	   = 0xF0F0F0F0F0F0F0F0ULL;
	vuint64_t expected = VUINT32_MAX;
	vatomic64_init(&g_shared, init);
	launch_threads(N, mt_atomic_and_run);
	for (vsize_t t = 0; t < N; t++) {
		mask = 0xF0F0F0F0F0F0F0F0ULL;
		for (vsize_t i = 0; i < IT; i++) {
			mask	 = mask << (i * t);
			expected = expected & mask;
		}
	}
	vuint64_t val = vatomic64_read(&g_shared);
	ASSERT(val == expected);
	V_UNUSED(expected, val);
}
/*****************************************************************************
 * MultiThreadedTest: vatomic64_or
 *****************************************************************************/
static inline void *
mt_atomic_or_run(void *args)
{
	vsize_t tid	   = (vsize_t)(vuintptr_t)args;
	vuint64_t mask = 0xF0F0F0F0F0F0F0F0ULL;

	for (vsize_t i = 0; i < IT; i++) {
		mask = mask << (i * tid);
		vatomic64_or(&g_shared, mask);
	}
	V_UNUSED(tid);
	return NULL;
}
static inline void
mt_atomic_or(void)
{
	vuint64_t init	   = VUINT32_MAX;
	vuint64_t mask	   = 0xF0F0F0F0F0F0F0F0ULL;
	vuint64_t expected = VUINT32_MAX;
	vatomic64_init(&g_shared, init);
	launch_threads(N, mt_atomic_or_run);
	for (vsize_t t = 0; t < N; t++) {
		mask = 0xF0F0F0F0F0F0F0F0ULL;
		for (vsize_t i = 0; i < IT; i++) {
			mask	 = mask << (i * t);
			expected = expected | mask;
		}
	}
	vuint64_t val = vatomic64_read(&g_shared);
	ASSERT(val == expected);
	V_UNUSED(expected, val);
}
/*****************************************************************************
 * MultiThreadedTest: vatomic64_xor
 *****************************************************************************/
static inline void *
mt_atomic_xor_run(void *args)
{
	vsize_t tid	   = (vsize_t)(vuintptr_t)args;
	vuint64_t mask = 0xF0F0F0F0F0F0F0F0ULL;

	for (vsize_t i = 0; i < IT; i++) {
		mask = mask << (i * tid);
		vatomic64_xor(&g_shared, mask);
	}
	V_UNUSED(tid);
	return NULL;
}
static inline void
mt_atomic_xor(void)
{
	vuint64_t init	   = VUINT32_MAX;
	vuint64_t mask	   = 0xF0F0F0F0F0F0F0F0ULL;
	vuint64_t expected = VUINT32_MAX;
	vatomic64_init(&g_shared, init);
	launch_threads(N, mt_atomic_xor_run);
	for (vsize_t t = 0; t < N; t++) {
		mask = 0xF0F0F0F0F0F0F0F0ULL;
		for (vsize_t i = 0; i < IT; i++) {
			mask	 = mask << (i * t);
			expected = expected ^ mask;
		}
	}
	vuint64_t val = vatomic64_read(&g_shared);
	ASSERT(val == expected);
	V_UNUSED(expected, val);
}
/*****************************************************************************
 * MultiThreadedTest: vatomic64_and_rel
 *****************************************************************************/
static inline void *
mt_atomic_and_rel_run(void *args)
{
	vsize_t tid	   = (vsize_t)(vuintptr_t)args;
	vuint64_t mask = 0xF0F0F0F0F0F0F0F0ULL;

	for (vsize_t i = 0; i < IT; i++) {
		mask = mask << (i * tid);
		vatomic64_and_rel(&g_shared, mask);
	}
	V_UNUSED(tid);
	return NULL;
}
static inline void
mt_atomic_and_rel(void)
{
	vuint64_t init	   = VUINT32_MAX;
	vuint64_t mask	   = 0xF0F0F0F0F0F0F0F0ULL;
	vuint64_t expected = VUINT32_MAX;
	vatomic64_init(&g_shared, init);
	launch_threads(N, mt_atomic_and_rel_run);
	for (vsize_t t = 0; t < N; t++) {
		mask = 0xF0F0F0F0F0F0F0F0ULL;
		for (vsize_t i = 0; i < IT; i++) {
			mask	 = mask << (i * t);
			expected = expected & mask;
		}
	}
	vuint64_t val = vatomic64_read(&g_shared);
	ASSERT(val == expected);
	V_UNUSED(expected, val);
}
/*****************************************************************************
 * MultiThreadedTest: vatomic64_or_rel
 *****************************************************************************/
static inline void *
mt_atomic_or_rel_run(void *args)
{
	vsize_t tid	   = (vsize_t)(vuintptr_t)args;
	vuint64_t mask = 0xF0F0F0F0F0F0F0F0ULL;

	for (vsize_t i = 0; i < IT; i++) {
		mask = mask << (i * tid);
		vatomic64_or_rel(&g_shared, mask);
	}
	V_UNUSED(tid);
	return NULL;
}
static inline void
mt_atomic_or_rel(void)
{
	vuint64_t init	   = VUINT32_MAX;
	vuint64_t mask	   = 0xF0F0F0F0F0F0F0F0ULL;
	vuint64_t expected = VUINT32_MAX;
	vatomic64_init(&g_shared, init);
	launch_threads(N, mt_atomic_or_rel_run);
	for (vsize_t t = 0; t < N; t++) {
		mask = 0xF0F0F0F0F0F0F0F0ULL;
		for (vsize_t i = 0; i < IT; i++) {
			mask	 = mask << (i * t);
			expected = expected | mask;
		}
	}
	vuint64_t val = vatomic64_read(&g_shared);
	ASSERT(val == expected);
	V_UNUSED(expected, val);
}
/*****************************************************************************
 * MultiThreadedTest: vatomic64_xor_rel
 *****************************************************************************/
static inline void *
mt_atomic_xor_rel_run(void *args)
{
	vsize_t tid	   = (vsize_t)(vuintptr_t)args;
	vuint64_t mask = 0xF0F0F0F0F0F0F0F0ULL;

	for (vsize_t i = 0; i < IT; i++) {
		mask = mask << (i * tid);
		vatomic64_xor_rel(&g_shared, mask);
	}
	V_UNUSED(tid);
	return NULL;
}
static inline void
mt_atomic_xor_rel(void)
{
	vuint64_t init	   = VUINT32_MAX;
	vuint64_t mask	   = 0xF0F0F0F0F0F0F0F0ULL;
	vuint64_t expected = VUINT32_MAX;
	vatomic64_init(&g_shared, init);
	launch_threads(N, mt_atomic_xor_rel_run);
	for (vsize_t t = 0; t < N; t++) {
		mask = 0xF0F0F0F0F0F0F0F0ULL;
		for (vsize_t i = 0; i < IT; i++) {
			mask	 = mask << (i * t);
			expected = expected ^ mask;
		}
	}
	vuint64_t val = vatomic64_read(&g_shared);
	ASSERT(val == expected);
	V_UNUSED(expected, val);
}
/*****************************************************************************
 * MultiThreadedTest: vatomic64_and_rlx
 *****************************************************************************/
static inline void *
mt_atomic_and_rlx_run(void *args)
{
	vsize_t tid	   = (vsize_t)(vuintptr_t)args;
	vuint64_t mask = 0xF0F0F0F0F0F0F0F0ULL;

	for (vsize_t i = 0; i < IT; i++) {
		mask = mask << (i * tid);
		vatomic64_and_rlx(&g_shared, mask);
	}
	V_UNUSED(tid);
	return NULL;
}
static inline void
mt_atomic_and_rlx(void)
{
	vuint64_t init	   = VUINT32_MAX;
	vuint64_t mask	   = 0xF0F0F0F0F0F0F0F0ULL;
	vuint64_t expected = VUINT32_MAX;
	vatomic64_init(&g_shared, init);
	launch_threads(N, mt_atomic_and_rlx_run);
	for (vsize_t t = 0; t < N; t++) {
		mask = 0xF0F0F0F0F0F0F0F0ULL;
		for (vsize_t i = 0; i < IT; i++) {
			mask	 = mask << (i * t);
			expected = expected & mask;
		}
	}
	vuint64_t val = vatomic64_read(&g_shared);
	ASSERT(val == expected);
	V_UNUSED(expected, val);
}
/*****************************************************************************
 * MultiThreadedTest: vatomic64_or_rlx
 *****************************************************************************/
static inline void *
mt_atomic_or_rlx_run(void *args)
{
	vsize_t tid	   = (vsize_t)(vuintptr_t)args;
	vuint64_t mask = 0xF0F0F0F0F0F0F0F0ULL;

	for (vsize_t i = 0; i < IT; i++) {
		mask = mask << (i * tid);
		vatomic64_or_rlx(&g_shared, mask);
	}
	V_UNUSED(tid);
	return NULL;
}
static inline void
mt_atomic_or_rlx(void)
{
	vuint64_t init	   = VUINT32_MAX;
	vuint64_t mask	   = 0xF0F0F0F0F0F0F0F0ULL;
	vuint64_t expected = VUINT32_MAX;
	vatomic64_init(&g_shared, init);
	launch_threads(N, mt_atomic_or_rlx_run);
	for (vsize_t t = 0; t < N; t++) {
		mask = 0xF0F0F0F0F0F0F0F0ULL;
		for (vsize_t i = 0; i < IT; i++) {
			mask	 = mask << (i * t);
			expected = expected | mask;
		}
	}
	vuint64_t val = vatomic64_read(&g_shared);
	ASSERT(val == expected);
	V_UNUSED(expected, val);
}
/*****************************************************************************
 * MultiThreadedTest: vatomic64_xor_rlx
 *****************************************************************************/
static inline void *
mt_atomic_xor_rlx_run(void *args)
{
	vsize_t tid	   = (vsize_t)(vuintptr_t)args;
	vuint64_t mask = 0xF0F0F0F0F0F0F0F0ULL;

	for (vsize_t i = 0; i < IT; i++) {
		mask = mask << (i * tid);
		vatomic64_xor_rlx(&g_shared, mask);
	}
	V_UNUSED(tid);
	return NULL;
}
static inline void
mt_atomic_xor_rlx(void)
{
	vuint64_t init	   = VUINT32_MAX;
	vuint64_t mask	   = 0xF0F0F0F0F0F0F0F0ULL;
	vuint64_t expected = VUINT32_MAX;
	vatomic64_init(&g_shared, init);
	launch_threads(N, mt_atomic_xor_rlx_run);
	for (vsize_t t = 0; t < N; t++) {
		mask = 0xF0F0F0F0F0F0F0F0ULL;
		for (vsize_t i = 0; i < IT; i++) {
			mask	 = mask << (i * t);
			expected = expected ^ mask;
		}
	}
	vuint64_t val = vatomic64_read(&g_shared);
	ASSERT(val == expected);
	V_UNUSED(expected, val);
}
/*****************************************************************************
 * Entry point
 *****************************************************************************/
int
main(void)
{
	mt_atomic_inc();
	mt_atomic_dec();
	mt_atomic_sub();
	mt_atomic_add();
	mt_atomic_max();
	mt_atomic_and();
	mt_atomic_or();
	mt_atomic_xor();
	mt_atomic_inc_rel();
	mt_atomic_dec_rel();
	mt_atomic_sub_rel();
	mt_atomic_add_rel();
	mt_atomic_max_rel();
	mt_atomic_and_rel();
	mt_atomic_or_rel();
	mt_atomic_xor_rel();
	mt_atomic_inc_rlx();
	mt_atomic_dec_rlx();
	mt_atomic_sub_rlx();
	mt_atomic_add_rlx();
	mt_atomic_max_rlx();
	mt_atomic_and_rlx();
	mt_atomic_or_rlx();
	mt_atomic_xor_rlx();
	mt_atomic_cmpxchg();
	mt_atomic_xchg();
	mt_atomic_cmpxchg_rel();
	mt_atomic_xchg_rel();
	mt_atomic_cmpxchg_acq();
	mt_atomic_xchg_acq();
	mt_atomic_cmpxchg_rlx();
	mt_atomic_xchg_rlx();
	return 0;
}
