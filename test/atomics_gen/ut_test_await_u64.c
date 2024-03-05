/*
 * Copyright (C) Huawei Technologies Co., Ltd. 2023-2024. All rights reserved.
 * SPDX-License-Identifier: MIT
 */

/* !!!Warning: File generated by tmpl; DO NOT EDIT.!!! */
#include <vsync/atomic.h>
#include <vsync/common/assert.h>
#include <vsync/common/dbg.h>
#include <test/thread_launcher.h>
#define VUINT64_VAL ((((vuint64_t)0xF) << 32U) | ((vuint64_t)VUINT32_MAX))
/*****************************************************************************
 * UnitTest: vatomic64_await_eq
 *****************************************************************************/
static inline void
ut_atomic_u64_await_eq(void)
{
	vatomic64_t obj = {VUINT64_VAL};
	vuint64_t val	= vatomic64_await_eq(&obj, VUINT64_VAL);
	ASSERT(val == VUINT64_VAL);
	V_UNUSED(val);
}
/*****************************************************************************
 * UnitTest: vatomic64_await_neq
 *****************************************************************************/
static inline void
ut_atomic_u64_await_neq(void)
{
	vatomic64_t obj = {VUINT64_VAL};
	vuint64_t val	= vatomic64_await_neq(&obj, VUINT64_MAX);
	ASSERT(val == VUINT64_VAL);
	V_UNUSED(val);
}
/*****************************************************************************
 * UnitTest: vatomic64_await_eq_acq
 *****************************************************************************/
static inline void
ut_atomic_u64_await_eq_acq(void)
{
	vatomic64_t obj = {VUINT64_VAL};
	vuint64_t val	= vatomic64_await_eq_acq(&obj, VUINT64_VAL);
	ASSERT(val == VUINT64_VAL);
	V_UNUSED(val);
}
/*****************************************************************************
 * UnitTest: vatomic64_await_neq_acq
 *****************************************************************************/
static inline void
ut_atomic_u64_await_neq_acq(void)
{
	vatomic64_t obj = {VUINT64_VAL};
	vuint64_t val	= vatomic64_await_neq_acq(&obj, VUINT64_MAX);
	ASSERT(val == VUINT64_VAL);
	V_UNUSED(val);
}
/*****************************************************************************
 * UnitTest: vatomic64_await_eq_rlx
 *****************************************************************************/
static inline void
ut_atomic_u64_await_eq_rlx(void)
{
	vatomic64_t obj = {VUINT64_VAL};
	vuint64_t val	= vatomic64_await_eq_rlx(&obj, VUINT64_VAL);
	ASSERT(val == VUINT64_VAL);
	V_UNUSED(val);
}
/*****************************************************************************
 * UnitTest: vatomic64_await_neq_rlx
 *****************************************************************************/
static inline void
ut_atomic_u64_await_neq_rlx(void)
{
	vatomic64_t obj = {VUINT64_VAL};
	vuint64_t val	= vatomic64_await_neq_rlx(&obj, VUINT64_MAX);
	ASSERT(val == VUINT64_VAL);
	V_UNUSED(val);
}

/*****************************************************************************
 * UnitTest: vatomic64_await_eq_set
 *****************************************************************************/
static inline void
ut_atomic_u64_await_eq_set(void)
{
	vatomic64_t obj = {VUINT64_VAL};
	vuint64_t n_val = (vuint64_t)0xFF;
	vuint64_t val	= vatomic64_await_eq_set(&obj, VUINT64_VAL, n_val);
	ASSERT(val == VUINT64_VAL);
	val = vatomic64_read(&obj);
	ASSERT(val == n_val);
	V_UNUSED(val);
}
/*****************************************************************************
 * UnitTest: vatomic64_await_neq_set
 *****************************************************************************/
static inline void
ut_atomic_u64_await_neq_set(void)
{
	vatomic64_t obj = {VUINT64_VAL};
	vuint64_t n_val = (vuint64_t)0xFF;
	vuint64_t val	= vatomic64_await_neq_set(&obj, VUINT64_MAX, n_val);
	ASSERT(val == VUINT64_VAL);
	val = vatomic64_read(&obj);
	ASSERT(val == n_val);
	V_UNUSED(val);
}
/*****************************************************************************
 * UnitTest: vatomic64_await_eq_set_rel
 *****************************************************************************/
static inline void
ut_atomic_u64_await_eq_set_rel(void)
{
	vatomic64_t obj = {VUINT64_VAL};
	vuint64_t n_val = (vuint64_t)0xFF;
	vuint64_t val	= vatomic64_await_eq_set_rel(&obj, VUINT64_VAL, n_val);
	ASSERT(val == VUINT64_VAL);
	val = vatomic64_read(&obj);
	ASSERT(val == n_val);
	V_UNUSED(val);
}
/*****************************************************************************
 * UnitTest: vatomic64_await_neq_set_rel
 *****************************************************************************/
static inline void
ut_atomic_u64_await_neq_set_rel(void)
{
	vatomic64_t obj = {VUINT64_VAL};
	vuint64_t n_val = (vuint64_t)0xFF;
	vuint64_t val	= vatomic64_await_neq_set_rel(&obj, VUINT64_MAX, n_val);
	ASSERT(val == VUINT64_VAL);
	val = vatomic64_read(&obj);
	ASSERT(val == n_val);
	V_UNUSED(val);
}
/*****************************************************************************
 * UnitTest: vatomic64_await_eq_set_acq
 *****************************************************************************/
static inline void
ut_atomic_u64_await_eq_set_acq(void)
{
	vatomic64_t obj = {VUINT64_VAL};
	vuint64_t n_val = (vuint64_t)0xFF;
	vuint64_t val	= vatomic64_await_eq_set_acq(&obj, VUINT64_VAL, n_val);
	ASSERT(val == VUINT64_VAL);
	val = vatomic64_read(&obj);
	ASSERT(val == n_val);
	V_UNUSED(val);
}
/*****************************************************************************
 * UnitTest: vatomic64_await_neq_set_acq
 *****************************************************************************/
static inline void
ut_atomic_u64_await_neq_set_acq(void)
{
	vatomic64_t obj = {VUINT64_VAL};
	vuint64_t n_val = (vuint64_t)0xFF;
	vuint64_t val	= vatomic64_await_neq_set_acq(&obj, VUINT64_MAX, n_val);
	ASSERT(val == VUINT64_VAL);
	val = vatomic64_read(&obj);
	ASSERT(val == n_val);
	V_UNUSED(val);
}
/*****************************************************************************
 * UnitTest: vatomic64_await_eq_set_rlx
 *****************************************************************************/
static inline void
ut_atomic_u64_await_eq_set_rlx(void)
{
	vatomic64_t obj = {VUINT64_VAL};
	vuint64_t n_val = (vuint64_t)0xFF;
	vuint64_t val	= vatomic64_await_eq_set_rlx(&obj, VUINT64_VAL, n_val);
	ASSERT(val == VUINT64_VAL);
	val = vatomic64_read(&obj);
	ASSERT(val == n_val);
	V_UNUSED(val);
}
/*****************************************************************************
 * UnitTest: vatomic64_await_neq_set_rlx
 *****************************************************************************/
static inline void
ut_atomic_u64_await_neq_set_rlx(void)
{
	vatomic64_t obj = {VUINT64_VAL};
	vuint64_t n_val = (vuint64_t)0xFF;
	vuint64_t val	= vatomic64_await_neq_set_rlx(&obj, VUINT64_MAX, n_val);
	ASSERT(val == VUINT64_VAL);
	val = vatomic64_read(&obj);
	ASSERT(val == n_val);
	V_UNUSED(val);
}

/*****************************************************************************
 * UnitTest: vatomic64_await_le
 *****************************************************************************/
static inline void
ut_atomic_u64_await_le(void)
{
	vatomic64_t obj = {VUINT64_VAL};
	vuint64_t val	= vatomic64_await_le(&obj, VUINT64_MAX);
	ASSERT(val == VUINT64_VAL);
	V_UNUSED(val);
}
/*****************************************************************************
 * UnitTest: vatomic64_await_gt
 *****************************************************************************/
static inline void
ut_atomic_u64_await_gt(void)
{
	vatomic64_t obj = {VUINT64_MAX};
	vuint64_t val	= vatomic64_await_gt(&obj, VUINT64_VAL);
	ASSERT(val == VUINT64_MAX);
	V_UNUSED(val);
}
/*****************************************************************************
 * UnitTest: vatomic64_await_ge
 *****************************************************************************/
static inline void
ut_atomic_u64_await_ge(void)
{
	vatomic64_t obj = {VUINT64_VAL};
	vuint64_t val	= vatomic64_await_ge(&obj, VUINT64_VAL);
	ASSERT(val == VUINT64_VAL);
	V_UNUSED(val);
}
/*****************************************************************************
 * UnitTest: vatomic64_await_le_acq
 *****************************************************************************/
static inline void
ut_atomic_u64_await_le_acq(void)
{
	vatomic64_t obj = {VUINT64_VAL};
	vuint64_t val	= vatomic64_await_le_acq(&obj, VUINT64_MAX);
	ASSERT(val == VUINT64_VAL);
	V_UNUSED(val);
}
/*****************************************************************************
 * UnitTest: vatomic64_await_gt_acq
 *****************************************************************************/
static inline void
ut_atomic_u64_await_gt_acq(void)
{
	vatomic64_t obj = {VUINT64_MAX};
	vuint64_t val	= vatomic64_await_gt_acq(&obj, VUINT64_VAL);
	ASSERT(val == VUINT64_MAX);
	V_UNUSED(val);
}
/*****************************************************************************
 * UnitTest: vatomic64_await_ge_acq
 *****************************************************************************/
static inline void
ut_atomic_u64_await_ge_acq(void)
{
	vatomic64_t obj = {VUINT64_VAL};
	vuint64_t val	= vatomic64_await_ge_acq(&obj, VUINT64_VAL);
	ASSERT(val == VUINT64_VAL);
	V_UNUSED(val);
}
/*****************************************************************************
 * UnitTest: vatomic64_await_le_rlx
 *****************************************************************************/
static inline void
ut_atomic_u64_await_le_rlx(void)
{
	vatomic64_t obj = {VUINT64_VAL};
	vuint64_t val	= vatomic64_await_le_rlx(&obj, VUINT64_MAX);
	ASSERT(val == VUINT64_VAL);
	V_UNUSED(val);
}
/*****************************************************************************
 * UnitTest: vatomic64_await_gt_rlx
 *****************************************************************************/
static inline void
ut_atomic_u64_await_gt_rlx(void)
{
	vatomic64_t obj = {VUINT64_MAX};
	vuint64_t val	= vatomic64_await_gt_rlx(&obj, VUINT64_VAL);
	ASSERT(val == VUINT64_MAX);
	V_UNUSED(val);
}
/*****************************************************************************
 * UnitTest: vatomic64_await_ge_rlx
 *****************************************************************************/
static inline void
ut_atomic_u64_await_ge_rlx(void)
{
	vatomic64_t obj = {VUINT64_VAL};
	vuint64_t val	= vatomic64_await_ge_rlx(&obj, VUINT64_VAL);
	ASSERT(val == VUINT64_VAL);
	V_UNUSED(val);
}

/*****************************************************************************
 * UnitTest: vatomic64_await_le_set
 *****************************************************************************/
static inline void
ut_atomic_u64_await_le_set(void)
{
	vatomic64_t obj = {VUINT64_VAL};
	vuint64_t n_val = (vuint64_t)0xFF;
	vuint64_t val	= vatomic64_await_le_set(&obj, VUINT64_MAX, n_val);
	ASSERT(val == VUINT64_VAL);
	val = vatomic64_read(&obj);
	ASSERT(val == n_val);
	V_UNUSED(val);
}
/*****************************************************************************
 * UnitTest: vatomic64_await_gt_set
 *****************************************************************************/
static inline void
ut_atomic_u64_await_gt_set(void)
{
	vatomic64_t obj = {VUINT64_MAX};
	vuint64_t n_val = (vuint64_t)0xFF;
	vuint64_t val	= vatomic64_await_gt_set(&obj, VUINT64_VAL, n_val);
	ASSERT(val == VUINT64_MAX);
	val = vatomic64_read(&obj);
	ASSERT(val == n_val);
	V_UNUSED(val);
}
/*****************************************************************************
 * UnitTest: vatomic64_await_ge_set
 *****************************************************************************/
static inline void
ut_atomic_u64_await_ge_set(void)
{
	vatomic64_t obj = {VUINT64_VAL};
	vuint64_t n_val = (vuint64_t)0xFF;
	vuint64_t val	= vatomic64_await_ge_set(&obj, VUINT64_VAL, n_val);
	ASSERT(val == VUINT64_VAL);
	val = vatomic64_read(&obj);
	ASSERT(val == n_val);
	V_UNUSED(val);
}
/*****************************************************************************
 * UnitTest: vatomic64_await_le_set_rel
 *****************************************************************************/
static inline void
ut_atomic_u64_await_le_set_rel(void)
{
	vatomic64_t obj = {VUINT64_VAL};
	vuint64_t n_val = (vuint64_t)0xFF;
	vuint64_t val	= vatomic64_await_le_set_rel(&obj, VUINT64_MAX, n_val);
	ASSERT(val == VUINT64_VAL);
	val = vatomic64_read(&obj);
	ASSERT(val == n_val);
	V_UNUSED(val);
}
/*****************************************************************************
 * UnitTest: vatomic64_await_gt_set_rel
 *****************************************************************************/
static inline void
ut_atomic_u64_await_gt_set_rel(void)
{
	vatomic64_t obj = {VUINT64_MAX};
	vuint64_t n_val = (vuint64_t)0xFF;
	vuint64_t val	= vatomic64_await_gt_set_rel(&obj, VUINT64_VAL, n_val);
	ASSERT(val == VUINT64_MAX);
	val = vatomic64_read(&obj);
	ASSERT(val == n_val);
	V_UNUSED(val);
}
/*****************************************************************************
 * UnitTest: vatomic64_await_ge_set_rel
 *****************************************************************************/
static inline void
ut_atomic_u64_await_ge_set_rel(void)
{
	vatomic64_t obj = {VUINT64_VAL};
	vuint64_t n_val = (vuint64_t)0xFF;
	vuint64_t val	= vatomic64_await_ge_set_rel(&obj, VUINT64_VAL, n_val);
	ASSERT(val == VUINT64_VAL);
	val = vatomic64_read(&obj);
	ASSERT(val == n_val);
	V_UNUSED(val);
}
/*****************************************************************************
 * UnitTest: vatomic64_await_le_set_acq
 *****************************************************************************/
static inline void
ut_atomic_u64_await_le_set_acq(void)
{
	vatomic64_t obj = {VUINT64_VAL};
	vuint64_t n_val = (vuint64_t)0xFF;
	vuint64_t val	= vatomic64_await_le_set_acq(&obj, VUINT64_MAX, n_val);
	ASSERT(val == VUINT64_VAL);
	val = vatomic64_read(&obj);
	ASSERT(val == n_val);
	V_UNUSED(val);
}
/*****************************************************************************
 * UnitTest: vatomic64_await_gt_set_acq
 *****************************************************************************/
static inline void
ut_atomic_u64_await_gt_set_acq(void)
{
	vatomic64_t obj = {VUINT64_MAX};
	vuint64_t n_val = (vuint64_t)0xFF;
	vuint64_t val	= vatomic64_await_gt_set_acq(&obj, VUINT64_VAL, n_val);
	ASSERT(val == VUINT64_MAX);
	val = vatomic64_read(&obj);
	ASSERT(val == n_val);
	V_UNUSED(val);
}
/*****************************************************************************
 * UnitTest: vatomic64_await_ge_set_acq
 *****************************************************************************/
static inline void
ut_atomic_u64_await_ge_set_acq(void)
{
	vatomic64_t obj = {VUINT64_VAL};
	vuint64_t n_val = (vuint64_t)0xFF;
	vuint64_t val	= vatomic64_await_ge_set_acq(&obj, VUINT64_VAL, n_val);
	ASSERT(val == VUINT64_VAL);
	val = vatomic64_read(&obj);
	ASSERT(val == n_val);
	V_UNUSED(val);
}
/*****************************************************************************
 * UnitTest: vatomic64_await_le_set_rlx
 *****************************************************************************/
static inline void
ut_atomic_u64_await_le_set_rlx(void)
{
	vatomic64_t obj = {VUINT64_VAL};
	vuint64_t n_val = (vuint64_t)0xFF;
	vuint64_t val	= vatomic64_await_le_set_rlx(&obj, VUINT64_MAX, n_val);
	ASSERT(val == VUINT64_VAL);
	val = vatomic64_read(&obj);
	ASSERT(val == n_val);
	V_UNUSED(val);
}
/*****************************************************************************
 * UnitTest: vatomic64_await_gt_set_rlx
 *****************************************************************************/
static inline void
ut_atomic_u64_await_gt_set_rlx(void)
{
	vatomic64_t obj = {VUINT64_MAX};
	vuint64_t n_val = (vuint64_t)0xFF;
	vuint64_t val	= vatomic64_await_gt_set_rlx(&obj, VUINT64_VAL, n_val);
	ASSERT(val == VUINT64_MAX);
	val = vatomic64_read(&obj);
	ASSERT(val == n_val);
	V_UNUSED(val);
}
/*****************************************************************************
 * UnitTest: vatomic64_await_ge_set_rlx
 *****************************************************************************/
static inline void
ut_atomic_u64_await_ge_set_rlx(void)
{
	vatomic64_t obj = {VUINT64_VAL};
	vuint64_t n_val = (vuint64_t)0xFF;
	vuint64_t val	= vatomic64_await_ge_set_rlx(&obj, VUINT64_VAL, n_val);
	ASSERT(val == VUINT64_VAL);
	val = vatomic64_read(&obj);
	ASSERT(val == n_val);
	V_UNUSED(val);
}

/*****************************************************************************
 * UnitTest: vatomic64_await_neq_add
 *****************************************************************************/
static inline void
ut_atomic_u64_await_neq_add(void)
{
	vatomic64_t obj = {VUINT64_VAL};
	vuint64_t ref	= VUINT64_VAL;
	vuint64_t val	= vatomic64_await_neq_add(&obj, VUINT64_MAX, 0x1U);
	ASSERT(val == VUINT64_VAL);
	ref = ref + 0x1U;
	val = vatomic64_read(&obj);
	ASSERT(val == ref);
	V_UNUSED(val, ref);
}
/*****************************************************************************
 * UnitTest: vatomic64_await_neq_sub
 *****************************************************************************/
static inline void
ut_atomic_u64_await_neq_sub(void)
{
	vatomic64_t obj = {VUINT64_VAL};
	vuint64_t ref	= VUINT64_VAL;
	vuint64_t val	= vatomic64_await_neq_sub(&obj, VUINT64_MAX, 0x1U);
	ASSERT(val == VUINT64_VAL);
	ref = ref - 0x1U;
	val = vatomic64_read(&obj);
	ASSERT(val == ref);
	V_UNUSED(val, ref);
}
/*****************************************************************************
 * UnitTest: vatomic64_await_eq_add
 *****************************************************************************/
static inline void
ut_atomic_u64_await_eq_add(void)
{
	vatomic64_t obj = {VUINT64_VAL};
	vuint64_t ref	= VUINT64_VAL;
	vuint64_t val	= vatomic64_await_eq_add(&obj, VUINT64_VAL, 0x1U);
	ASSERT(val == VUINT64_VAL);
	ref = ref + 0x1U;
	val = vatomic64_read(&obj);
	ASSERT(val == ref);
	V_UNUSED(val, ref);
}
/*****************************************************************************
 * UnitTest: vatomic64_await_eq_sub
 *****************************************************************************/
static inline void
ut_atomic_u64_await_eq_sub(void)
{
	vatomic64_t obj = {VUINT64_VAL};
	vuint64_t ref	= VUINT64_VAL;
	vuint64_t val	= vatomic64_await_eq_sub(&obj, VUINT64_VAL, 0x1U);
	ASSERT(val == VUINT64_VAL);
	ref = ref - 0x1U;
	val = vatomic64_read(&obj);
	ASSERT(val == ref);
	V_UNUSED(val, ref);
}
/*****************************************************************************
 * UnitTest: vatomic64_await_le_add
 *****************************************************************************/
static inline void
ut_atomic_u64_await_le_add(void)
{
	vatomic64_t obj = {VUINT64_VAL};
	vuint64_t ref	= VUINT64_VAL;
	vuint64_t val	= vatomic64_await_le_add(&obj, VUINT64_MAX, 0x1U);
	ASSERT(val == VUINT64_VAL);
	ref = ref + 0x1U;
	val = vatomic64_read(&obj);
	ASSERT(val == ref);
	V_UNUSED(val, ref);
}
/*****************************************************************************
 * UnitTest: vatomic64_await_le_sub
 *****************************************************************************/
static inline void
ut_atomic_u64_await_le_sub(void)
{
	vatomic64_t obj = {VUINT64_VAL};
	vuint64_t ref	= VUINT64_VAL;
	vuint64_t val	= vatomic64_await_le_sub(&obj, VUINT64_MAX, 0x1U);
	ASSERT(val == VUINT64_VAL);
	ref = ref - 0x1U;
	val = vatomic64_read(&obj);
	ASSERT(val == ref);
	V_UNUSED(val, ref);
}
/*****************************************************************************
 * UnitTest: vatomic64_await_gt_add
 *****************************************************************************/
static inline void
ut_atomic_u64_await_gt_add(void)
{
	vatomic64_t obj = {VUINT64_MAX};
	vuint64_t ref	= VUINT64_MAX;
	vuint64_t val	= vatomic64_await_gt_add(&obj, VUINT64_VAL, 0x1U);
	ASSERT(val == VUINT64_MAX);
	ref = ref + 0x1U;
	val = vatomic64_read(&obj);
	ASSERT(val == ref);
	V_UNUSED(val, ref);
}
/*****************************************************************************
 * UnitTest: vatomic64_await_gt_sub
 *****************************************************************************/
static inline void
ut_atomic_u64_await_gt_sub(void)
{
	vatomic64_t obj = {VUINT64_MAX};
	vuint64_t ref	= VUINT64_MAX;
	vuint64_t val	= vatomic64_await_gt_sub(&obj, VUINT64_VAL, 0x1U);
	ASSERT(val == VUINT64_MAX);
	ref = ref - 0x1U;
	val = vatomic64_read(&obj);
	ASSERT(val == ref);
	V_UNUSED(val, ref);
}
/*****************************************************************************
 * UnitTest: vatomic64_await_ge_add
 *****************************************************************************/
static inline void
ut_atomic_u64_await_ge_add(void)
{
	vatomic64_t obj = {VUINT64_VAL};
	vuint64_t ref	= VUINT64_VAL;
	vuint64_t val	= vatomic64_await_ge_add(&obj, VUINT64_VAL, 0x1U);
	ASSERT(val == VUINT64_VAL);
	ref = ref + 0x1U;
	val = vatomic64_read(&obj);
	ASSERT(val == ref);
	V_UNUSED(val, ref);
}
/*****************************************************************************
 * UnitTest: vatomic64_await_ge_sub
 *****************************************************************************/
static inline void
ut_atomic_u64_await_ge_sub(void)
{
	vatomic64_t obj = {VUINT64_VAL};
	vuint64_t ref	= VUINT64_VAL;
	vuint64_t val	= vatomic64_await_ge_sub(&obj, VUINT64_VAL, 0x1U);
	ASSERT(val == VUINT64_VAL);
	ref = ref - 0x1U;
	val = vatomic64_read(&obj);
	ASSERT(val == ref);
	V_UNUSED(val, ref);
}
/*****************************************************************************
 * UnitTest: vatomic64_await_neq_add_rel
 *****************************************************************************/
static inline void
ut_atomic_u64_await_neq_add_rel(void)
{
	vatomic64_t obj = {VUINT64_VAL};
	vuint64_t ref	= VUINT64_VAL;
	vuint64_t val	= vatomic64_await_neq_add_rel(&obj, VUINT64_MAX, 0x1U);
	ASSERT(val == VUINT64_VAL);
	ref = ref + 0x1U;
	val = vatomic64_read(&obj);
	ASSERT(val == ref);
	V_UNUSED(val, ref);
}
/*****************************************************************************
 * UnitTest: vatomic64_await_neq_sub_rel
 *****************************************************************************/
static inline void
ut_atomic_u64_await_neq_sub_rel(void)
{
	vatomic64_t obj = {VUINT64_VAL};
	vuint64_t ref	= VUINT64_VAL;
	vuint64_t val	= vatomic64_await_neq_sub_rel(&obj, VUINT64_MAX, 0x1U);
	ASSERT(val == VUINT64_VAL);
	ref = ref - 0x1U;
	val = vatomic64_read(&obj);
	ASSERT(val == ref);
	V_UNUSED(val, ref);
}
/*****************************************************************************
 * UnitTest: vatomic64_await_eq_add_rel
 *****************************************************************************/
static inline void
ut_atomic_u64_await_eq_add_rel(void)
{
	vatomic64_t obj = {VUINT64_VAL};
	vuint64_t ref	= VUINT64_VAL;
	vuint64_t val	= vatomic64_await_eq_add_rel(&obj, VUINT64_VAL, 0x1U);
	ASSERT(val == VUINT64_VAL);
	ref = ref + 0x1U;
	val = vatomic64_read(&obj);
	ASSERT(val == ref);
	V_UNUSED(val, ref);
}
/*****************************************************************************
 * UnitTest: vatomic64_await_eq_sub_rel
 *****************************************************************************/
static inline void
ut_atomic_u64_await_eq_sub_rel(void)
{
	vatomic64_t obj = {VUINT64_VAL};
	vuint64_t ref	= VUINT64_VAL;
	vuint64_t val	= vatomic64_await_eq_sub_rel(&obj, VUINT64_VAL, 0x1U);
	ASSERT(val == VUINT64_VAL);
	ref = ref - 0x1U;
	val = vatomic64_read(&obj);
	ASSERT(val == ref);
	V_UNUSED(val, ref);
}
/*****************************************************************************
 * UnitTest: vatomic64_await_le_add_rel
 *****************************************************************************/
static inline void
ut_atomic_u64_await_le_add_rel(void)
{
	vatomic64_t obj = {VUINT64_VAL};
	vuint64_t ref	= VUINT64_VAL;
	vuint64_t val	= vatomic64_await_le_add_rel(&obj, VUINT64_MAX, 0x1U);
	ASSERT(val == VUINT64_VAL);
	ref = ref + 0x1U;
	val = vatomic64_read(&obj);
	ASSERT(val == ref);
	V_UNUSED(val, ref);
}
/*****************************************************************************
 * UnitTest: vatomic64_await_le_sub_rel
 *****************************************************************************/
static inline void
ut_atomic_u64_await_le_sub_rel(void)
{
	vatomic64_t obj = {VUINT64_VAL};
	vuint64_t ref	= VUINT64_VAL;
	vuint64_t val	= vatomic64_await_le_sub_rel(&obj, VUINT64_MAX, 0x1U);
	ASSERT(val == VUINT64_VAL);
	ref = ref - 0x1U;
	val = vatomic64_read(&obj);
	ASSERT(val == ref);
	V_UNUSED(val, ref);
}
/*****************************************************************************
 * UnitTest: vatomic64_await_gt_add_rel
 *****************************************************************************/
static inline void
ut_atomic_u64_await_gt_add_rel(void)
{
	vatomic64_t obj = {VUINT64_MAX};
	vuint64_t ref	= VUINT64_MAX;
	vuint64_t val	= vatomic64_await_gt_add_rel(&obj, VUINT64_VAL, 0x1U);
	ASSERT(val == VUINT64_MAX);
	ref = ref + 0x1U;
	val = vatomic64_read(&obj);
	ASSERT(val == ref);
	V_UNUSED(val, ref);
}
/*****************************************************************************
 * UnitTest: vatomic64_await_gt_sub_rel
 *****************************************************************************/
static inline void
ut_atomic_u64_await_gt_sub_rel(void)
{
	vatomic64_t obj = {VUINT64_MAX};
	vuint64_t ref	= VUINT64_MAX;
	vuint64_t val	= vatomic64_await_gt_sub_rel(&obj, VUINT64_VAL, 0x1U);
	ASSERT(val == VUINT64_MAX);
	ref = ref - 0x1U;
	val = vatomic64_read(&obj);
	ASSERT(val == ref);
	V_UNUSED(val, ref);
}
/*****************************************************************************
 * UnitTest: vatomic64_await_ge_add_rel
 *****************************************************************************/
static inline void
ut_atomic_u64_await_ge_add_rel(void)
{
	vatomic64_t obj = {VUINT64_VAL};
	vuint64_t ref	= VUINT64_VAL;
	vuint64_t val	= vatomic64_await_ge_add_rel(&obj, VUINT64_VAL, 0x1U);
	ASSERT(val == VUINT64_VAL);
	ref = ref + 0x1U;
	val = vatomic64_read(&obj);
	ASSERT(val == ref);
	V_UNUSED(val, ref);
}
/*****************************************************************************
 * UnitTest: vatomic64_await_ge_sub_rel
 *****************************************************************************/
static inline void
ut_atomic_u64_await_ge_sub_rel(void)
{
	vatomic64_t obj = {VUINT64_VAL};
	vuint64_t ref	= VUINT64_VAL;
	vuint64_t val	= vatomic64_await_ge_sub_rel(&obj, VUINT64_VAL, 0x1U);
	ASSERT(val == VUINT64_VAL);
	ref = ref - 0x1U;
	val = vatomic64_read(&obj);
	ASSERT(val == ref);
	V_UNUSED(val, ref);
}
/*****************************************************************************
 * UnitTest: vatomic64_await_neq_add_acq
 *****************************************************************************/
static inline void
ut_atomic_u64_await_neq_add_acq(void)
{
	vatomic64_t obj = {VUINT64_VAL};
	vuint64_t ref	= VUINT64_VAL;
	vuint64_t val	= vatomic64_await_neq_add_acq(&obj, VUINT64_MAX, 0x1U);
	ASSERT(val == VUINT64_VAL);
	ref = ref + 0x1U;
	val = vatomic64_read(&obj);
	ASSERT(val == ref);
	V_UNUSED(val, ref);
}
/*****************************************************************************
 * UnitTest: vatomic64_await_neq_sub_acq
 *****************************************************************************/
static inline void
ut_atomic_u64_await_neq_sub_acq(void)
{
	vatomic64_t obj = {VUINT64_VAL};
	vuint64_t ref	= VUINT64_VAL;
	vuint64_t val	= vatomic64_await_neq_sub_acq(&obj, VUINT64_MAX, 0x1U);
	ASSERT(val == VUINT64_VAL);
	ref = ref - 0x1U;
	val = vatomic64_read(&obj);
	ASSERT(val == ref);
	V_UNUSED(val, ref);
}
/*****************************************************************************
 * UnitTest: vatomic64_await_eq_add_acq
 *****************************************************************************/
static inline void
ut_atomic_u64_await_eq_add_acq(void)
{
	vatomic64_t obj = {VUINT64_VAL};
	vuint64_t ref	= VUINT64_VAL;
	vuint64_t val	= vatomic64_await_eq_add_acq(&obj, VUINT64_VAL, 0x1U);
	ASSERT(val == VUINT64_VAL);
	ref = ref + 0x1U;
	val = vatomic64_read(&obj);
	ASSERT(val == ref);
	V_UNUSED(val, ref);
}
/*****************************************************************************
 * UnitTest: vatomic64_await_eq_sub_acq
 *****************************************************************************/
static inline void
ut_atomic_u64_await_eq_sub_acq(void)
{
	vatomic64_t obj = {VUINT64_VAL};
	vuint64_t ref	= VUINT64_VAL;
	vuint64_t val	= vatomic64_await_eq_sub_acq(&obj, VUINT64_VAL, 0x1U);
	ASSERT(val == VUINT64_VAL);
	ref = ref - 0x1U;
	val = vatomic64_read(&obj);
	ASSERT(val == ref);
	V_UNUSED(val, ref);
}
/*****************************************************************************
 * UnitTest: vatomic64_await_le_add_acq
 *****************************************************************************/
static inline void
ut_atomic_u64_await_le_add_acq(void)
{
	vatomic64_t obj = {VUINT64_VAL};
	vuint64_t ref	= VUINT64_VAL;
	vuint64_t val	= vatomic64_await_le_add_acq(&obj, VUINT64_MAX, 0x1U);
	ASSERT(val == VUINT64_VAL);
	ref = ref + 0x1U;
	val = vatomic64_read(&obj);
	ASSERT(val == ref);
	V_UNUSED(val, ref);
}
/*****************************************************************************
 * UnitTest: vatomic64_await_le_sub_acq
 *****************************************************************************/
static inline void
ut_atomic_u64_await_le_sub_acq(void)
{
	vatomic64_t obj = {VUINT64_VAL};
	vuint64_t ref	= VUINT64_VAL;
	vuint64_t val	= vatomic64_await_le_sub_acq(&obj, VUINT64_MAX, 0x1U);
	ASSERT(val == VUINT64_VAL);
	ref = ref - 0x1U;
	val = vatomic64_read(&obj);
	ASSERT(val == ref);
	V_UNUSED(val, ref);
}
/*****************************************************************************
 * UnitTest: vatomic64_await_gt_add_acq
 *****************************************************************************/
static inline void
ut_atomic_u64_await_gt_add_acq(void)
{
	vatomic64_t obj = {VUINT64_MAX};
	vuint64_t ref	= VUINT64_MAX;
	vuint64_t val	= vatomic64_await_gt_add_acq(&obj, VUINT64_VAL, 0x1U);
	ASSERT(val == VUINT64_MAX);
	ref = ref + 0x1U;
	val = vatomic64_read(&obj);
	ASSERT(val == ref);
	V_UNUSED(val, ref);
}
/*****************************************************************************
 * UnitTest: vatomic64_await_gt_sub_acq
 *****************************************************************************/
static inline void
ut_atomic_u64_await_gt_sub_acq(void)
{
	vatomic64_t obj = {VUINT64_MAX};
	vuint64_t ref	= VUINT64_MAX;
	vuint64_t val	= vatomic64_await_gt_sub_acq(&obj, VUINT64_VAL, 0x1U);
	ASSERT(val == VUINT64_MAX);
	ref = ref - 0x1U;
	val = vatomic64_read(&obj);
	ASSERT(val == ref);
	V_UNUSED(val, ref);
}
/*****************************************************************************
 * UnitTest: vatomic64_await_ge_add_acq
 *****************************************************************************/
static inline void
ut_atomic_u64_await_ge_add_acq(void)
{
	vatomic64_t obj = {VUINT64_VAL};
	vuint64_t ref	= VUINT64_VAL;
	vuint64_t val	= vatomic64_await_ge_add_acq(&obj, VUINT64_VAL, 0x1U);
	ASSERT(val == VUINT64_VAL);
	ref = ref + 0x1U;
	val = vatomic64_read(&obj);
	ASSERT(val == ref);
	V_UNUSED(val, ref);
}
/*****************************************************************************
 * UnitTest: vatomic64_await_ge_sub_acq
 *****************************************************************************/
static inline void
ut_atomic_u64_await_ge_sub_acq(void)
{
	vatomic64_t obj = {VUINT64_VAL};
	vuint64_t ref	= VUINT64_VAL;
	vuint64_t val	= vatomic64_await_ge_sub_acq(&obj, VUINT64_VAL, 0x1U);
	ASSERT(val == VUINT64_VAL);
	ref = ref - 0x1U;
	val = vatomic64_read(&obj);
	ASSERT(val == ref);
	V_UNUSED(val, ref);
}
/*****************************************************************************
 * UnitTest: vatomic64_await_neq_add_rlx
 *****************************************************************************/
static inline void
ut_atomic_u64_await_neq_add_rlx(void)
{
	vatomic64_t obj = {VUINT64_VAL};
	vuint64_t ref	= VUINT64_VAL;
	vuint64_t val	= vatomic64_await_neq_add_rlx(&obj, VUINT64_MAX, 0x1U);
	ASSERT(val == VUINT64_VAL);
	ref = ref + 0x1U;
	val = vatomic64_read(&obj);
	ASSERT(val == ref);
	V_UNUSED(val, ref);
}
/*****************************************************************************
 * UnitTest: vatomic64_await_neq_sub_rlx
 *****************************************************************************/
static inline void
ut_atomic_u64_await_neq_sub_rlx(void)
{
	vatomic64_t obj = {VUINT64_VAL};
	vuint64_t ref	= VUINT64_VAL;
	vuint64_t val	= vatomic64_await_neq_sub_rlx(&obj, VUINT64_MAX, 0x1U);
	ASSERT(val == VUINT64_VAL);
	ref = ref - 0x1U;
	val = vatomic64_read(&obj);
	ASSERT(val == ref);
	V_UNUSED(val, ref);
}
/*****************************************************************************
 * UnitTest: vatomic64_await_eq_add_rlx
 *****************************************************************************/
static inline void
ut_atomic_u64_await_eq_add_rlx(void)
{
	vatomic64_t obj = {VUINT64_VAL};
	vuint64_t ref	= VUINT64_VAL;
	vuint64_t val	= vatomic64_await_eq_add_rlx(&obj, VUINT64_VAL, 0x1U);
	ASSERT(val == VUINT64_VAL);
	ref = ref + 0x1U;
	val = vatomic64_read(&obj);
	ASSERT(val == ref);
	V_UNUSED(val, ref);
}
/*****************************************************************************
 * UnitTest: vatomic64_await_eq_sub_rlx
 *****************************************************************************/
static inline void
ut_atomic_u64_await_eq_sub_rlx(void)
{
	vatomic64_t obj = {VUINT64_VAL};
	vuint64_t ref	= VUINT64_VAL;
	vuint64_t val	= vatomic64_await_eq_sub_rlx(&obj, VUINT64_VAL, 0x1U);
	ASSERT(val == VUINT64_VAL);
	ref = ref - 0x1U;
	val = vatomic64_read(&obj);
	ASSERT(val == ref);
	V_UNUSED(val, ref);
}
/*****************************************************************************
 * UnitTest: vatomic64_await_le_add_rlx
 *****************************************************************************/
static inline void
ut_atomic_u64_await_le_add_rlx(void)
{
	vatomic64_t obj = {VUINT64_VAL};
	vuint64_t ref	= VUINT64_VAL;
	vuint64_t val	= vatomic64_await_le_add_rlx(&obj, VUINT64_MAX, 0x1U);
	ASSERT(val == VUINT64_VAL);
	ref = ref + 0x1U;
	val = vatomic64_read(&obj);
	ASSERT(val == ref);
	V_UNUSED(val, ref);
}
/*****************************************************************************
 * UnitTest: vatomic64_await_le_sub_rlx
 *****************************************************************************/
static inline void
ut_atomic_u64_await_le_sub_rlx(void)
{
	vatomic64_t obj = {VUINT64_VAL};
	vuint64_t ref	= VUINT64_VAL;
	vuint64_t val	= vatomic64_await_le_sub_rlx(&obj, VUINT64_MAX, 0x1U);
	ASSERT(val == VUINT64_VAL);
	ref = ref - 0x1U;
	val = vatomic64_read(&obj);
	ASSERT(val == ref);
	V_UNUSED(val, ref);
}
/*****************************************************************************
 * UnitTest: vatomic64_await_gt_add_rlx
 *****************************************************************************/
static inline void
ut_atomic_u64_await_gt_add_rlx(void)
{
	vatomic64_t obj = {VUINT64_MAX};
	vuint64_t ref	= VUINT64_MAX;
	vuint64_t val	= vatomic64_await_gt_add_rlx(&obj, VUINT64_VAL, 0x1U);
	ASSERT(val == VUINT64_MAX);
	ref = ref + 0x1U;
	val = vatomic64_read(&obj);
	ASSERT(val == ref);
	V_UNUSED(val, ref);
}
/*****************************************************************************
 * UnitTest: vatomic64_await_gt_sub_rlx
 *****************************************************************************/
static inline void
ut_atomic_u64_await_gt_sub_rlx(void)
{
	vatomic64_t obj = {VUINT64_MAX};
	vuint64_t ref	= VUINT64_MAX;
	vuint64_t val	= vatomic64_await_gt_sub_rlx(&obj, VUINT64_VAL, 0x1U);
	ASSERT(val == VUINT64_MAX);
	ref = ref - 0x1U;
	val = vatomic64_read(&obj);
	ASSERT(val == ref);
	V_UNUSED(val, ref);
}
/*****************************************************************************
 * UnitTest: vatomic64_await_ge_add_rlx
 *****************************************************************************/
static inline void
ut_atomic_u64_await_ge_add_rlx(void)
{
	vatomic64_t obj = {VUINT64_VAL};
	vuint64_t ref	= VUINT64_VAL;
	vuint64_t val	= vatomic64_await_ge_add_rlx(&obj, VUINT64_VAL, 0x1U);
	ASSERT(val == VUINT64_VAL);
	ref = ref + 0x1U;
	val = vatomic64_read(&obj);
	ASSERT(val == ref);
	V_UNUSED(val, ref);
}
/*****************************************************************************
 * UnitTest: vatomic64_await_ge_sub_rlx
 *****************************************************************************/
static inline void
ut_atomic_u64_await_ge_sub_rlx(void)
{
	vatomic64_t obj = {VUINT64_VAL};
	vuint64_t ref	= VUINT64_VAL;
	vuint64_t val	= vatomic64_await_ge_sub_rlx(&obj, VUINT64_VAL, 0x1U);
	ASSERT(val == VUINT64_VAL);
	ref = ref - 0x1U;
	val = vatomic64_read(&obj);
	ASSERT(val == ref);
	V_UNUSED(val, ref);
}
/*****************************************************************************
 * Entry point
 *****************************************************************************/
int
main(void)
{
	ut_atomic_u64_await_eq();
	ut_atomic_u64_await_neq();
	ut_atomic_u64_await_eq_acq();
	ut_atomic_u64_await_neq_acq();
	ut_atomic_u64_await_eq_rlx();
	ut_atomic_u64_await_neq_rlx();

	ut_atomic_u64_await_eq_set();
	ut_atomic_u64_await_neq_set();
	ut_atomic_u64_await_eq_set_rel();
	ut_atomic_u64_await_neq_set_rel();
	ut_atomic_u64_await_eq_set_acq();
	ut_atomic_u64_await_neq_set_acq();
	ut_atomic_u64_await_eq_set_rlx();
	ut_atomic_u64_await_neq_set_rlx();

	ut_atomic_u64_await_le();
	ut_atomic_u64_await_gt();
	ut_atomic_u64_await_ge();
	ut_atomic_u64_await_le_acq();
	ut_atomic_u64_await_gt_acq();
	ut_atomic_u64_await_ge_acq();
	ut_atomic_u64_await_le_rlx();
	ut_atomic_u64_await_gt_rlx();
	ut_atomic_u64_await_ge_rlx();

	ut_atomic_u64_await_le_set();
	ut_atomic_u64_await_gt_set();
	ut_atomic_u64_await_ge_set();
	ut_atomic_u64_await_le_set_rel();
	ut_atomic_u64_await_gt_set_rel();
	ut_atomic_u64_await_ge_set_rel();
	ut_atomic_u64_await_le_set_acq();
	ut_atomic_u64_await_gt_set_acq();
	ut_atomic_u64_await_ge_set_acq();
	ut_atomic_u64_await_le_set_rlx();
	ut_atomic_u64_await_gt_set_rlx();
	ut_atomic_u64_await_ge_set_rlx();

	ut_atomic_u64_await_neq_add();
	ut_atomic_u64_await_neq_sub();
	ut_atomic_u64_await_eq_add();
	ut_atomic_u64_await_eq_sub();
	ut_atomic_u64_await_le_add();
	ut_atomic_u64_await_le_sub();
	ut_atomic_u64_await_gt_add();
	ut_atomic_u64_await_gt_sub();
	ut_atomic_u64_await_ge_add();
	ut_atomic_u64_await_ge_sub();
	ut_atomic_u64_await_neq_add_rel();
	ut_atomic_u64_await_neq_sub_rel();
	ut_atomic_u64_await_eq_add_rel();
	ut_atomic_u64_await_eq_sub_rel();
	ut_atomic_u64_await_le_add_rel();
	ut_atomic_u64_await_le_sub_rel();
	ut_atomic_u64_await_gt_add_rel();
	ut_atomic_u64_await_gt_sub_rel();
	ut_atomic_u64_await_ge_add_rel();
	ut_atomic_u64_await_ge_sub_rel();
	ut_atomic_u64_await_neq_add_acq();
	ut_atomic_u64_await_neq_sub_acq();
	ut_atomic_u64_await_eq_add_acq();
	ut_atomic_u64_await_eq_sub_acq();
	ut_atomic_u64_await_le_add_acq();
	ut_atomic_u64_await_le_sub_acq();
	ut_atomic_u64_await_gt_add_acq();
	ut_atomic_u64_await_gt_sub_acq();
	ut_atomic_u64_await_ge_add_acq();
	ut_atomic_u64_await_ge_sub_acq();
	ut_atomic_u64_await_neq_add_rlx();
	ut_atomic_u64_await_neq_sub_rlx();
	ut_atomic_u64_await_eq_add_rlx();
	ut_atomic_u64_await_eq_sub_rlx();
	ut_atomic_u64_await_le_add_rlx();
	ut_atomic_u64_await_le_sub_rlx();
	ut_atomic_u64_await_gt_add_rlx();
	ut_atomic_u64_await_gt_sub_rlx();
	ut_atomic_u64_await_ge_add_rlx();
	ut_atomic_u64_await_ge_sub_rlx();

	return 0;
}
