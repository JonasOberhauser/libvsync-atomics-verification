/*
 * Copyright (C) Huawei Technologies Co., Ltd. 2024. All rights reserved.
 * SPDX-License-Identifier: MIT
 */

/**
 * This C file call all available atomic APIs
 * It is not meant for running. It is to be used with `vsyncer info` in
 * different Configs to ensure the used barriers match the config.
 */
#include <vsync/atomic.h>

/* !!!Warning: File generated by tmpl; DO NOT EDIT.!!! */

vatomic8_t g_u8_a;
vuint8_t g_u8_v;
vatomic16_t g_u16_a;
vuint16_t g_u16_v;
vatomic32_t g_u32_a;
vuint32_t g_u32_v;
vatomic64_t g_u64_a;
vuint64_t g_u64_v;
vatomicptr_t g_ptr_a;
void *g_ptr_v;
vatomicsz_t g_sz_a;
vsize_t g_sz_v;

int
main(void)
{
    vatomic32_await_ge_sub(&g_u32_a, g_u32_v, g_u32_v);
    vatomic32_await_ge_sub_acq(&g_u32_a, g_u32_v, g_u32_v);
    vatomic32_await_ge_sub_rel(&g_u32_a, g_u32_v, g_u32_v);
    vatomic32_await_ge_sub_rlx(&g_u32_a, g_u32_v, g_u32_v);
    vatomic64_await_ge_sub(&g_u64_a, g_u64_v, g_u64_v);
    vatomic64_await_ge_sub_acq(&g_u64_a, g_u64_v, g_u64_v);
    vatomic64_await_ge_sub_rel(&g_u64_a, g_u64_v, g_u64_v);
    vatomic64_await_ge_sub_rlx(&g_u64_a, g_u64_v, g_u64_v);
}
