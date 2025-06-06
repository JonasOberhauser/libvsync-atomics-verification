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
    vatomic_fence();
    vatomic_fence_acq();
    vatomic_fence_rel();
    vatomic_fence_rlx();
}
