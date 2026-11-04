/*
 * cbits/infera_jit.c
 *
 * Executable page allocation and CPU feature detection for Infera's native WAM JIT tier.
 * Adapted from fprisc:compiler/cbits/handjit.c
 * Copyright (c) 2026 Jasen Qin (hyperswine), MIT License.
 */

#include <stdint.h>
#include <string.h>
#include <sys/mman.h>

#if defined(__APPLE__)
#include <pthread.h>
#include <libkern/OSCacheControl.h>
#endif

static size_t round_page(size_t n) {
    size_t page = 16384;
    return (n + page - 1) & ~(page - 1);
}

void *infera_jit_alloc(const uint8_t *code, int len) {
    if (len <= 0 || !code) return 0;
    size_t sz = round_page((size_t)len);
    int flags = MAP_PRIVATE | MAP_ANON;
#if defined(__APPLE__) && defined(__aarch64__)
    flags |= MAP_JIT;
#endif
    void *p = mmap(0, sz, PROT_READ | PROT_WRITE | PROT_EXEC, flags, -1, 0);
    if (p == MAP_FAILED) {
        p = mmap(0, sz, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANON, -1, 0);
        if (p == MAP_FAILED) return 0;
        memcpy(p, code, (size_t)len);
        if (mprotect(p, sz, PROT_READ | PROT_EXEC) != 0) {
            munmap(p, sz);
            return 0;
        }
    } else {
#if defined(__APPLE__) && defined(__aarch64__)
        pthread_jit_write_protect_np(0);
#endif
        memcpy(p, code, (size_t)len);
#if defined(__APPLE__) && defined(__aarch64__)
        pthread_jit_write_protect_np(1);
#endif
    }
#if defined(__APPLE__)
    sys_icache_invalidate(p, (size_t)len);
#elif defined(__GNUC__) || defined(__clang__)
    __builtin___clear_cache((char *)p, (char *)p + len);
#endif
    return p;
}

void infera_jit_free(void *ptr, int len) {
    if (!ptr || len <= 0) return;
    munmap(ptr, round_page((size_t)len));
}

int infera_jit_has_sse41(void) {
#if defined(__x86_64__) || defined(_M_X64)
    uint32_t eax = 1, ebx = 0, ecx = 0, edx = 0;
    __asm__ volatile("cpuid"
                     : "+a"(eax), "=b"(ebx), "=c"(ecx), "=d"(edx));
    return (ecx & (1u << 19)) ? 1 : 0;
#else
    return 0;
#endif
}
