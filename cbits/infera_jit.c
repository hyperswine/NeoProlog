/* infera_jit.c — executable memory for the Infera native JIT tier.
 *
 * Adapted from fprisc:compiler/cbits/handjit.c
 * Copyright (c) 2026 Jasen Qin (hyperswine), MIT License.
 *
 * On macOS arm64, supports both MAP_JIT + pthread_jit_write_protect_np
 * and W^X mprotect(PROT_READ | PROT_EXEC) with page-aligned sizing and
 * instruction-cache invalidation.
 */
#include <stdint.h>
#include <string.h>
#include <sys/mman.h>
#include <unistd.h>

#if defined(__APPLE__)
#include <libkern/OSCacheControl.h>
#include <pthread.h>
#endif

void *infera_jit_alloc(const uint8_t *buf, long n) {
  if (n <= 0) return 0;
  long page = sysconf(_SC_PAGESIZE);
  if (page <= 0) page = 16384;
  long sz = (n + page - 1) & ~(page - 1);

#if defined(__APPLE__) && defined(__aarch64__)
  void *p = mmap(0, (size_t)sz, PROT_READ | PROT_WRITE | PROT_EXEC,
                 MAP_PRIVATE | MAP_ANONYMOUS | MAP_JIT, -1, 0);
  if (p != MAP_FAILED) {
    pthread_jit_write_protect_np(0);
    memcpy(p, buf, (size_t)n);
    pthread_jit_write_protect_np(1);
    sys_icache_invalidate(p, (size_t)sz);
    return p;
  }
#endif

  void *p2 = mmap(0, (size_t)sz, PROT_READ | PROT_WRITE,
                  MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  if (p2 == MAP_FAILED) return 0;
  memcpy(p2, buf, (size_t)n);
  if (mprotect(p2, (size_t)sz, PROT_READ | PROT_EXEC) != 0) {
    munmap(p2, (size_t)sz);
    return 0;
  }
#if defined(__APPLE__)
  sys_icache_invalidate(p2, (size_t)sz);
#else
  __builtin___clear_cache((char *)p2, (char *)p2 + sz);
#endif
  return p2;
}

void infera_jit_free(void *p, long n) {
  if (!p || n <= 0) return;
  long page = sysconf(_SC_PAGESIZE);
  if (page <= 0) page = 16384;
  long sz = (n + page - 1) & ~(page - 1);
  munmap(p, (size_t)sz);
}

#if defined(__x86_64__)
#include <cpuid.h>
int infera_jit_has_sse41(void) {
  unsigned a, b, c, d;
  if (!__get_cpuid(1, &a, &b, &c, &d)) return 0;
  return (c & bit_SSE4_1) ? 1 : 0;
}
#else
int infera_jit_has_sse41(void) { return 1; }
#endif
