#include "Rts.h"
#include <unistd.h>

/* Bound the Haskell heap by the machine rather than by a constant: unless
   +RTS -M chose a limit, allow three quarters of physical memory. Running
   past it raises HeapOverflow, which the CLI, REPL and run mode report as
   an out-of-memory fault instead of letting the system kill the process. */
void infera_cap_heap(void) {
    if (RtsFlags.GcFlags.maxHeapSize != 0) return;
    long pages = sysconf(_SC_PHYS_PAGES), size = sysconf(_SC_PAGESIZE);
    if (pages <= 0 || size <= 0) return;
    unsigned long long bytes = (unsigned long long)pages * (unsigned long long)size / 4 * 3;
    unsigned long long blocks = bytes / BLOCK_SIZE;
    RtsFlags.GcFlags.maxHeapSize = blocks > 0xffffffffULL ? 0xffffffffU : (uint32_t)blocks;
}
