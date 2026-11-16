#include <poll.h>
#include <errno.h>
#include <stdlib.h>
#include <time.h>
static long long now_ms(void) {
    struct timespec t;
    clock_gettime(CLOCK_MONOTONIC, &t);
    return (long long)t.tv_sec * 1000 + t.tv_nsec / 1000000;
}

/* Block until one of n descriptors is readable (or at hangup/error) or the
   timeout passes; a negative timeout waits indefinitely. ready[i] is set to
   1 for each readable descriptor. Returns the number ready, 0 on timeout,
   or -errno. EINTR resumes with the remaining time. */
int infera_poll_many(const int *fds, int n, long long timeout_ms, int *ready) {
    struct pollfd *ps = calloc(n > 0 ? n : 1, sizeof *ps);
    if (!ps) return -ENOMEM;
    for (int i = 0; i < n; i++) { ps[i].fd = fds[i]; ps[i].events = POLLIN; ready[i] = 0; }
    long long deadline = timeout_ms < 0 ? -1 : now_ms() + timeout_ms;
    int r;
    for (;;) {
        int wait;
        if (deadline < 0) wait = -1;
        else {
            long long left = deadline - now_ms();
            if (left < 0) left = 0;
            wait = left > 0x7fffffff ? 0x7fffffff : (int)left;
        }
        r = poll(ps, (nfds_t)n, wait);
        if (r >= 0) {
            if (r == 0 && deadline >= 0 && now_ms() < deadline) continue; /* clamped wait */
            break;
        }
        if (errno != EINTR) { r = -errno; break; }
    }
    if (r > 0)
        for (int i = 0; i < n; i++)
            ready[i] = (ps[i].revents & (POLLIN | POLLHUP | POLLERR | POLLNVAL)) != 0;
    free(ps);
    return r;
}
