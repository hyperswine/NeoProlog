#include <poll.h>
#include <errno.h>
/* Single-threaded runner owns the socket for this complete call. */
int infera_poll_read(int fd) {
    struct pollfd p = {fd, POLLIN, 0};
    int r;
    do { r = poll(&p, 1, 0); } while (r < 0 && errno == EINTR);
    return r > 0 && (p.revents & (POLLIN | POLLHUP | POLLERR));
}
