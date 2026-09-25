#define _POSIX_C_SOURCE 200809L
#include <errno.h>
#include <fcntl.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/socket.h>
#include <sys/wait.h>
#include <unistd.h>

/* Keep the same open file description in the parent and both child streams,
   so a bad restoration is visible after the host has exited. */
int main(int argc, char **argv) {
  if (argc != 5) return 2;
  int sockets[2];
  if (socketpair(AF_UNIX, SOCK_STREAM, 0, sockets) != 0) {
    perror("socketpair");
    return 1;
  }
  int flags = fcntl(sockets[0], F_GETFL);
  if (flags < 0 || fcntl(sockets[0], F_SETFL,
      atoi(argv[3]) ? flags | O_NONBLOCK : flags & ~O_NONBLOCK) < 0) {
    perror("set initial flags");
    return 1;
  }
  int before = fcntl(sockets[0], F_GETFL);
  if (before < 0) { perror("get initial flags"); return 1; }
  pid_t child = fork();
  if (child < 0) { perror("fork"); return 1; }
  if (child == 0) {
    if (dup2(sockets[0], STDIN_FILENO) < 0 ||
        dup2(sockets[0], STDOUT_FILENO) < 0) _exit(125);
    close(sockets[0]);
    close(sockets[1]);
    alarm(5);
    execl(argv[1], argv[1], argv[2], (char *)NULL);
    _exit(126);
  }
  int status;
  while (waitpid(child, &status, 0) < 0) {
    if (errno != EINTR) { perror("waitpid"); return 1; }
  }
  int after = fcntl(sockets[0], F_GETFL);
  close(sockets[0]);
  close(sockets[1]);
  if (!WIFEXITED(status) || WEXITSTATUS(status) != atoi(argv[4])) {
    fprintf(stderr, "unexpected host wait status: %d\n", status);
    return 1;
  }
  if (after != before) {
    fprintf(stderr, "shared stream flags changed: %d -> %d\n", before, after);
    return 1;
  }
  return 0;
}
