/* Local Darwin runner: flock(2), process-group deadline, and nice priority.
 * This is an execution resource wrapper, not a proof or compiler dependency. */
#include <errno.h>
#include <fcntl.h>
#include <math.h>
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/file.h>
#include <sys/resource.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>

static volatile sig_atomic_t interrupted;
static void on_signal(int sig) { interrupted = sig; }
static double now(void) {
  struct timespec t;
  if (clock_gettime(CLOCK_MONOTONIC, &t) != 0) { perror("clock_gettime"); exit(2); }
  return (double)t.tv_sec + (double)t.tv_nsec / 1e9;
}
static void pause_tick(void) {
  struct timespec t = {0, 10000000};
  nanosleep(&t, NULL);
}
static double duration(const char *value) {
  char *end;
  errno = 0;
  double n = strtod(value, &end);
  if (end == value || errno || !isfinite(n) || n < 0) return -1;
  if (*end) {
    if (end[1]) return -1;
    switch (*end) {
      case 's': break;
      case 'm': n *= 60; break;
      case 'h': n *= 3600; break;
      case 'd': n *= 86400; break;
      default: return -1;
    }
  }
  return isfinite(n) ? n : -1;
}
int main(int argc, char **argv) {
  if (argc < 5) return 2;
  double lock_limit = duration(argv[2]), run_limit = duration(argv[3]);
  if (lock_limit < 0 || run_limit <= 0) {
    fputs("leanrun: invalid lock or execution timeout\n", stderr); return 2;
  }
  struct sigaction action;
  memset(&action, 0, sizeof(action));
  action.sa_handler = on_signal;
  sigemptyset(&action.sa_mask);
  sigaction(SIGINT, &action, NULL);
  sigaction(SIGTERM, &action, NULL);
  sigaction(SIGHUP, &action, NULL);
  /* Leave this descriptor inherited: descendants retain the same lock. */
  int fd = open(argv[1], O_CREAT | O_RDWR, 0600);
  if (fd < 0) { perror("leanrun: open lock"); return 2; }
  double start = now();
  while (flock(fd, LOCK_EX | LOCK_NB) != 0) {
    if (errno != EWOULDBLOCK && errno != EINTR) { perror("leanrun: flock"); return 2; }
    if (interrupted) return 128 + interrupted;
    if (now() - start >= lock_limit) {
      fputs("leanrun: timed out waiting for the machine-wide Lean slot\n", stderr);
      return 75;
    }
    pause_tick();
  }
  if (interrupted) return 128 + interrupted;
  pid_t pid = fork();
  if (pid < 0) { perror("leanrun: fork"); return 2; }
  if (pid == 0) {
    if (setpgid(0, 0) != 0) { perror("leanrun: setpgid"); _exit(2); }
    signal(SIGINT, SIG_DFL); signal(SIGTERM, SIG_DFL); signal(SIGHUP, SIG_DFL);
    if (setpriority(PRIO_PROCESS, 0, 10) != 0) {
      const char *inherit = getenv("LEANRUN_INHERIT_PRIORITY");
      if (!inherit || strcmp(inherit, "1") != 0) {
        perror("leanrun: nice"); _exit(2);
      }
      fputs("leanrun: explicitly authorized inherited priority; nice unavailable\n", stderr);
    }
    setenv("LEANRUN_LOCAL_IN_SCOPE", "1", 1);
    execvp(argv[4], argv + 4);
    perror("leanrun: exec"); _exit(127);
  }
  setpgid(pid, pid);
  double deadline = now() + run_limit;
  int reason = 0, status = 0;
  for (;;) {
    pid_t result = waitpid(pid, &status, WNOHANG);
    if (result == pid) break;
    if (result < 0 && errno != EINTR) { perror("leanrun: waitpid"); return 2; }
    if (!reason && (interrupted || now() >= deadline)) {
      reason = interrupted ? 128 + interrupted : 124;
      kill(-pid, interrupted ? interrupted : SIGTERM);
      deadline = now() + 1;
    } else if (reason && now() >= deadline) {
      kill(-pid, SIGKILL);
    }
    pause_tick();
  }
  /* A timed-out leader can exit before its descendants; stop the entire group. */
  if (reason) { kill(-pid, SIGKILL); return reason; }
  if (WIFEXITED(status)) return WEXITSTATUS(status);
  return WIFSIGNALED(status) ? 128 + WTERMSIG(status) : 2;
}
