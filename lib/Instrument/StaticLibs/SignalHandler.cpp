/*
 * Copyright (C) 2016 David Devecsery
 */

#include <signal.h>
#include <unistd.h>

#include <cassert>
#include <cstring>

#include <iostream>
#include <fstream>

// Okay, make a signal handler mask for this thread
static const bool signal_is_term[] = {
  false,  // 0  - ?
  true,   // SIGHUP - 1
  true,   // SIGINT
  true,   // SIGQUIT
  true,   // SIGILL
  false,  // SIGTRAP - 5
  true,   // SIGABRT
  true,   // SIGBUS - 7
  true,   // SIGFPE
  true,   // SIGKILL
  true,   // SIGUSR1
  true,   // SIGSEGV
  true,   // SIGUSR2
  true,   // SIGPIPE - 13
  true,   // SIGALRM
  true,   // SIGTERM
  true,   // SIGSTKFLT
  false,  // SIGCHLD - 17
  false,  // SIGCONT
  false,  // SIGSTOP
  false,  // SIGTSTP
  false,  // SIGTTIN
  false,  // SIGTTOU
  false,  // SIGURG
  true,   // SIGXCPU
  true,   // SIGXFSZ
  true,   // SIGVTALRM
  true,   // SIGPROF
  false,  // SIGWINCH
  true,   // SIGIO
  true,   // SIGPWR
  true,   // SIGSYS
};

static void (*exit_fcn)(void);

static void term_handler(int signo) {
  /*
  std::ofstream ofil("/tmp/ngx_sighand.out", std::ios::app);

  ofil << getpid() << ": Caught signal: " << signo << "\n";
  */
  exit_fcn();

  _exit(signo);
}

// typedef void (*sigcall_t )(int, siginfo_t *, void *);
typedef void (*sigcall_t )(int);
static sigcall_t reset_shims[] = {
  NULL,  // 0  - ?
  NULL,   // SIGHUP - 1
  NULL,   // SIGINT
  NULL,   // SIGQUIT
  NULL,   // SIGILL
  NULL,  // SIGTRAP - 5
  NULL,   // SIGABRT
  NULL,   // SIGBUS - 7
  NULL,   // SIGFPE
  NULL,   // SIGKILL
  NULL,   // SIGUSR1
  NULL,   // SIGSEGV
  NULL,   // SIGUSR2
  NULL,   // SIGPIPE - 13
  NULL,   // SIGALRM
  NULL,   // SIGTERM
  NULL,   // SIGSTKFLT
  NULL,  // SIGCHLD - 17
  NULL,  // SIGCONT
  NULL,  // SIGSTOP
  NULL,  // SIGTSTP
  NULL,  // SIGTTIN
  NULL,  // SIGTTOU
  NULL,  // SIGURG
  NULL,   // SIGXCPU
  NULL,   // SIGXFSZ
  NULL,   // SIGVTALRM
  NULL,   // SIGPROF
  NULL,  // SIGWINCH
  NULL,   // SIGIO
  NULL,   // SIGPWR
  NULL,   // SIGSYS
};

static void reset_handler(int signo) {
  struct sigaction act;
  sigemptyset(&act.sa_mask);
  act.sa_flags = 0;
  act.sa_handler = term_handler;
  sigaction(signo, &act, nullptr);

  reset_shims[signo](signo);
}

/*
static void term_action(int signo, siginfo_t *, void *) {
  term_handler(signo);
}
*/

extern "C" {

void __SignalHandlers_init(void (*do_exit)(void)) {
  exit_fcn = do_exit;
  // Setup sigactions for all the term handlers
  // for each term signal, point to my handler
  // FIXME: max signal? -- 32?
  for (int i = 0; i < 32; i++) {
    if (signal_is_term[i]) {
      struct sigaction act;
      sigemptyset(&act.sa_mask);
      act.sa_flags = 0;
      act.sa_handler = term_handler;
      sigaction(i, &act, nullptr);
    }
  }
}

// wrap sigaction
int __SignalHandlers_sigaction_shim(int signo,
    const struct sigaction *act,
    struct sigaction *oldact) {
  // I dont handle SA_RESETHAND -- unless I have to
  // assert((act->sa_flags & SA_RESETHAND) && signal_is_term[signo] == false);
  int ret = 0;

  /*
  std::ofstream ofil("/tmp/ngx_sighand.out", std::ios::app);
  ofil << getpid() << ": sigaction wrap?: " << signo << "\n";
  */

  // If they are setting the handler, do that
  if (act->sa_flags & SA_SIGINFO) {
    // If its not a term operation
    if (act->sa_handler != SIG_DFL || !signal_is_term[signo]) {
      // ofil << "wrap non-dfl" << std::endl;;
      if ((act->sa_flags & SA_RESETHAND) && signal_is_term[signo] == false) {
        struct sigaction newact;
        memcpy(static_cast<void *>(&newact),
            static_cast<const void *>(act), sizeof(newact));
        newact.sa_flags &= ~SA_RESETHAND;
        reset_shims[signo] = act->sa_handler;
        newact.sa_handler = reset_handler;
        ret = sigaction(signo, &newact, oldact);
      } else {
        ret = sigaction(signo, act, oldact);
      }

    // If its a term operation
    } else {
      struct sigaction new_act;
      memcpy(&new_act, act, sizeof(new_act));
      new_act.sa_handler = term_handler;
      // ofil << "wrap overwrite??" << std::endl;;
      ret = sigaction(signo, &new_act, oldact);
    }
  } else {
    // ofil << "wrap sigaction" << std::endl;;
    if ((act->sa_flags & SA_RESETHAND) && signal_is_term[signo] == false) {
      struct sigaction newact;
      memcpy(static_cast<void *>(&newact),
          static_cast<const void *>(act), sizeof(newact));
      newact.sa_flags &= ~SA_RESETHAND;
      reset_shims[signo] = act->sa_handler;
      newact.sa_handler = reset_handler;
      ret = sigaction(signo, &newact, oldact);
    } else {
      ret = sigaction(signo, act, oldact);
    }
    /*
    if (act->sa_sigaction != SIG_DFL || !signal_is_term(signo)) {
    } else {
      struct sigaction new_act;
      memcpy(&new_act, act, sizeof(new_act));
      new_act.sa_handler = term_handler;
      ret = sigaction(signo, act, oldact);
    }
    */
  }

  return ret;
}

int __SignalHandlers_exit_shim(int code) {
  /*
  std::ofstream ofil("/tmp/ngx_sighand.out", std::ios::app);
  ofil << getpid() << ": _exit code: " << code << "\n";
  */
  exit_fcn();

  _exit(code);
}

}
