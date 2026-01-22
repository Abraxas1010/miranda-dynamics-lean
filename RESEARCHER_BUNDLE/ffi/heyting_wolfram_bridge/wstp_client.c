/*
 * Minimal WSTP client (C → Wolfram Kernel).
 *
 * This is intentionally small and build-guarded: you need a Wolfram installation
 * with the WSTP SDK (wstp.h + libs) to compile it.
 *
 * Primary external references:
 * - WSTP Unix developer guide:
 *   https://reference.wolfram.com/language/tutorial/WSTPDeveloperGuide-Unix.html?view=all
 * - WSOpenString:
 *   https://reference.wolfram.com/language/ref/c/WSOpenString.html?view=all
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "wstp.h"

static WSENV g_env = (WSENV)0;
static WSLINK g_link = (WSLINK)0;

static void wolfram_cleanup(void) {
  if (g_link != (WSLINK)0) {
    WSClose(g_link);
    g_link = (WSLINK)0;
  }
  if (g_env != (WSENV)0) {
    WSDeinitialize(g_env);
    g_env = (WSENV)0;
  }
}

static int wolfram_init(void) {
  int error = 0;
  const char* kernel = getenv("WOLFRAM_KERNEL");
  if (kernel == NULL || kernel[0] == '\0') {
    kernel = "WolframKernel";
  }

  g_env = WSInitialize((WSEnvironmentParameter)0);
  if (g_env == (WSENV)0) {
    fprintf(stderr, "WSInitialize failed\n");
    return -1;
  }

  /* Launch a local kernel via WSTP. */
  char link_args[1024];
  snprintf(link_args, sizeof(link_args), "-linkmode launch -linkname '%s -wstp'", kernel);

  g_link = WSOpenString(g_env, link_args, &error);
  if (g_link == (WSLINK)0) {
    fprintf(stderr, "WSOpenString failed (error=%d)\n", error);
    wolfram_cleanup();
    return -1;
  }

  return 0;
}

static int wolfram_eval_int64(const char* expr, wsint64* out) {
  if (g_link == (WSLINK)0) {
    return -1;
  }

  /* EvaluatePacket[ToExpression[expr]] */
  if (!WSPutFunction(g_link, "EvaluatePacket", 1)) return -1;
  if (!WSPutFunction(g_link, "ToExpression", 1)) return -1;
  if (!WSPutString(g_link, expr)) return -1;
  if (!WSEndPacket(g_link)) return -1;

  int pkt = 0;
  while ((pkt = WSNextPacket(g_link)) && pkt != RETURNPKT) {
    WSNewPacket(g_link);
  }
  if (pkt == 0) {
    return -1;
  }

  if (!WSGetInteger64(g_link, out)) {
    WSNewPacket(g_link);
    return -1;
  }

  /* Clear packet contents */
  WSNewPacket(g_link);
  return 0;
}

int main(int argc, char** argv) {
  (void)argc;
  (void)argv;

  printf("WSTP client smoke test\n");
  printf("======================\n");

  if (wolfram_init() != 0) {
    fprintf(stderr, "E: failed to initialize WSTP link\n");
    return 1;
  }

  wsint64 v = 0;
  if (wolfram_eval_int64("2 + 2", &v) != 0) {
    fprintf(stderr, "E: failed to evaluate expression via WSTP\n");
    wolfram_cleanup();
    return 1;
  }

  printf("2 + 2 = %lld\n", (long long)v);
  wolfram_cleanup();
  return (v == 4) ? 0 : 1;
}
