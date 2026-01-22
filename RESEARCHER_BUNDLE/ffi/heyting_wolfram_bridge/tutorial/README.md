# Wolfram ↔ C tutorial (standalone)

This directory contains a **standalone** Wolfram Engine ↔ C ForeignFunctionLoad tutorial.
It is intentionally separate from the repo-integrated HeytingLean→C export workflow.

## Run

From the repo root:

```bash
./scripts/qa_wolfram_tutorial.sh
```

If you want to run the Wolfram tests directly:

```bash
cc -shared -fPIC -O2 -o ffi/heyting_wolfram_bridge/tutorial/libtest_heytinglean.so \
  ffi/heyting_wolfram_bridge/tutorial/libtest_heytinglean.c -lm

LIBTEST_HEYTINGLEAN_SO="$PWD/ffi/heyting_wolfram_bridge/tutorial/libtest_heytinglean.so" \
  wolframscript -file ffi/heyting_wolfram_bridge/tutorial/test_wolfram_to_c.wls

LIBTEST_HEYTINGLEAN_SO="$PWD/ffi/heyting_wolfram_bridge/tutorial/libtest_heytinglean.so" \
  wolframscript -file ffi/heyting_wolfram_bridge/tutorial/test_bidirectional.wls
```

