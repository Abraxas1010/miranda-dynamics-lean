#!/usr/bin/env wolframscript

(* Wolfram → C integration smoke test for HeytingLean-exported kernel.

   Requires: wolframscript (Wolfram Engine).
   Usage:
     HEYTING_WOLFRAM_LIB=dist/lambda_kernel_export/libheyting_kernel.so wolframscript -file ffi/heyting_wolfram_bridge/test_wolfram_to_heyting_kernel.wls
*)

Print["Wolfram → HeytingLean kernel FFI test"];
Print["====================================\n"];

libPath = Environment["HEYTING_WOLFRAM_LIB"];
If[libPath === Missing["NotAvailable"] || libPath === "" ,
  root = ExpandFileName[FileNameJoin[{DirectoryName[$InputFileName], "..", ".."}]];
  libPath = FileNameJoin[{root, "dist", "lambda_kernel_export", "libheyting_kernel.so"}];
];
libPath = ExpandFileName[libPath];

If[!FileExistsQ[libPath],
  Print["ERROR: shared library not found at: ", libPath];
  Exit[1];
];

Print["Library: ", libPath];

add1 = ForeignFunctionLoad[libPath, "heyting_add1", {"Integer64"} -> "Integer64"];
add2 = ForeignFunctionLoad[libPath, "heyting_add2", {"Integer64", "Integer64"} -> "Integer64"];

tests = {0, 1, 2, 41, 123, 1024};
allPass = True;
Do[
  x = t;
  y = add1[x];
  expected = x + 1;
  pass = IntegerQ[y] && (y == expected);
  If[!pass, allPass = False];
  Print["  heyting_add1(", x, ") = ", y, " (expected: ", expected, ") ", If[pass, "PASS", "FAIL"]];
,
{t, tests}
];

Print[""];
Print["Testing heyting_add2 (Nat→Nat→Nat)"];
pairs = {{0, 0}, {1, 0}, {0, 1}, {2, 3}, {20, 22}, {123, 456}};
Do[
  x = p[[1]];
  y = p[[2]];
  z = add2[x, y];
  expected = x + y;
  pass = IntegerQ[z] && (z == expected);
  If[!pass, allPass = False];
  Print["  heyting_add2(", x, ", ", y, ") = ", z, " (expected: ", expected, ") ", If[pass, "PASS", "FAIL"]];
,
{p, pairs}
];

Print["\nResult: ", If[allPass, "PASS", "FAIL"]];
Exit[If[allPass, 0, 1]];
