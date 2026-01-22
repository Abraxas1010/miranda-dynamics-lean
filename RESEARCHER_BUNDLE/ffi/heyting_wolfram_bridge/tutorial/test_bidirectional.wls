#!/usr/bin/env wolframscript

(* ============================================= *)
(* BIDIRECTIONAL INTEGRATION TEST                *)
(* (Wolfram verifies C outputs)                  *)
(* ============================================= *)

Print["Bidirectional Integration Test"];
Print["================================\n"];

scriptDir = If[$InputFileName =!= "", DirectoryName[$InputFileName], Directory[]];
libPath = ExpandFileName @ Replace[
  Environment["LIBTEST_HEYTINGLEAN_SO"],
  {
    s_String /; StringLength[s] > 0 :> s,
    _ :> FileNameJoin[{scriptDir, "libtest_heytinglean.so"}]
  }
];

If[!FileExistsQ[libPath],
  Print["ERROR: Library not found at: ", libPath];
  Exit[1];
];

(* Load C functions *)
fieldAdd = ForeignFunctionLoad[libPath, "verified_field_add",
  {"UnsignedInteger64", "UnsignedInteger64"} -> "UnsignedInteger64"];
fieldMult = ForeignFunctionLoad[libPath, "verified_field_mult",
  {"UnsignedInteger64", "UnsignedInteger64"} -> "UnsignedInteger64"];
modExp = ForeignFunctionLoad[libPath, "verified_mod_exp",
  {"UnsignedInteger64", "UnsignedInteger64", "UnsignedInteger64"} -> "UnsignedInteger64"];
sumArray = ForeignFunctionLoad[libPath, "sum_array",
  {"RawPointer"::["CDouble"], "Integer64"} -> "CDouble"];

allOk = True;

(* -------------------------------------------- *)
(* TEST 1: Symbolic → C → Verify                *)
(* -------------------------------------------- *)
Print["TEST 1: Symbolic Generation → C Execution → Symbolic Verification"];
SeedRandom[42];
a = RandomInteger[{1, 1000}];
b = RandomInteger[{1, 1000}];
Print["  Generated: a = ", a, ", b = ", b];

cSum = fieldAdd[a, b];
cProd = fieldMult[a, b];
wSum = a + b;
wProd = a * b;

Print["  Addition: C=", cSum, ", Wolfram=", wSum];
Print["  Multiplication: C=", cProd, ", Wolfram=", wProd];
allOk = allOk && (cSum == wSum) && (cProd == wProd);
Print[""];

(* -------------------------------------------- *)
(* TEST 2: C Array ↔ Wolfram List               *)
(* -------------------------------------------- *)
Print["TEST 2: Array/List Round-Trip"];
wList = Table[n^2, {n, 1, 10}];
Print["  Wolfram list: ", wList];
cArray = RawMemoryExport[N[wList], "CDouble"];
cSum2 = sumArray[cArray["Value"], 10];
wSum2 = Total[wList];
Print["  Sum via C: ", cSum2];
Print["  Sum via Wolfram: ", wSum2];
allOk = allOk && (Abs[cSum2 - wSum2] < 0.001);
RawMemoryFree[cArray["Value"]];
Print[""];

(* -------------------------------------------- *)
(* TEST 3: Mixed Crypto Simulation              *)
(* -------------------------------------------- *)
Print["TEST 3: Cryptographic Workflow Simulation"];
p = 997; g = 5; x = 123;
Print["  Parameters: p=", p, ", g=", g, ", x=", x];

cPublicKey = modExp[g, x, p];
wPublicKey = PowerMod[g, x, p];
Print["  Public key (C):       ", cPublicKey];
Print["  Public key (Wolfram): ", wPublicKey];
allOk = allOk && (cPublicKey == wPublicKey);

message = 42;
k = 67;
c1 = modExp[g, k, p];
c2 = Mod[message * modExp[wPublicKey, k, p], p];
s = modExp[c1, x, p];
sInv = PowerMod[s, -1, p];
decrypted = Mod[c2 * sInv, p];
Print["  Original message: ", message];
Print["  Decrypted message: ", decrypted];
allOk = allOk && (message == decrypted);
Print[""];

(* -------------------------------------------- *)
(* TEST 4: Performance Comparison               *)
(* -------------------------------------------- *)
Print["TEST 4: Performance Comparison"];
iterations = ToExpression @ Replace[Environment["LIBTEST_ITERATIONS"], {s_String /; StringLength[s] > 0 :> s, _ :> "20000"}];
iterations = If[IntegerQ[iterations] && iterations > 0, iterations, 20000];

cTime = AbsoluteTiming[Do[modExp[7, 1000, 997], {iterations}]][[1]];
wTime = AbsoluteTiming[Do[PowerMod[7, 1000, 997], {iterations}]][[1]];

Print["  ", iterations, " mod_exp operations:"];
Print["    C time:       ", NumberForm[cTime, 4], " seconds"];
Print["    Wolfram time: ", NumberForm[wTime, 4], " seconds"];
If[cTime > 0, Print["    Ratio: ", NumberForm[wTime/cTime, 3], "x"]];
Print[""];

(* -------------------------------------------- *)
(* TEST 5: Edge Cases                           *)
(* -------------------------------------------- *)
Print["TEST 5: Edge Case Test"];
edgeCases = {{0, 0}, {1, 1}, {2^32 - 1, 1}};
Do[
  {aa, bb} = case;
  cRes = fieldAdd[aa, bb];
  wRes = aa + bb;
  ok = (cRes == wRes);
  allOk = allOk && ok;
  Print["  fieldAdd[", aa, ", ", bb, "] = ", cRes, " (expected: ", wRes, ")"];
  ,
  {case, edgeCases}
];
Print[""];

Print["================================"];
Print["Bidirectional Tests Complete"];
Print["================================"];

If[allOk, Exit[0], Exit[1]];
