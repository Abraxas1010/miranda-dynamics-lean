#!/usr/bin/env wolframscript

(* ============================================= *)
(* WOLFRAM → C INTEGRATION TESTS                 *)
(* Using ForeignFunctionLoad                      *)
(* ============================================= *)

Print["Starting Wolfram → C Integration Tests"];
Print["========================================\n"];

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
  Print["Hint: build it via: cc -shared -fPIC -O2 -o ", FileNameJoin[{scriptDir, "libtest_heytinglean.so"}], " ", FileNameJoin[{scriptDir, "libtest_heytinglean.c"}], " -lm"];
  Exit[1];
];

Print["Library found: ", libPath];
Print[""];

fail[msg_] := (Print["✗ FAIL: ", msg]; $Failed)
pass[msg_] := (Print["✓ PASS: ", msg]; True)

allOk = True;

(* -------------------------------------------- *)
(* TEST 1: Basic Integer Arithmetic             *)
(* -------------------------------------------- *)
Print["TEST 1: Basic Integer Arithmetic"];

fieldAdd =
  ForeignFunctionLoad[libPath, "verified_field_add",
    {"UnsignedInteger64", "UnsignedInteger64"} -> "UnsignedInteger64"];

fieldMult =
  ForeignFunctionLoad[libPath, "verified_field_mult",
    {"UnsignedInteger64", "UnsignedInteger64"} -> "UnsignedInteger64"];

modExp =
  ForeignFunctionLoad[libPath, "verified_mod_exp",
    {"UnsignedInteger64", "UnsignedInteger64", "UnsignedInteger64"} -> "UnsignedInteger64"];

result1 = fieldAdd[17, 25]; expected1 = 42;
Print["  field_add(17, 25) = ", result1, " (expected: ", expected1, ")"];
allOk = allOk && (result1 == expected1);

result2 = fieldMult[6, 7]; expected2 = 42;
Print["  field_mult(6, 7) = ", result2, " (expected: ", expected2, ")"];
allOk = allOk && (result2 == expected2);

result3 = modExp[2, 10, 1000]; expected3 = 24;
Print["  mod_exp(2, 10, 1000) = ", result3, " (expected: ", expected3, ")"];
allOk = allOk && (result3 == expected3);

Print[""];

(* -------------------------------------------- *)
(* TEST 2: Array Operations                     *)
(* -------------------------------------------- *)
Print["TEST 2: Array Operations"];

sumArray =
  ForeignFunctionLoad[libPath, "sum_array",
    {"RawPointer"::["CDouble"], "Integer64"} -> "CDouble"];

dotProduct =
  ForeignFunctionLoad[libPath, "dot_product",
    {"RawPointer"::["CDouble"], "RawPointer"::["CDouble"], "Integer64"} -> "CDouble"];

arr1 = RawMemoryExport[{1.0, 2.0, 3.0, 4.0, 5.0}, "CDouble"];
arr2 = RawMemoryExport[{2.0, 2.0, 2.0, 2.0, 2.0}, "CDouble"];

result4 = sumArray[arr1["Value"], 5]; expected4 = 15.0;
Print["  sum_array([1,2,3,4,5]) = ", result4, " (expected: ", expected4, ")"];
allOk = allOk && (Abs[result4 - expected4] < 0.001);

result5 = dotProduct[arr1["Value"], arr2["Value"], 5]; expected5 = 30.0;
Print["  dot_product([1,2,3,4,5], [2,2,2,2,2]) = ", result5, " (expected: ", expected5, ")"];
allOk = allOk && (Abs[result5 - expected5] < 0.001);

RawMemoryFree[arr1["Value"]];
RawMemoryFree[arr2["Value"]];

Print[""];

(* -------------------------------------------- *)
(* TEST 3: Byte-String Operations               *)
(* -------------------------------------------- *)
Print["TEST 3: Byte-String Operations"];

stringLength =
  ForeignFunctionLoad[libPath, "string_length",
    {"RawPointer"::["UnsignedInteger8"], "Integer64"} -> "Integer64"];

isPalindrome =
  ForeignFunctionLoad[libPath, "is_palindrome",
    {"RawPointer"::["UnsignedInteger8"], "Integer64"} -> "Integer32"];

bytes1 = ToCharacterCode["Hello, World!", "UTF8"];
buf1 = RawMemoryExport[bytes1, "UnsignedInteger8"];
result6 = stringLength[buf1["Value"], Length[bytes1]]; expected6 = Length[bytes1];
Print["  string_length(\"Hello, World!\") = ", result6, " (expected: ", expected6, ")"];
allOk = allOk && (result6 == expected6);
RawMemoryFree[buf1["Value"]];

bytesA = ToCharacterCode["racecar", "UTF8"]; bufA = RawMemoryExport[bytesA, "UnsignedInteger8"];
bytesB = ToCharacterCode["hello", "UTF8"]; bufB = RawMemoryExport[bytesB, "UnsignedInteger8"];
result7a = isPalindrome[bufA["Value"], Length[bytesA]];
result7b = isPalindrome[bufB["Value"], Length[bytesB]];
Print["  is_palindrome(\"racecar\") = ", result7a, " (expected: 1)"];
Print["  is_palindrome(\"hello\") = ", result7b, " (expected: 0)"];
allOk = allOk && (result7a == 1) && (result7b == 0);
RawMemoryFree[bufA["Value"]];
RawMemoryFree[bufB["Value"]];

Print[""];

(* -------------------------------------------- *)
(* TEST 4: State Management                     *)
(* -------------------------------------------- *)
Print["TEST 4: State Management (Counter)"];

getCount =
  ForeignFunctionLoad[libPath, "get_call_count",
    {} -> "UnsignedInteger64"];

increment =
  ForeignFunctionLoad[libPath, "increment_counter",
    {} -> "Void"];

resetCount =
  ForeignFunctionLoad[libPath, "reset_counter",
    {} -> "Void"];

resetCount[];
initial = getCount[];
Print["  Initial count: ", initial];

increment[]; increment[]; increment[];
afterThree = getCount[];
Print["  After 3 increments: ", afterThree, " (expected: 3)"];
allOk = allOk && (afterThree == 3);

resetCount[];
afterReset = getCount[];
Print["  After reset: ", afterReset, " (expected: 0)"];
allOk = allOk && (afterReset == 0);

Print[""];

(* -------------------------------------------- *)
(* TEST 5: Error Handling                       *)
(* -------------------------------------------- *)
Print["TEST 5: Error Handling"];

safeDivide =
  ForeignFunctionLoad[libPath, "safe_divide",
    {"CDouble", "CDouble", "RawPointer"::["CDouble"]} -> "Integer32"];

resultMem = RawMemoryAllocate["CDouble", 1];
resultPtr = resultMem["Value"];

errCode1 = safeDivide[10.0, 2.0, resultPtr];
divResult = RawMemoryRead[resultMem];
Print["  safe_divide(10, 2): code=", errCode1, ", result=", divResult];
allOk = allOk && (errCode1 == 0) && (Abs[divResult - 5.0] < 0.001);

errCode2 = safeDivide[10.0, 0.0, resultPtr];
Print["  safe_divide(10, 0): code=", errCode2, " (expected: -1)"];
allOk = allOk && (errCode2 == -1);

RawMemoryFree[resultPtr];

Print[""];

(* -------------------------------------------- *)
(* TEST 6: Wolfram Cross-Verification           *)
(* -------------------------------------------- *)
Print["TEST 6: Wolfram Cross-Verification"];

{cRes, wRes, match} =
  Module[{base = 7, exp = 13, mod = 101, cResult, wResult},
    cResult = modExp[base, exp, mod];
    wResult = PowerMod[base, exp, mod];
    {cResult, wResult, cResult == wResult}
  ];

Print["  Hybrid mod_exp(7, 13, 101): C=", cRes, ", Wolfram=", wRes];
allOk = allOk && TrueQ[match];

Print[""];

Print["========================================"];
Print["Wolfram → C Tests Complete"];
Print["========================================"];

If[allOk, Exit[0], Exit[1]];
