(* ::Package:: *)

(* HeytingLeanBridge.wl

   Minimal Wolfram Language package for calling HeytingLean-exported C symbols.

   This is intentionally tiny and aligns with `lambda_kernel_export`, which emits
   a nat→nat demo function `heyting_add1`.
*)

BeginPackage["HeytingLeanBridge`"]

LoadHeytingKernel::usage =
  "LoadHeytingKernel[path] loads a HeytingLean kernel shared library and initializes FFI handles. \
If path is omitted, defaults to dist/lambda_kernel_export/libheyting_kernel.so relative to the current directory."

HeytingKernelLoaded::usage = "HeytingKernelLoaded[] returns True if the library is loaded."

HeytingAdd1::usage = "HeytingAdd1[x] calls the exported heyting_add1 function (nat→nat demo)."

Begin["`Private`"]

$HeytingLibraryPath = None;
$HeytingLoaded = False;
$HeytingAdd1Fn = None;

LoadHeytingKernel[path_: Automatic] := Module[{p = path},
  If[p === Automatic,
    p = FileNameJoin[{Directory[], "dist", "lambda_kernel_export", "libheyting_kernel.so"}];
  ];
  If[!FileExistsQ[p],
    Message[LoadHeytingKernel::notfound, p];
    Return[$Failed];
  ];
  $HeytingLibraryPath = p;
  $HeytingAdd1Fn = ForeignFunctionLoad[p, "heyting_add1", {CLong} -> CLong];
  $HeytingLoaded = True;
  True
]

LoadHeytingKernel::notfound = "HeytingLean kernel library not found at path: `1`";

HeytingKernelLoaded[] := $HeytingLoaded

HeytingAdd1[x_Integer] /; $HeytingLoaded := $HeytingAdd1Fn[x]
HeytingAdd1[___] /; !$HeytingLoaded := (Message[HeytingAdd1::notloaded]; $Failed)
HeytingAdd1::notloaded = "HeytingLean kernel library not loaded. Call LoadHeytingKernel first.";

End[]
EndPackage[]

