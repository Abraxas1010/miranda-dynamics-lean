#!/usr/bin/env wolframscript

(* ============================================= *)
(* NOTEBOOK → HYPERGRAPH RUNNER (Wolfram Engine) *)
(* Extract WolframModel examples from a .nb and  *)
(* run them headlessly via SetReplace`WolframModel *)
(* ============================================= *)

If[Quiet @ Check[Needs["SetReplace`"], $Failed] === $Failed,
  Print["ERROR: SetReplace` not available. Install from https://github.com/maxitg/SetReplace and re-run."];
  Exit[1];
];

scriptDir = If[$InputFileName =!= "", DirectoryName[$InputFileName], Directory[]];
repoRoot = ExpandFileName[FileNameJoin[{scriptDir, "..", ".."}]];
libPath = FileNameJoin[{repoRoot, "dist", "lambda_kernel_export", "libheyting_kernel.so"}];

$HeytingAvailable = FileExistsQ[libPath];
If[$HeytingAvailable,
  heytingAdd2 = ForeignFunctionLoad[libPath, "heyting_add2",
    {"Integer64", "Integer64"} -> "Integer64"];
  VerifiedHypergraphMetric[hypergraph_List] := Module[{flat},
    flat = Flatten[hypergraph];
    Fold[heytingAdd2[#1, #2] &, 0, flat]
  ];
];

HypergraphToArray[hypergraph_List] := Module[{flat, lengths},
  lengths = Length /@ hypergraph;
  flat = Flatten[hypergraph];
  <|"data" -> flat, "lengths" -> lengths, "count" -> Length[hypergraph]|>
];

ExportForC[result_Association, outputDir_String] := Module[
  {jsonPath, binPath, arrayData, stream, meta},

  CreateDirectory[outputDir, CreateIntermediateDirectories -> True];

  jsonPath = FileNameJoin[{outputDir, result["modelKey"] <> "_metadata.json"}];
  meta = <|
    "model" -> result["modelKey"],
    "name" -> result["modelName"],
    "notebook" -> result["notebookPath"],
    "notebookModelIndex" -> result["notebookModelIndex"],
    "steps" -> result["steps"],
    "finalStateSize" -> result["finalStateSize"],
    "eventCount" -> result["eventCount"],
    "vertexCount" -> result["vertexCount"]
  |>;
  If[KeyExistsQ[result, "verifiedMetric"],
    meta = Join[meta, <|"verifiedMetric" -> result["verifiedMetric"]|>];
  ];
  Export[jsonPath, meta];
  Print["Exported metadata: ", jsonPath];

  arrayData = HypergraphToArray[result["finalState"]];

  binPath = FileNameJoin[{outputDir, result["modelKey"] <> "_hypergraph.bin"}];
  stream = OpenWrite[binPath, BinaryFormat -> True, ByteOrdering -> -1];
  BinaryWrite[stream, arrayData["data"], "Integer64"];
  Close[stream];
  Print["Exported binary data: ", binPath];

  binPath = FileNameJoin[{outputDir, result["modelKey"] <> "_lengths.bin"}];
  stream = OpenWrite[binPath, BinaryFormat -> True, ByteOrdering -> -1];
  BinaryWrite[stream, arrayData["lengths"], "Integer64"];
  Close[stream];
  Print["Exported lengths: ", binPath];

  outputDir
];

ExtractNotebookWolframModelCalls[nb_Notebook] := Module[
  {inputBoxes, held, calls},

  inputBoxes = Cases[nb, Cell[BoxData[b_], "Input", ___] :> b, Infinity];
  held = ToExpression[#, StandardForm, HoldComplete] & /@ inputBoxes;

  calls = Flatten @ Cases[
    held,
    HoldPattern[
      HoldComplete[
        ResourceFunction[ResourceObject[assoc_Association, ___]][args___]
      ]
    ] /; Lookup[assoc, "Name", ""] === "WolframModel" :>
      <|"args" -> {args}, "meta" -> assoc|>,
    Infinity
  ];

  calls
];

NormalizeCall[call_Association] := Module[
  {argsList, params, rule, init, stepSpec},

  argsList = call["args"];
  params = If[Length[argsList] == 1 && ListQ[argsList[[1]]], argsList[[1]], argsList];

  If[Length[params] < 2,
    Return[$Failed]
  ];

  rule = params[[1]];
  init = params[[2]];
  stepSpec = If[Length[params] >= 3, params[[3]], Missing["stepSpec"]];

  <|
    "rule" -> rule,
    "init" -> init,
    "stepSpec" -> stepSpec,
    "rawArgs" -> params
  |>
];

args = Rest[$ScriptCommandLine];

usage[] := Module[{},
  Print["Usage:"];
  Print["  wolframscript -file ", $InputFileName, " <notebook.nb> [modelIndex] [stepsOverride] [outputDir]"];
  Print[""];
  Print["Notes:"];
  Print["  - modelIndex=0 prints discovered WolframModel calls and exits."];
  Print["  - stepsOverride=Automatic uses the notebook's step spec when available, else defaults to 50."];
];

If[Length[args] < 1,
  usage[];
  Exit[2];
];

notebookPath = ExpandFileName[args[[1]]];
If[!FileExistsQ[notebookPath],
  Print["ERROR: notebook not found: ", notebookPath];
  Exit[1];
];

modelIndex = If[Length[args] >= 2, ToExpression[args[[2]]], 1];
If[!IntegerQ[modelIndex], modelIndex = 1];

stepsOverride = If[Length[args] >= 3, ToExpression[args[[3]]], Automatic];
outputDir = If[Length[args] >= 4, args[[4]], "/tmp/notebook_hypergraph_output"];

Print["Notebook hypergraph runner"];
Print["========================"];
Print["Notebook: ", notebookPath];
Print["Output:   ", outputDir];
Print[""];

nb = Import[notebookPath, "Notebook"];
rawCalls = ExtractNotebookWolframModelCalls[nb];
normCalls = DeleteCases[NormalizeCall /@ rawCalls, $Failed];

If[Length[normCalls] == 0,
  Print["ERROR: no WolframModel calls found in notebook input cells."];
  Exit[1];
];

If[modelIndex == 0,
  Print["Discovered WolframModel calls: ", Length[normCalls]];
  Do[
    Print["  #", i, " stepSpec=", normCalls[[i]]["stepSpec"]];
    ,
    {i, 1, Length[normCalls]}
  ];
  Exit[0];
];

If[modelIndex < 1 || modelIndex > Length[normCalls],
  Print["ERROR: modelIndex out of range: ", modelIndex, " (valid: 1..", Length[normCalls], ")"];
  Exit[1];
];

selected = normCalls[[modelIndex]];

resolvedStepSpec := Module[{s = stepsOverride},
  Which[
    IntegerQ[s] && s > 0, s,
    s === Automatic && (IntegerQ[selected["stepSpec"]] || AssociationQ[selected["stepSpec"]]),
      selected["stepSpec"],
    True, 50
  ]
];

modelKey = FileBaseName[notebookPath] <> "_nb" <> ToString[modelIndex];
modelName = "NotebookModel[" <> FileNameTake[notebookPath] <> "]#" <> ToString[modelIndex];
stepSpec = resolvedStepSpec;

Print["Selected model index: ", modelIndex];
Print["Step spec: ", stepSpec];
Print[""];

evolution = WolframModel[
  selected["rule"],
  selected["init"],
  stepSpec,
  "EventSelectionFunction" -> "GlobalSpacelike"
];

finalState = evolution["FinalState"];

result = <|
  "modelKey" -> modelKey,
  "modelName" -> modelName,
  "notebookPath" -> notebookPath,
  "notebookModelIndex" -> modelIndex,
  "steps" -> stepSpec,
  "finalState" -> finalState,
  "finalStateSize" -> Length[finalState],
  "eventCount" -> evolution["EventsCount"],
  "vertexCount" -> Length[Union[Flatten[finalState]]]
|>;

Print["Results:"];
Print["  Final hyperedges: ", result["finalStateSize"]];
Print["  Total events:     ", result["eventCount"]];
Print["  Vertices:         ", result["vertexCount"]];

If[$HeytingAvailable,
  metric = VerifiedHypergraphMetric[finalState];
  result = Join[result, <|"verifiedMetric" -> ToString[metric]|>];
  Print["\nRunning HeytingLean verified metric over final state..."];
  Print["Verified metric: ", metric];
];

ExportForC[result, outputDir];

Print["\nOK"];
Exit[0];
