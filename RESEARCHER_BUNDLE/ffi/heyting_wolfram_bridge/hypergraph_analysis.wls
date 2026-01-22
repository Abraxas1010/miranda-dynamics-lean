#!/usr/bin/env wolframscript

(* ============================================= *)
(* WOLFRAM PHYSICS HYPERGRAPH ANALYSIS           *)
(* Integration with HeytingLean verified C code  *)
(* ============================================= *)

(* Require SetReplace for WolframModel. *)
If[Quiet@Check[Needs["SetReplace`"], $Failed] === $Failed,
    Print["ERROR: SetReplace` not available. Install from https://github.com/maxitg/SetReplace and re-run."];
    Exit[1];
];

Print["Wolfram Physics Hypergraph Analysis"];
Print["=====================================\n"];

(* --------------------------------------------- *)
(* CONFIGURATION                                 *)
(* --------------------------------------------- *)

(* Path to HeytingLean library *)
scriptDir = If[$InputFileName =!= "", DirectoryName[$InputFileName], Directory[]];
repoRoot = ExpandFileName[FileNameJoin[{scriptDir, "..", ".."}]];
libPath = FileNameJoin[{repoRoot, "dist", "lambda_kernel_export", "libheyting_kernel.so"}];

(* Check library exists *)
If[!FileExistsQ[libPath],
    Print["WARNING: HeytingLean library not found at: ", libPath];
    Print["Running in Wolfram-only mode.\n"];
    $HeytingAvailable = False;
,
    $HeytingAvailable = True;
    Print["HeytingLean library found: ", libPath, "\n"];
];

(* --------------------------------------------- *)
(* MODEL DEFINITIONS                             *)
(* --------------------------------------------- *)

$Models = <|
    "universe1" -> <|
        "name" -> "Universe 1 (Classic 2->3)",
        "rule" -> {{1,2,3},{2,4,5}} -> {{5,6,1},{6,4,2},{4,5,3}},
        "init" -> {{1,2,3},{2,4,5}},
        "description" -> "The original Wolfram Physics model"
    |>,
    "stringTheory" -> <|
        "name" -> "String Theory Analog",
        "rule" -> {{1,2},{2,3}} -> {{1,2},{2,4},{4,3}},
        "init" -> {{1,2},{2,3},{3,4},{4,5},{5,1}},
        "description" -> "Edge subdivision mimicking string worldsheets"
    |>,
    "triangleGrowth" -> <|
        "name" -> "Triangle Growth",
        "rule" -> {{1,2},{2,3},{3,1}} -> {{1,2},{2,4},{4,3},{3,1},{1,4}},
        "init" -> {{1,2},{2,3},{3,1}},
        "description" -> "Triangular structure expansion"
    |>,
    "starExpansion" -> <|
        "name" -> "Star to Clique",
        "rule" -> {{1,2},{1,3},{1,4}} -> {{2,3},{2,4},{2,5},{3,5},{4,5}},
        "init" -> {{1,2},{1,3},{1,4},{1,5}},
        "description" -> "Star graph transforms to clique"
    |>,
    "minimalCausal" -> <|
        "name" -> "Minimal Causal",
        "rule" -> {{1,2},{2,3}} -> {{1,2},{2,3},{3,4},{4,1}},
        "init" -> {{1,2},{2,3}},
        "description" -> "Minimal rule with non-trivial causal structure"
    |>
|>;

(* --------------------------------------------- *)
(* ANALYSIS FUNCTIONS                            *)
(* --------------------------------------------- *)

(* Run a model and extract properties *)
AnalyzeModel[modelKey_String, steps_Integer: 50] := Module[
    {model, evolution, finalState, result, spatialEdgeCount},

    model = $Models[modelKey];
    If[MissingQ[model],
        Print["Unknown model: ", modelKey];
        Return[$Failed]
    ];

    Print["Analyzing: ", model["name"]];
    Print["Rule: ", model["rule"]];
    Print["Steps: ", steps];
    Print[""];

    (* Run evolution *)
    evolution = WolframModel[
        model["rule"],
        model["init"],
        steps,
        "EventSelectionFunction" -> "GlobalSpacelike"
    ];

    finalState = evolution["FinalState"];
    spatialEdgeCount =
        If[AllTrue[finalState, ListQ[#] && Length[#] == 2 &],
            Length[finalState],
            -1
        ];

    (* Extract properties *)
    result = <|
        "modelKey" -> modelKey,
        "modelName" -> model["name"],
        "steps" -> steps,
        "finalState" -> finalState,
        "finalStateSize" -> Length[finalState],
        "eventCount" -> evolution["EventsCount"],
        "generations" -> evolution["TotalGenerationsCount"],
        "vertexCount" -> Length[Union[Flatten[finalState]]],
        "causalEdgeCount" -> EdgeCount[evolution["CausalGraph"]],
        "spatialEdgeCount" -> spatialEdgeCount
    |>;

    Print["Results:"];
    Print["  Final hyperedges: ", result["finalStateSize"]];
    Print["  Total events: ", result["eventCount"]];
    Print["  Vertices: ", result["vertexCount"]];
    Print["  Causal edges: ", result["causalEdgeCount"]];
    If[result["spatialEdgeCount"] >= 0,
        Print["  Spatial edges: ", result["spatialEdgeCount"]];
    ];
    Print[""];

    result
];

(* Convert hypergraph to flat array for C *)
HypergraphToArray[hypergraph_List] := Module[
    {flat, lengths},
    lengths = Length /@ hypergraph;
    flat = Flatten[hypergraph];
    <|"data" -> flat, "lengths" -> lengths, "count" -> Length[hypergraph]|>
];

(* Export for C consumption *)
ExportForC[result_Association, outputDir_String] := Module[
    {jsonPath, binPath, arrayData, stream},

    CreateDirectory[outputDir, CreateIntermediateDirectories -> True];

    (* JSON metadata *)
    jsonPath = FileNameJoin[{outputDir, result["modelKey"] <> "_metadata.json"}];
    Export[jsonPath, <|
        "model" -> result["modelKey"],
        "name" -> result["modelName"],
        "steps" -> result["steps"],
        "finalStateSize" -> result["finalStateSize"],
        "eventCount" -> result["eventCount"],
        "vertexCount" -> result["vertexCount"]
    |>];
    Print["Exported metadata: ", jsonPath];

    (* Binary hypergraph data *)
    arrayData = HypergraphToArray[result["finalState"]];
    binPath = FileNameJoin[{outputDir, result["modelKey"] <> "_hypergraph.bin"}];
    stream = OpenWrite[binPath, BinaryFormat -> True, ByteOrdering -> -1];
    BinaryWrite[stream, arrayData["data"], "Integer64"];
    Close[stream];
    Print["Exported binary data: ", binPath];

    (* Lengths file *)
    binPath = FileNameJoin[{outputDir, result["modelKey"] <> "_lengths.bin"}];
    stream = OpenWrite[binPath, BinaryFormat -> True, ByteOrdering -> -1];
    BinaryWrite[stream, arrayData["lengths"], "Integer64"];
    Close[stream];
    Print["Exported lengths: ", binPath];

    outputDir
];

(* --------------------------------------------- *)
(* HEYTINGLEAN INTEGRATION (if available)        *)
(* --------------------------------------------- *)

If[$HeytingAvailable,
    (* Load verified C functions *)
    Print["Loading HeytingLean functions..."];

    heytingAdd2 = ForeignFunctionLoad[libPath, "heyting_add2",
        {"Integer64", "Integer64"} -> "Integer64"];

    (* Verified computation on hypergraph data *)
    VerifiedHypergraphMetric[hypergraph_List] := Module[
        {flat},
        flat = Flatten[hypergraph];
        Fold[heytingAdd2[#1, #2] &, 0, flat]
    ];

    Print["HeytingLean functions loaded.\n"];
];

(* --------------------------------------------- *)
(* MAIN EXECUTION                                *)
(* --------------------------------------------- *)

(* Parse command line args *)
args = Rest[$ScriptCommandLine];
modelKey = If[Length[args] >= 1, args[[1]], "universe1"];
steps = If[Length[args] >= 2, ToExpression[args[[2]]], 50];
outputDir = If[Length[args] >= 3, args[[3]], "/tmp/hypergraph_output"];

(* Run analysis *)
result = AnalyzeModel[modelKey, steps];

If[result =!= $Failed,
    (* Export for C *)
    ExportForC[result, outputDir];

    (* Run verified computation if available *)
    If[$HeytingAvailable,
        Print["\nRunning verified computation on hypergraph..."];
        metric = VerifiedHypergraphMetric[result["finalState"]];
        Print["Verified metric result: ", metric];
    ];

    Print["\n====================================="];
    Print["Analysis complete."];
    Print["Output directory: ", outputDir];
];
