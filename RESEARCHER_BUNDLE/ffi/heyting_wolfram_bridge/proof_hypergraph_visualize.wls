#!/usr/bin/env wolframscript

(* ============================================= *)
(* Lean proof term hypergraph visualization       *)
(* Wolfram Physics style via WolframModelPlot     *)
(* ============================================= *)

readInt64List[path_String] := Module[{stream, data},
  stream = OpenRead[path, BinaryFormat -> True, ByteOrdering -> -1];
  If[stream === $Failed, Return[$Failed]];
  data = BinaryReadList[stream, "Integer64"];
  Close[stream];
  data
];

reconstructHypergraph[data_List, lengths_List] := TakeList[data, lengths];

args = Rest[$ScriptCommandLine];
If[Length[args] < 4,
  Print["Usage: proof_hypergraph_visualize.wls <data.bin> <lengths.bin> <metadata.json> <outDir>"];
  Exit[2];
];

dataPath = args[[1]];
lengthsPath = args[[2]];
metaPath = args[[3]];
outDir = args[[4]];

If[!FileExistsQ[dataPath] || !FileExistsQ[lengthsPath] || !FileExistsQ[metaPath],
  Print["ERROR: missing input file(s)."];
  Print["  data:   ", dataPath];
  Print["  lens:   ", lengthsPath];
  Print["  meta:   ", metaPath];
  Exit[2];
];

CreateDirectory[outDir, CreateIntermediateDirectories -> True];

data = readInt64List[dataPath];
lengths = readInt64List[lengthsPath];
If[data === $Failed || lengths === $Failed,
  Print["ERROR: failed to read binary inputs."];
  Exit[1];
];

hyper = reconstructHypergraph[data, lengths];
meta = Quiet @ Check[Import[metaPath, "RawJSON"], $Failed];
If[meta === $Failed,
  Print["ERROR: failed to parse metadata JSON: ", metaPath];
  Exit[1];
];

modelKey = Lookup[meta, "model", FileBaseName[dataPath]];
rootId = Lookup[meta, "root", Missing["NoRoot"]];

nodes = Lookup[meta, "nodes", {}];
labelAssoc = Association @ Map[
  (ToExpression[Lookup[#, "id", -1]] -> Lookup[#, "label", ""]) &,
  nodes
];
kindAssoc = Association @ Map[
  (ToExpression[Lookup[#, "id", -1]] -> Lookup[#, "kind", ""]) &,
  nodes
];

labelOf[v_] := Module[{lbl = Lookup[labelAssoc, v, ""]},
  If[StringLength[lbl] > 0,
    lbl,
    ToString[v]
  ]
];

shortLabelOf[v_] := Module[{lbl = labelOf[v]},
  If[StringLength[lbl] > 24, StringTake[lbl, 21] <> "…", lbl]
];

(* Hypergraph plot *)
setReplaceOk = (Quiet @ Check[Needs["SetReplace`"]; True, False]) === True;

hgPlot =
  If[setReplaceOk,
    WolframModelPlot[
      hyper,
      VertexSize -> 0.25,
      VertexLabels -> Placed[
        Thread[Union[Flatten[hyper]] -> (Tooltip[shortLabelOf[#], labelOf[#]] & /@ Union[Flatten[hyper]])],
        Center
      ]
    ],
    HypergraphPlot[
      hyper,
      VertexLabels -> Placed[
        Thread[Union[Flatten[hyper]] -> (Tooltip[shortLabelOf[#], labelOf[#]] & /@ Union[Flatten[hyper]])],
        Center
      ]
    ]
  ];

Export[FileNameJoin[{outDir, modelKey <> "_term_hypergraph.png"}], hgPlot];

(* Directed “proof DAG” view: premise → parent (parent = last vertex in each hyperedge). *)
dirEdges = Flatten[
  Table[
    DirectedEdge[child, Last[edge]],
    {edge, hyper},
    {child, Most[edge]}
  ],
  1
];

dagPlot =
  Graph[
    DeleteDuplicates[dirEdges],
    VertexLabels -> (v_ :> Placed[Tooltip[shortLabelOf[v], kindAssoc[v] <> ": " <> labelOf[v]], Center]),
    GraphLayout -> "LayeredDigraphEmbedding",
    ImageSize -> 900
  ];

Export[FileNameJoin[{outDir, modelKey <> "_term_dag.png"}], dagPlot];

(* Optional: collapsed constant-dependency view if present. *)
constMetaFiles = FileNames["*_constdeps_metadata.json", outDir];
If[Length[constMetaFiles] >= 1,
  constMeta = Quiet @ Check[Import[First[constMetaFiles], "RawJSON"], $Failed];
  If[constMeta =!= $Failed,
    constModel = Lookup[constMeta, "model", "constdeps"];
    constLabels = Lookup[constMeta, "labels", {}];
    constDataFiles = FileNames["*_constdeps_hypergraph.bin", outDir];
    constLenFiles = FileNames["*_constdeps_lengths.bin", outDir];
    If[Length[constDataFiles] >= 1 && Length[constLenFiles] >= 1,
      cdata = readInt64List[First[constDataFiles]];
      clens = readInt64List[First[constLenFiles]];
      cedges = reconstructHypergraph[cdata, clens];
      labelConst[v_] := Module[{i = v + 1},
        If[1 <= i <= Length[constLabels], constLabels[[i]], ToString[v]]
      ];
      cdir = DirectedEdge @@@ cedges;
      cplot =
        Graph[
          DeleteDuplicates[cdir],
          VertexLabels -> (v_ :> Placed[Tooltip[labelConst[v], labelConst[v]], Center]),
          GraphLayout -> "LayeredDigraphEmbedding",
          ImageSize -> 900
        ];
      Export[FileNameJoin[{outDir, constModel <> "_dag.png"}], cplot];
    ];
  ];
];

If[rootId =!= Missing["NoRoot"],
  Export[FileNameJoin[{outDir, modelKey <> "_root.txt"}], ToString[rootId], "Text"];
];

Exit[0];

