#!/usr/bin/env wolframscript

(* ============================================= *)
(* Proof hypergraph witness generator             *)
(* Produces a deterministic derivation/toposort    *)
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
If[Length[args] < 3,
  Print["Usage: proof_hypergraph_witness.wls <data.bin> <lengths.bin> <rootId>"];
  Exit[2];
];

dataPath = args[[1]];
lengthsPath = args[[2]];
rootId = ToExpression[args[[3]]];

data = readInt64List[dataPath];
lengths = readInt64List[lengthsPath];
If[data === $Failed || lengths === $Failed,
  Print["{\"ok\":false,\"error\":\"failed to read binary inputs\"}"];
  Exit[1];
];

hyper = reconstructHypergraph[data, lengths];
vertices = Union[Flatten[hyper]];
parents = Union[Last /@ hyper];
leaves = Complement[vertices, parents];

known = Sort[leaves];
remaining = hyper;
order = known;
steps = {};

availableEdgeQ[edge_List] := SubsetQ[known, Most[edge]];

While[True,
  avail = Select[remaining, availableEdgeQ];
  If[Length[avail] == 0, Break[]];
  pick = First @ SortBy[avail, Last];
  parent = Last[pick];
  If[!MemberQ[known, parent],
    AppendTo[steps, <|"parent" -> parent, "premises" -> Most[pick], "edge" -> pick|>];
    known = Sort[Union[known, {parent}]];
    order = Append[order, parent];
  ];
  remaining = DeleteCases[remaining, pick, 1, 1];
];

ok = MemberQ[known, rootId];

payload = <|
  "ok" -> ok,
  "derivedRoot" -> rootId,
  "leafCount" -> Length[leaves],
  "hyperedgeCount" -> Length[hyper],
  "steps" -> steps,
  "order" -> order
|>;

Print[ExportString[payload, "JSON", "Compact" -> True]];

Exit[If[ok, 0, 1]];

