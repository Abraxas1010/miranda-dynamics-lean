#!/usr/bin/env wolframscript

(* ============================================= *)
(* Lean ↔ Wolfram lossless I/O helper            *)
(* Reads a hypergraph binary pair (data+lengths) *)
(* and re-exports it (parse + re-encode).        *)
(* ============================================= *)

args = Rest[$ScriptCommandLine];

usage[] := Module[{},
  Print["Usage:"];
  Print["  wolframscript -file ", $InputFileName, " <in_hypergraph.bin> <in_lengths.bin> <out_hypergraph.bin> <out_lengths.bin>"];
];

If[Length[args] < 4,
  usage[];
  Exit[2];
];

inHyper = ExpandFileName[args[[1]]];
inLens = ExpandFileName[args[[2]]];
outHyper = ExpandFileName[args[[3]]];
outLens = ExpandFileName[args[[4]]];

If[!FileExistsQ[inHyper],
  Print["ERROR: input hypergraph not found: ", inHyper];
  Exit[1];
];
If[!FileExistsQ[inLens],
  Print["ERROR: input lengths not found: ", inLens];
  Exit[1];
];

readInt64List[path_] := Module[{s, xs},
  s = OpenRead[path, BinaryFormat -> True, ByteOrdering -> -1];
  xs = BinaryReadList[s, "Integer64"];
  Close[s];
  xs
];

lengths = readInt64List[inLens];
data = readInt64List[inHyper];

If[Total[lengths] =!= Length[data],
  Print["ERROR: length mismatch: Total[lengths]=", Total[lengths], " but data length=", Length[data]];
  Exit[1];
];

writeInt64List[path_, xs_] := Module[{dir, s},
  dir = DirectoryName[path];
  If[dir =!= "" && !DirectoryQ[dir],
    CreateDirectory[dir, CreateIntermediateDirectories -> True];
  ];
  s = OpenWrite[path, BinaryFormat -> True, ByteOrdering -> -1];
  BinaryWrite[s, xs, "Integer64"];
  Close[s];
];

(* Reconstruct hypergraph (to confirm the format is well-formed) *)
edges = TakeList[data, lengths];

(* Re-export via a fresh encode path *)
flat2 = Flatten[edges];
lengths2 = Length /@ edges;

If[flat2 =!= data || lengths2 =!= lengths,
  Print["ERROR: internal roundtrip mismatch while parsing notebook binary format."];
  Exit[1];
];

writeInt64List[outHyper, flat2];
writeInt64List[outLens, lengths2];

Print["OK"];
Exit[0];
