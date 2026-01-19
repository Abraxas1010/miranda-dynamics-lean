// Miranda Dynamics UMAP Proof Data
// Generated from HeytingLean.MirandaDynamics (96 Lean files, 811 declarations)

const mirandaProofsData = {
  metadata: {
    project: "Miranda Dynamics",
    description: "Computational universality in dynamical systems",
    leanFiles: 96,
    totalDeclarations: 811,
    sorryCount: 0,
    generated: "2026-01-19"
  },
  families: {
    'TKFT': { color: '#3b82f6', count: 45 },
    'Billiards/Cantor': { color: '#10b981', count: 156 },
    'Billiards/Geometry': { color: '#22d3d3', count: 287 },
    'Computation': { color: '#f59e0b', count: 89 },
    'Discrete': { color: '#ef4444', count: 67 },
    'FixedPoint': { color: '#8b5cf6', count: 34 },
    'HeytingTuring': { color: '#ec4899', count: 28 },
    'Undecidability': { color: '#f97316', count: 19 },
    'External': { color: '#6366f1', count: 31 },
    'Fluids': { color: '#14b8a6', count: 38 },
    'Geometry': { color: '#a855f7', count: 17 }
  },
  items: [
    // TKFT Core
    { name: "ReachingRel", kind: "structure", family: "TKFT", pos: { x: 0.15, y: 0.20, z: 0.30 } },
    { name: "ReachingRel.comp", kind: "theorem", family: "TKFT", pos: { x: 0.18, y: 0.22, z: 0.32 } },
    { name: "ReachingRel.assoc", kind: "theorem", family: "TKFT", pos: { x: 0.20, y: 0.24, z: 0.28 } },
    { name: "ReachingRel.id_left", kind: "theorem", family: "TKFT", pos: { x: 0.17, y: 0.26, z: 0.31 } },
    { name: "ReachingRel.id_right", kind: "theorem", family: "TKFT", pos: { x: 0.19, y: 0.25, z: 0.29 } },
    { name: "reachingRelOfFlow", kind: "def", family: "TKFT", pos: { x: 0.22, y: 0.28, z: 0.35 } },
    { name: "TKFT.Obj", kind: "structure", family: "TKFT", pos: { x: 0.14, y: 0.18, z: 0.27 } },
    { name: "TKFT.equivalence", kind: "theorem", family: "TKFT", pos: { x: 0.21, y: 0.30, z: 0.33 } },
    { name: "BordismSemantics", kind: "structure", family: "TKFT", pos: { x: 0.16, y: 0.32, z: 0.36 } },
    { name: "DiscreteBordism.comp", kind: "theorem", family: "TKFT", pos: { x: 0.18, y: 0.34, z: 0.38 } },

    // Cantor Encoding
    { name: "encodeTape", kind: "def", family: "Billiards/Cantor", pos: { x: 0.45, y: 0.50, z: 0.40 } },
    { name: "encodeTape_injective", kind: "theorem", family: "Billiards/Cantor", pos: { x: 0.48, y: 0.52, z: 0.42 } },
    { name: "headInterval", kind: "def", family: "Billiards/Cantor", pos: { x: 0.43, y: 0.48, z: 0.38 } },
    { name: "τ", kind: "def", family: "Billiards/Cantor", pos: { x: 0.46, y: 0.54, z: 0.44 } },
    { name: "cantorNucleus", kind: "def", family: "Billiards/Cantor", pos: { x: 0.50, y: 0.56, z: 0.46 } },
    { name: "cantorNucleus_fixed_iff", kind: "theorem", family: "Billiards/Cantor", pos: { x: 0.52, y: 0.58, z: 0.48 } },
    { name: "CantorCylinder", kind: "def", family: "Billiards/Cantor", pos: { x: 0.47, y: 0.46, z: 0.36 } },
    { name: "CantorDigit", kind: "def", family: "Billiards/Cantor", pos: { x: 0.44, y: 0.44, z: 0.34 } },
    { name: "writeTape", kind: "def", family: "Billiards/Cantor", pos: { x: 0.49, y: 0.60, z: 0.50 } },
    { name: "writeTape_encode", kind: "theorem", family: "Billiards/Cantor", pos: { x: 0.51, y: 0.62, z: 0.52 } },

    // Billiards Geometry
    { name: "SpecularReflection", kind: "structure", family: "Billiards/Geometry", pos: { x: 0.70, y: 0.40, z: 0.55 } },
    { name: "reflectVelocity", kind: "def", family: "Billiards/Geometry", pos: { x: 0.72, y: 0.42, z: 0.57 } },
    { name: "UnitSquare", kind: "def", family: "Billiards/Geometry", pos: { x: 0.68, y: 0.38, z: 0.53 } },
    { name: "CollisionState", kind: "structure", family: "Billiards/Geometry", pos: { x: 0.74, y: 0.44, z: 0.59 } },
    { name: "next?", kind: "def", family: "Billiards/Geometry", pos: { x: 0.76, y: 0.46, z: 0.61 } },
    { name: "PaperMap", kind: "structure", family: "Billiards/Geometry", pos: { x: 0.78, y: 0.48, z: 0.63 } },
    { name: "PaperLink", kind: "structure", family: "Billiards/Geometry", pos: { x: 0.80, y: 0.50, z: 0.65 } },
    { name: "semiconj", kind: "theorem", family: "Billiards/Geometry", pos: { x: 0.82, y: 0.52, z: 0.67 } },
    { name: "ParabolicShiftCorridor", kind: "def", family: "Billiards/Geometry", pos: { x: 0.75, y: 0.54, z: 0.69 } },
    { name: "rwWall", kind: "def", family: "Billiards/Geometry", pos: { x: 0.77, y: 0.56, z: 0.71 } },

    // Computation
    { name: "DetSys", kind: "structure", family: "Computation", pos: { x: 0.30, y: 0.70, z: 0.25 } },
    { name: "HaltSys", kind: "structure", family: "Computation", pos: { x: 0.32, y: 0.72, z: 0.27 } },
    { name: "stepN", kind: "def", family: "Computation", pos: { x: 0.34, y: 0.74, z: 0.29 } },
    { name: "stepN_eq_iterate", kind: "theorem", family: "Computation", pos: { x: 0.36, y: 0.76, z: 0.31 } },
    { name: "haltsFrom", kind: "def", family: "Computation", pos: { x: 0.38, y: 0.78, z: 0.33 } },
    { name: "GenShiftCfg", kind: "structure", family: "Computation", pos: { x: 0.33, y: 0.68, z: 0.23 } },
    { name: "GenShiftCtrlCfg", kind: "structure", family: "Computation", pos: { x: 0.35, y: 0.66, z: 0.21 } },
    { name: "embedCfg", kind: "def", family: "Computation", pos: { x: 0.37, y: 0.80, z: 0.35 } },
    { name: "FlowRealization", kind: "structure", family: "Computation", pos: { x: 0.39, y: 0.82, z: 0.37 } },
    { name: "isPeriodicPt_enc", kind: "theorem", family: "Computation", pos: { x: 0.41, y: 0.84, z: 0.39 } },

    // Discrete
    { name: "reachesPeriod2_iff_halts", kind: "theorem", family: "Discrete", pos: { x: 0.55, y: 0.75, z: 0.60 } },
    { name: "FlowBridge", kind: "structure", family: "Discrete", pos: { x: 0.53, y: 0.73, z: 0.58 } },
    { name: "discreteFlow", kind: "def", family: "Discrete", pos: { x: 0.57, y: 0.77, z: 0.62 } },
    { name: "GeneralizedShiftBridge", kind: "structure", family: "Discrete", pos: { x: 0.59, y: 0.79, z: 0.64 } },
    { name: "halts_iff_reaches_period", kind: "theorem", family: "Discrete", pos: { x: 0.61, y: 0.81, z: 0.66 } },

    // FixedPoint
    { name: "unionNucleus", kind: "def", family: "FixedPoint", pos: { x: 0.25, y: 0.45, z: 0.50 } },
    { name: "isFixedPoint_unionNucleus_iff", kind: "theorem", family: "FixedPoint", pos: { x: 0.27, y: 0.47, z: 0.52 } },
    { name: "loopSet", kind: "def", family: "FixedPoint", pos: { x: 0.23, y: 0.43, z: 0.48 } },
    { name: "flowNucleusOsc", kind: "def", family: "FixedPoint", pos: { x: 0.29, y: 0.49, z: 0.54 } },

    // HeytingTuring
    { name: "predNucleus", kind: "def", family: "HeytingTuring", pos: { x: 0.40, y: 0.35, z: 0.70 } },
    { name: "predNucleus_fixed_iff", kind: "theorem", family: "HeytingTuring", pos: { x: 0.42, y: 0.37, z: 0.72 } },
    { name: "PredFrame", kind: "abbrev", family: "HeytingTuring", pos: { x: 0.38, y: 0.33, z: 0.68 } },
    { name: "period2Nucleus", kind: "def", family: "HeytingTuring", pos: { x: 0.44, y: 0.39, z: 0.74 } },
    { name: "not_computable_mem_reachesPeriod2Set", kind: "theorem", family: "HeytingTuring", pos: { x: 0.46, y: 0.41, z: 0.76 } },

    // Undecidability
    { name: "not_computable_of_reduces", kind: "theorem", family: "Undecidability", pos: { x: 0.60, y: 0.25, z: 0.45 } },
    { name: "not_computable_of_halting_reduces", kind: "theorem", family: "Undecidability", pos: { x: 0.62, y: 0.27, z: 0.47 } },
    { name: "Reduces", kind: "def", family: "Undecidability", pos: { x: 0.58, y: 0.23, z: 0.43 } },

    // External
    { name: "BilliardsComputesClaim", kind: "structure", family: "External", pos: { x: 0.85, y: 0.30, z: 0.20 } },
    { name: "EulerTuringCompleteClaim", kind: "structure", family: "External", pos: { x: 0.87, y: 0.32, z: 0.22 } },
    { name: "NavierStokesTuringCompleteClaim", kind: "structure", family: "External", pos: { x: 0.89, y: 0.34, z: 0.24 } },
    { name: "not_computable_of_billiardsComputes", kind: "theorem", family: "External", pos: { x: 0.86, y: 0.36, z: 0.26 } },

    // Fluids
    { name: "ContactLinear", kind: "structure", family: "Fluids", pos: { x: 0.12, y: 0.60, z: 0.75 } },
    { name: "ContactLinearFlow", kind: "structure", family: "Fluids", pos: { x: 0.14, y: 0.62, z: 0.77 } },
    { name: "curl3", kind: "def", family: "Fluids", pos: { x: 0.10, y: 0.58, z: 0.73 } },
    { name: "gradDiv3", kind: "def", family: "Fluids", pos: { x: 0.16, y: 0.64, z: 0.79 } },

    // Geometry
    { name: "DifferentialForm", kind: "structure", family: "Geometry", pos: { x: 0.08, y: 0.85, z: 0.15 } },
    { name: "ContactEuclidean", kind: "structure", family: "Geometry", pos: { x: 0.10, y: 0.87, z: 0.17 } }
  ],
  edges: [
    // TKFT internal
    [0, 1], [0, 2], [0, 3], [0, 4], [5, 7], [6, 7], [8, 9],
    // Cantor encoding chain
    [10, 11], [12, 10], [13, 10], [14, 15], [16, 17], [18, 19],
    // Geometry
    [20, 21], [22, 23], [23, 24], [25, 26], [26, 27], [28, 29],
    // Computation
    [30, 31], [31, 32], [32, 33], [31, 34], [35, 36], [37, 38], [38, 39],
    // Discrete bridge
    [40, 34], [41, 42], [43, 44], [40, 44],
    // FixedPoint
    [45, 46], [47, 48], [45, 48],
    // HeytingTuring
    [49, 50], [51, 52], [52, 53],
    // Undecidability
    [54, 55], [56, 54],
    // External
    [57, 60], [58, 60], [59, 60],
    // Cross-module dependencies
    [40, 53], [44, 46], [11, 27], [5, 42], [31, 41]
  ]
};

// Export for use in viewers
if (typeof module !== 'undefined') {
  module.exports = mirandaProofsData;
}
