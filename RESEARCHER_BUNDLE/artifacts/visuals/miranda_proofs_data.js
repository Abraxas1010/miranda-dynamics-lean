// Miranda Dynamics UMAP Proof Data
// Generated from HeytingLean.MirandaDynamics (142 Lean files, 1541 declarations)

const mirandaProofsData = {
  metadata: {
    project: "Miranda Dynamics",
    description: "Computational universality in dynamical systems + Wolfram Physics bridge",
    leanFiles: 142,
    totalDeclarations: 1541,
    sorryCount: 0,
    generated: "2026-01-21"
  },
  families: {
    "Billiards/Cantor": {
        "color": "#10b981",
        "count": 114
    },
    "Billiards/Geometry": {
        "color": "#22d3d3",
        "count": 723
    },
    "CLI": {
        "color": "#78716c",
        "count": 6
    },
    "Computation": {
        "color": "#f59e0b",
        "count": 66
    },
    "Discrete": {
        "color": "#ef4444",
        "count": 35
    },
    "External": {
        "color": "#6366f1",
        "count": 16
    },
    "FixedPoint": {
        "color": "#8b5cf6",
        "count": 5
    },
    "Fluids": {
        "color": "#14b8a6",
        "count": 34
    },
    "Geometry": {
        "color": "#a855f7",
        "count": 9
    },
    "Other": {
        "color": "#9ca3af",
        "count": 35
    },
    "Seismic": {
        "color": "#06b6d4",
        "count": 59
    },
    "TKFT": {
        "color": "#3b82f6",
        "count": 54
    },
    "Undecidability": {
        "color": "#f97316",
        "count": 6
    },
    "Wolfram": {
        "color": "#84cc16",
        "count": 130
    },
    "Wolfram/Branchial": {
        "color": "#16a34a",
        "count": 7
    },
    "Wolfram/Causal": {
        "color": "#15803d",
        "count": 143
    },
    "Wolfram/Multiway": {
        "color": "#22c55e",
        "count": 70
    },
    "Wolfram/WM148": {
        "color": "#166534",
        "count": 29
    }
},
  items: [
    {
        "name": "HeytingLean.MirandaDynamics.Billiard.Position",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.04859193041920662,
            "y": 0.9331041574478149,
            "z": 0.775233805179596
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiard.Velocity",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.03754110634326935,
            "y": 0.9554012417793274,
            "z": 0.8357599973678589
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiard.Ball",
        "kind": "structure",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.011946522630751133,
            "y": 0.9688762426376343,
            "z": 0.9764425158500671
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiard.Table",
        "kind": "structure",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.04191935807466507,
            "y": 0.9472534656524658,
            "z": 0.7848564982414246
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiard.BilliardState",
        "kind": "structure",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.024144480004906654,
            "y": 0.9601075053215027,
            "z": 0.9419865608215332
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiard.Observation",
        "kind": "structure",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.021022651344537735,
            "y": 0.962689220905304,
            "z": 0.9591766595840454
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiard.CalibrationRun",
        "kind": "structure",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.23340177536010742,
            "y": 0.545013964176178,
            "z": 0.4481702744960785
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiard.rmsError",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.02763557806611061,
            "y": 0.9736095666885376,
            "z": 0.8770774006843567
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiard.calibrationError",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.2874493896961212,
            "y": 0.426445871591568,
            "z": 0.37504681944847107
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiard.calibrationObjective",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.0889521911740303,
            "y": 0.8487001657485962,
            "z": 0.7481701374053955
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiard.collide",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.16416238248348236,
            "y": 0.6735360026359558,
            "z": 0.48244017362594604
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiard.reflectWalls",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.47836658358573914,
            "y": 0.07746332138776779,
            "z": 0.15716798603534698
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiard.advanceBall",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.37295299768447876,
            "y": 0.21994173526763916,
            "z": 0.26399046182632446
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiard.evolveSteps",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.4700288772583008,
            "y": 0.08838165551424026,
            "z": 0.14264483749866486
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiard.evolve",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.3322031497955322,
            "y": 0.3105039894580841,
            "z": 0.2453213483095169
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiard.ObservationParams",
        "kind": "structure",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.0818566381931305,
            "y": 0.8599892258644104,
            "z": 0.7274705171585083
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiard.roundTo",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.5460754036903381,
            "y": 0.08028990030288696,
            "z": 0.048973143100738525
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiard.observe",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.5400675535202026,
            "y": 0.08203770220279694,
            "z": 0.04203486815094948
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiard.reaches",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.6714377403259277,
            "y": 0.06257545202970505,
            "z": 0.10175694525241852
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiard.observableReaches",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.22989869117736816,
            "y": 0.558682382106781,
            "z": 0.48311296105384827
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.CantorBlockExplicit",
        "kind": "def",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.596633791923523,
            "y": 0.07592346519231796,
            "z": 0.19372165203094482
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.CantorBlockExplicit_subset_CantorBlock",
        "kind": "theorem",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.7007339000701904,
            "y": 0.07387381047010422,
            "z": 0.394072949886322
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.paperFgen",
        "kind": "theorem",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.8964200615882874,
            "y": 0.04509945213794708,
            "z": 0.3304714858531952
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.CantorBlock",
        "kind": "def",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.344034880399704,
            "y": 0.29484090209007263,
            "z": 0.3174886405467987
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.tauAffine",
        "kind": "def",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.5535990595817566,
            "y": 0.07701308280229568,
            "z": 0.05995811149477959
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.tauAffine_apply",
        "kind": "theorem",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.16293157637119293,
            "y": 0.7063670754432678,
            "z": 0.5977364182472229
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.paperFgenAffine",
        "kind": "def",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.25812944769859314,
            "y": 0.4924612045288086,
            "z": 0.42889565229415894
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.paperFgenAffine_apply",
        "kind": "theorem",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.3992115557193756,
            "y": 0.21449479460716248,
            "z": 0.3940010964870453
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.paperFgen",
        "kind": "theorem",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.6568058133125305,
            "y": 0.06437897682189941,
            "z": 0.10967879742383957
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.cantorWidth",
        "kind": "def",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.17158693075180054,
            "y": 0.6825385689735413,
            "z": 0.5686758160591125
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.cantorWidth_nil",
        "kind": "theorem",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.5395994186401367,
            "y": 0.06830016523599625,
            "z": 0.16516125202178955
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.cantorWidth_cons",
        "kind": "theorem",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.9030666947364807,
            "y": 0.042006220668554306,
            "z": 0.3546599745750427
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.cantorLeft",
        "kind": "def",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.31938278675079346,
            "y": 0.3463265299797058,
            "z": 0.30947959423065186
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.cantorLeft_nil",
        "kind": "theorem",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.7426115274429321,
            "y": 0.05501171573996544,
            "z": 0.15554949641227722
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.cantorLeft_cons",
        "kind": "theorem",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.4933702349662781,
            "y": 0.07461697608232498,
            "z": 0.18066662549972534
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.cantorLeft_nonneg",
        "kind": "theorem",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.0962417721748352,
            "y": 0.8343561887741089,
            "z": 0.7143219113349915
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.cantorLeft_add_width_le_one",
        "kind": "theorem",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.3065190613269806,
            "y": 0.4567873477935791,
            "z": 0.5838090777397156
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.cantorLeft_le_one",
        "kind": "theorem",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.5463788509368896,
            "y": 0.07028008997440338,
            "z": 0.19844798743724823
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.cantorWidth_le_one",
        "kind": "theorem",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.8527801632881165,
            "y": 0.06085565686225891,
            "z": 0.2834506332874298
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.abs_cantorLeft_sub_le_one_sub_width",
        "kind": "theorem",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.8195344805717468,
            "y": 0.0614020973443985,
            "z": 0.4330909550189972
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.cantorLeft_separated_of_length_eq",
        "kind": "theorem",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.710716724395752,
            "y": 0.0683431401848793,
            "z": 0.35873493552207947
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.cantorLeft_append_singleton",
        "kind": "theorem",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.5315837264060974,
            "y": 0.1401481181383133,
            "z": 0.45158544182777405
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.cantorLeft_sub_append_singleton",
        "kind": "theorem",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.9919598698616028,
            "y": 0.009528500027954578,
            "z": 0.8052381873130798
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.cantorLeft_separated_append_singleton_of_length_eq",
        "kind": "theorem",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.9503532648086548,
            "y": 0.015204106457531452,
            "z": 0.7369255423545837
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.cantorCylinderInterval",
        "kind": "def",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.5870863795280457,
            "y": 0.07595674693584442,
            "z": 0.20388755202293396
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.cantorCylinderInterval_subset_Icc",
        "kind": "theorem",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.5443481206893921,
            "y": 0.14283935725688934,
            "z": 0.4761197865009308
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.mem_cantorCylinder_iff_mem_interval",
        "kind": "theorem",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.299109548330307,
            "y": 0.4910372197628021,
            "z": 0.6308903098106384
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.cantorCylinder_eq_interval",
        "kind": "theorem",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.6329840421676636,
            "y": 0.07883051782846451,
            "z": 0.25466057658195496
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.cantorCylinderInterval_disjoint_of_length_eq",
        "kind": "theorem",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.9771206378936768,
            "y": 0.01485314592719078,
            "z": 0.7802238464355469
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.cantorHeadInterval",
        "kind": "def",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.4986089766025543,
            "y": 0.07779308408498764,
            "z": 0.20836156606674194
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.cantorTailAffine",
        "kind": "def",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.46419137716293335,
            "y": 0.10581018030643463,
            "z": 0.25623616576194763
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.cantorCylinder",
        "kind": "def",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.7561109662055969,
            "y": 0.053555309772491455,
            "z": 0.15602055191993713
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.cantorHeadInterval_disjoint",
        "kind": "theorem",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.6712026000022888,
            "y": 0.07242392748594284,
            "z": 0.292592316865921
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.cantorCylinder_eq_of_mem_of_length_eq",
        "kind": "theorem",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.3746698796749115,
            "y": 0.36609330773353577,
            "z": 0.6127470135688782
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.cantorCylinder_disjoint_of_length_eq",
        "kind": "theorem",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.7523865103721619,
            "y": 0.06315651535987854,
            "z": 0.4093227982521057
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.cantorHeadDigit",
        "kind": "theorem",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.5404322147369385,
            "y": 0.06839464604854584,
            "z": 0.16718706488609314
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.cantorTail",
        "kind": "theorem",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.9766624569892883,
            "y": 0.016909129917621613,
            "z": 0.6605292558670044
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.cantorDigitAt",
        "kind": "theorem",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.4523061215877533,
            "y": 0.1085016131401062,
            "z": 0.2320156991481781
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.getOpt_append_length_singleton",
        "kind": "theorem",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.29041552543640137,
            "y": 0.4976848363876343,
            "z": 0.6184681057929993
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.cantorDigitBlock",
        "kind": "def",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.8536494970321655,
            "y": 0.057524263858795166,
            "z": 0.27850988507270813
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.cantorDigitAt",
        "kind": "theorem",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.6502577066421509,
            "y": 0.06573313474655151,
            "z": 0.1493891030550003
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.oneThird",
        "kind": "def",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.38215142488479614,
            "y": 0.19539137184619904,
            "z": 0.22830504179000854
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.twoThird",
        "kind": "def",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.1741853654384613,
            "y": 0.6673351526260376,
            "z": 0.5232250094413757
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.cantorHeadDigit",
        "kind": "def",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.07473061233758926,
            "y": 0.8761746883392334,
            "z": 0.7593979239463806
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.cantorTail",
        "kind": "def",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.1147083193063736,
            "y": 0.7938198447227478,
            "z": 0.6342581510543823
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.cantorHeadDigit",
        "kind": "theorem",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.7581813931465149,
            "y": 0.054251380264759064,
            "z": 0.17394357919692993
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.cantorTail",
        "kind": "theorem",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.7594369649887085,
            "y": 0.05357574298977852,
            "z": 0.14115099608898163
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.cantorDigitAt",
        "kind": "def",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.22355227172374725,
            "y": 0.5673521161079407,
            "z": 0.47313448786735535
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.cantorDigitAt",
        "kind": "theorem",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.4067097008228302,
            "y": 0.15634793043136597,
            "z": 0.2656835615634918
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.cantorDigitAt",
        "kind": "theorem",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.810234010219574,
            "y": 0.05500701814889908,
            "z": 0.18957580626010895
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.cantorDigitAt",
        "kind": "theorem",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.4392422139644623,
            "y": 0.11561482399702072,
            "z": 0.218583345413208
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.Tape",
        "kind": "def",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.03558176010847092,
            "y": 0.9609251022338867,
            "z": 0.7968168258666992
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.tapeIndex",
        "kind": "def",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.3015861511230469,
            "y": 0.384390652179718,
            "z": 0.3130691647529602
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.indexNat",
        "kind": "def",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.10424121469259262,
            "y": 0.811047375202179,
            "z": 0.6345311999320984
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.tapeIndex_indexNat",
        "kind": "theorem",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.39464443922042847,
            "y": 0.19807493686676025,
            "z": 0.34118714928627014
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.digits",
        "kind": "def",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.07954202592372894,
            "y": 0.859896183013916,
            "z": 0.6661641001701355
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.digits_injective",
        "kind": "theorem",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.17347486317157745,
            "y": 0.6840437054634094,
            "z": 0.5932667255401611
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.cantorEncode",
        "kind": "def",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.6100806593894958,
            "y": 0.0702539011836052,
            "z": 0.13072197139263153
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.cantorEncode_injective",
        "kind": "theorem",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.9250501990318298,
            "y": 0.025432227179408073,
            "z": 0.4647659659385681
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.encodeTape",
        "kind": "def",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.17223414778709412,
            "y": 0.6796227097511292,
            "z": 0.5587925910949707
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.encodeTape_injective",
        "kind": "theorem",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.1292600780725479,
            "y": 0.7794562578201294,
            "z": 0.7040486335754395
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.cantorEncode_le_one",
        "kind": "theorem",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.7567287683486938,
            "y": 0.055690426379442215,
            "z": 0.20680862665176392
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.cantorEncode_nonneg",
        "kind": "theorem",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.9524691104888916,
            "y": 0.01981915719807148,
            "z": 0.528028130531311
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.cantorEncode_mem_Icc",
        "kind": "theorem",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.45214518904685974,
            "y": 0.15855076909065247,
            "z": 0.39639970660209656
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.encodeTape_mem_Icc",
        "kind": "theorem",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.3851035535335541,
            "y": 0.22803905606269836,
            "z": 0.3717242479324341
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.cantorEncode_succ",
        "kind": "theorem",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.5461208820343018,
            "y": 0.06839992105960846,
            "z": 0.19512119889259338
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.cantorEncode_mem_preCantorSet",
        "kind": "theorem",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.8579834699630737,
            "y": 0.05605069175362587,
            "z": 0.42458224296569824
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.cantorEncode_mem_cantorSet",
        "kind": "theorem",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.45051276683807373,
            "y": 0.18402232229709625,
            "z": 0.44960036873817444
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.encodeTape_mem_cantorSet",
        "kind": "theorem",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.4267767071723938,
            "y": 0.19986283779144287,
            "z": 0.43771880865097046
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.headScale",
        "kind": "def",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.289558470249176,
            "y": 0.40875858068466187,
            "z": 0.3225344717502594
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.headScale_pos",
        "kind": "theorem",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.3984862267971039,
            "y": 0.17048649489879608,
            "z": 0.2747146487236023
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.tau",
        "kind": "def",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.02980722486972809,
            "y": 0.9687657356262207,
            "z": 0.8619479537010193
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.headLeft",
        "kind": "def",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.4599176347255707,
            "y": 0.10625580698251724,
            "z": 0.10537321120500565
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.headRight",
        "kind": "def",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.43482866883277893,
            "y": 0.12280726432800293,
            "z": 0.17310020327568054
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.headInterval",
        "kind": "def",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.2529316544532776,
            "y": 0.4943486750125885,
            "z": 0.39975154399871826
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.headScale_le_one_third",
        "kind": "theorem",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.9343750476837158,
            "y": 0.022675665095448494,
            "z": 0.49739155173301697
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.headLeft_nonneg",
        "kind": "theorem",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.703852653503418,
            "y": 0.05980191379785538,
            "z": 0.15857979655265808
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.headRight_le_one",
        "kind": "theorem",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.7773712873458862,
            "y": 0.056548114866018295,
            "z": 0.22816364467144012
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.headInterval_subset_Icc",
        "kind": "theorem",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.3048824667930603,
            "y": 0.45397064089775085,
            "z": 0.5711111426353455
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.tau_mem_headInterval",
        "kind": "theorem",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.642998456954956,
            "y": 0.07029207795858383,
            "z": 0.2014026939868927
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.negSucc_lt_negSucc_iff",
        "kind": "theorem",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.6718438863754272,
            "y": 0.06925109028816223,
            "z": 0.25669315457344055
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.pow3_gt_two",
        "kind": "lemma",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.5483798980712891,
            "y": 0.06937434524297714,
            "z": 0.08002285659313202
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.pow_mul_inv_pow_add",
        "kind": "lemma",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.6438280344009399,
            "y": 0.06877486407756805,
            "z": 0.19172024726867676
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.two_mul_inv_pow_lt_inv_pow_of_lt_add",
        "kind": "lemma",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.7840328216552734,
            "y": 0.061921872198581696,
            "z": 0.45525750517845154
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.headInterval_length",
        "kind": "theorem",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.6027603149414062,
            "y": 0.07560694217681885,
            "z": 0.1901882439851761
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.headRight_lt_headLeft_of_lt",
        "kind": "theorem",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.31047865748405457,
            "y": 0.4533151388168335,
            "z": 0.5879320502281189
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.disjoint_Icc_of_lt",
        "kind": "theorem",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.36925452947616577,
            "y": 0.2603153586387634,
            "z": 0.37668800354003906
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.headInterval_disjoint",
        "kind": "theorem",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.8375906944274902,
            "y": 0.06536827236413956,
            "z": 0.28747043013572693
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.headInterval_lt_of_lt",
        "kind": "theorem",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.8421785831451416,
            "y": 0.0652187317609787,
            "z": 0.29868587851524353
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.headScale_neg",
        "kind": "theorem",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.47981011867523193,
            "y": 0.0804516151547432,
            "z": 0.19517232477664948
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.headLeft_neg",
        "kind": "theorem",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.4000012278556824,
            "y": 0.16552087664604187,
            "z": 0.26337486505508423
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.headRight_neg",
        "kind": "theorem",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.4021022617816925,
            "y": 0.16412930190563202,
            "z": 0.2718012034893036
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.headInterval_reflect",
        "kind": "theorem",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.2893126308917999,
            "y": 0.4734707772731781,
            "z": 0.552983820438385
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.tau_shift_law",
        "kind": "theorem",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.2825792729854584,
            "y": 0.4343318045139313,
            "z": 0.3669751286506653
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.headShift",
        "kind": "def",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.29110851883888245,
            "y": 0.4062342345714569,
            "z": 0.3328417241573334
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.headShift_tau",
        "kind": "theorem",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.6975805759429932,
            "y": 0.05864755064249039,
            "z": 0.15435738861560822
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.tau_surj_headInterval",
        "kind": "theorem",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.7676753401756287,
            "y": 0.05699336528778076,
            "z": 0.2564633786678314
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.headShift_mem_headInterval_succ",
        "kind": "theorem",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.7541570663452148,
            "y": 0.06195371598005295,
            "z": 0.38710352778434753
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.tau_injective",
        "kind": "theorem",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.41472214460372925,
            "y": 0.14648669958114624,
            "z": 0.25902101397514343
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.encodeWithHead",
        "kind": "def",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.4743083119392395,
            "y": 0.08976507186889648,
            "z": 0.21546798944473267
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.encodeWithHead_shift",
        "kind": "theorem",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.8542138934135437,
            "y": 0.06009426712989807,
            "z": 0.30531904101371765
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.encodeWithHead_injective_tape",
        "kind": "theorem",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.5986925959587097,
            "y": 0.11259286105632782,
            "z": 0.4202493131160736
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.encodeWithHead_injective_pair",
        "kind": "theorem",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.31237882375717163,
            "y": 0.45630621910095215,
            "z": 0.5975285172462463
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.cantorCompl",
        "kind": "def",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.24955572187900543,
            "y": 0.5001152157783508,
            "z": 0.3960578441619873
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.cantorNucleus",
        "kind": "def",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.40559694170951843,
            "y": 0.1586313396692276,
            "z": 0.26144692301750183
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.cantorNucleus_fixed_iff",
        "kind": "theorem",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.42741045355796814,
            "y": 0.19652147591114044,
            "z": 0.43771225214004517
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.indexNat_tapeIndex",
        "kind": "theorem",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.6096782088279724,
            "y": 0.07516715675592422,
            "z": 0.17911198735237122
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.tapeIndex_injective",
        "kind": "theorem",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.21115396916866302,
            "y": 0.618411123752594,
            "z": 0.5812667608261108
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.Tape",
        "kind": "def",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.3891097903251648,
            "y": 0.1833927184343338,
            "z": 0.1784987449645996
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.digits_write",
        "kind": "theorem",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.24316184222698212,
            "y": 0.5169843435287476,
            "z": 0.42581096291542053
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.cantorFunction_update_one",
        "kind": "theorem",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.8296657204627991,
            "y": 0.06608515232801437,
            "z": 0.3025537431240082
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.cantorEncode_updateDigit",
        "kind": "theorem",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.6807819604873657,
            "y": 0.06788647919893265,
            "z": 0.2632722854614258
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.encodeTape_write",
        "kind": "theorem",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.4973272979259491,
            "y": 0.0768153965473175,
            "z": 0.19786490499973297
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.encodeTape_write_eq_add_pow",
        "kind": "theorem",
        "family": "Billiards/Cantor",
        "pos": {
            "x": 0.5925562977790833,
            "y": 0.1097145825624466,
            "z": 0.392263799905777
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.Demo.showList",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.11280940473079681,
            "y": 0.8015055060386658,
            "z": 0.6561852693557739
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.Demo.sampleTape",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.2648524045944214,
            "y": 0.47636479139328003,
            "z": 0.4138641655445099
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.Demo.main",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.4890042245388031,
            "y": 0.07586601376533508,
            "z": 0.11657983809709549
        }
    },
    {
        "name": "main",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.0006937136058695614,
            "y": 0.9866642355918884,
            "z": 0.982033371925354
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.FloatSim.Vec2",
        "kind": "structure",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.04998292401432991,
            "y": 0.9279537796974182,
            "z": 0.8358142971992493
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.FloatSim.Vec2",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.30370062589645386,
            "y": 0.3828156888484955,
            "z": 0.33542153239250183
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.FloatSim.Vec2",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.20373716950416565,
            "y": 0.6168144345283508,
            "z": 0.5214046239852905
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.FloatSim.clamp01",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.169166699051857,
            "y": 0.6997073292732239,
            "z": 0.6005821228027344
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.FloatSim.inRect",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.04184618964791298,
            "y": 0.9386951923370361,
            "z": 0.8685426712036133
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.FloatSim.inf",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.023206088691949844,
            "y": 0.9540023803710938,
            "z": 0.9650163650512695
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.FloatSim.nextTime1D",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.04739184305071831,
            "y": 0.9324339032173157,
            "z": 0.8605932593345642
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.FloatSim.abs",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.23402374982833862,
            "y": 0.5388028025627136,
            "z": 0.43925899267196655
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.FloatSim.reflectX",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.7117899656295776,
            "y": 0.0584770105779171,
            "z": 0.1720634251832962
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.FloatSim.reflectY",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.632523775100708,
            "y": 0.0699126273393631,
            "z": 0.16584385931491852
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.FloatSim.reflectXY",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.6894577741622925,
            "y": 0.06287691742181778,
            "z": 0.19576817750930786
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.FloatSim.stepRect",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.5485749840736389,
            "y": 0.07045590132474899,
            "z": 0.19602413475513458
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.GenShiftCtrlMap.next",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.8460062146186829,
            "y": 0.059717122465372086,
            "z": 0.28746798634529114
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.GenShiftCtrlMap.next",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.849120020866394,
            "y": 0.06288161873817444,
            "z": 0.29900646209716797
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.GenShiftCtrlMap.encodeCfgCtrl_mem_CtrlDomain",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.4622637927532196,
            "y": 0.2629881799221039,
            "z": 0.6138805150985718
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.GenShiftCtrlMap.semiconj",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.8884119391441345,
            "y": 0.048806071281433105,
            "z": 0.4195650517940521
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.GenShiftCtrlMap.PaperLink",
        "kind": "structure",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.7617447972297668,
            "y": 0.05763351544737816,
            "z": 0.2754272520542145
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.GenShiftCtrlMap.paperLink",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.5493566989898682,
            "y": 0.07469342648983002,
            "z": 0.220839723944664
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.GenShiftCtrlMap.semiconj_iter",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.9712982177734375,
            "y": 0.015270481817424297,
            "z": 0.6912106275558472
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.GenShiftCtrlMap.ReturnRel_encode",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.3551396131515503,
            "y": 0.3767590820789337,
            "z": 0.5814469456672668
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.Table",
        "kind": "structure",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.49848926067352295,
            "y": 0.08102261275053024,
            "z": 0.07385105639696121
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.State",
        "kind": "structure",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.01410255953669548,
            "y": 0.9529628157615662,
            "z": 0.9930281043052673
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.Table.Flight",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.5691803097724915,
            "y": 0.07278045266866684,
            "z": 0.08315206319093704
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.Table.Step",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.5021412372589111,
            "y": 0.06974726915359497,
            "z": 0.12636731564998627
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.Table.Reaches",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.2963137924671173,
            "y": 0.39936962723731995,
            "z": 0.34407272934913635
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.Table.reachingRel",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.01981245167553425,
            "y": 0.9440918564796448,
            "z": 0.9830923080444336
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.Table.Step",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.4973304569721222,
            "y": 0.07122573256492615,
            "z": 0.13545341789722443
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.Table.Reaches",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.4411334693431854,
            "y": 0.11897038668394089,
            "z": 0.23409369587898254
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.Table.Reaches",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.3991440534591675,
            "y": 0.16988471150398254,
            "z": 0.27913931012153625
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.Table.Step",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.030126728117465973,
            "y": 0.9612159132957458,
            "z": 0.8978108763694763
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.GeometryDemo.showState",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.20106273889541626,
            "y": 0.6432188749313354,
            "z": 0.6081109642982483
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.GeometryDemo.loop",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.20418529212474823,
            "y": 0.6254425644874573,
            "z": 0.5682156085968018
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.GeometryDemo.main",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.357648104429245,
            "y": 0.287706196308136,
            "z": 0.3875112235546112
        }
    },
    {
        "name": "main",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.001851409673690796,
            "y": 0.9876593351364136,
            "z": 0.9743085503578186
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.Table.DeterministicNext.hitPoint",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.46044158935546875,
            "y": 0.21453623473644257,
            "z": 0.5320598483085632
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.Table.DeterministicNext.IsHitTime",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.455270916223526,
            "y": 0.22967290878295898,
            "z": 0.5516577959060669
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.Table.DeterministicNext.IsFirstHitTime",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.4866635799407959,
            "y": 0.20978085696697235,
            "z": 0.5583154559135437
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.Table.DeterministicNext.Good",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.3620654344558716,
            "y": 0.34009671211242676,
            "z": 0.5324001312255859
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.Table.DeterministicNext.next",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.6823338866233826,
            "y": 0.0703854039311409,
            "z": 0.30200257897377014
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.Table.DeterministicNext.next",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.8811396956443787,
            "y": 0.05134720355272293,
            "z": 0.42955249547958374
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.Table.DeterministicNext.Step_of_next",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.5704373717308044,
            "y": 0.13614146411418915,
            "z": 0.48625949025154114
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.GeometryToGenShiftCtrl.Link",
        "kind": "structure",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.917179524898529,
            "y": 0.024813368916511536,
            "z": 0.48422476649284363
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.GeometryToGenShiftCtrl.Link.encode",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.7579243779182434,
            "y": 0.0619957260787487,
            "z": 0.4145367741584778
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.GeometryToGenShiftCtrl.Link.encode_mem",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.9173558354377747,
            "y": 0.010057482868432999,
            "z": 0.6253990530967712
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.GeometryToGenShiftCtrl.Link.semiconj",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.9104580283164978,
            "y": 0.015614823438227177,
            "z": 0.5934512615203857
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.GeometryToGenShiftCtrl.Link.paperLink",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.6538729071617126,
            "y": 0.09657882899045944,
            "z": 0.4533780813217163
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.UnitSquareMap.PaperLink",
        "kind": "structure",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.9785289168357849,
            "y": 0.015165547840297222,
            "z": 0.7044113278388977
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.UnitSquareMap.nextIter",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.8807052969932556,
            "y": 0.052215829491615295,
            "z": 0.3898114264011383
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.UnitSquareMap.nextIter",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.6028093099594116,
            "y": 0.07811239361763,
            "z": 0.19681860506534576
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.UnitSquareMap.PaperLink",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.88497394323349,
            "y": 0.0466165728867054,
            "z": 0.40217503905296326
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.headStateLeft",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.8242916464805603,
            "y": 0.05742479860782623,
            "z": 0.21692118048667908
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.headStateRight",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.913733959197998,
            "y": 0.03760746493935585,
            "z": 0.36839139461517334
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.headStateInterval",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.8308424353599548,
            "y": 0.0616096630692482,
            "z": 0.2502136826515198
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.headStateInterval_subset_headInterval",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.6416675448417664,
            "y": 0.1017201766371727,
            "z": 0.45572543144226074
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.inset",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.3406433165073395,
            "y": 0.29001033306121826,
            "z": 0.25405335426330566
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.inset_pos",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.7517821192741394,
            "y": 0.053025178611278534,
            "z": 0.14226849377155304
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.inset_lt_one",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.7566260695457458,
            "y": 0.05285732075572014,
            "z": 0.150010347366333
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.tauState",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.9129492044448853,
            "y": 0.03891107067465782,
            "z": 0.35640841722488403
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.tauState_mem_headStateInterval",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.9363803863525391,
            "y": 0.017343729734420776,
            "z": 0.5524941682815552
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.encodeWithHeadState",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.8983486294746399,
            "y": 0.04489936679601669,
            "z": 0.39487236738204956
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.encodeWithHeadState_mem_headStateInterval",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.886755108833313,
            "y": 0.02767198719084263,
            "z": 0.585868239402771
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.headIndexState",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.9635781645774841,
            "y": 0.017752720043063164,
            "z": 0.5623928308486938
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.headStateInterval_disjoint_of_ne",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.5492582321166992,
            "y": 0.14101040363311768,
            "z": 0.4764343500137329
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.headIndexState",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.9531495571136475,
            "y": 0.020767105743288994,
            "z": 0.5073535442352295
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.headIndexState",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.9677116274833679,
            "y": 0.016936657950282097,
            "z": 0.5818150043487549
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.Line",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.29698529839515686,
            "y": 0.3887045979499817,
            "z": 0.26324811577796936
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.mem_Line_iff",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.6936920285224915,
            "y": 0.059236958622932434,
            "z": 0.14469124376773834
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.inner_add_smul",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.6997178792953491,
            "y": 0.05940663814544678,
            "z": 0.16704566776752472
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.timeToLine",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.45768025517463684,
            "y": 0.09709639847278595,
            "z": 0.15364369750022888
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.timeToLine",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.19034738838672638,
            "y": 0.6365538239479065,
            "z": 0.5121612548828125
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.timeToLine",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.35392260551452637,
            "y": 0.26449695229530334,
            "z": 0.28059762716293335
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.mem_Line_of_timeToLine",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.9512487053871155,
            "y": 0.018930966034531593,
            "z": 0.5329439640045166
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperBilliardMap.CollisionState",
        "kind": "structure",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.480584979057312,
            "y": 0.18334859609603882,
            "z": 0.4998800456523895
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperBilliardMap.Good",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.639509916305542,
            "y": 0.07252895832061768,
            "z": 0.21051070094108582
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperBilliardMap.next",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.2912110984325409,
            "y": 0.4754742980003357,
            "z": 0.5687471032142639
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperBilliardMap.encode",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.8291463255882263,
            "y": 0.06582214683294296,
            "z": 0.29633617401123047
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperBilliardMap.encode_def",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.9213981032371521,
            "y": 0.022964471951127052,
            "z": 0.4852420687675476
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperBilliardMap.semiconj",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.8304697275161743,
            "y": 0.06561736762523651,
            "z": 0.3096579909324646
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperBilliardMap.PaperLink",
        "kind": "structure",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.8432083129882812,
            "y": 0.06318912655115128,
            "z": 0.35846370458602905
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperBilliardMap.paperLink",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.3267503082752228,
            "y": 0.4201001822948456,
            "z": 0.5779678821563721
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperBilliardMap.semiconj_iter",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.8286660313606262,
            "y": 0.06475449353456497,
            "z": 0.3712974190711975
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperBilliardMap.paperLinkGeneric",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.18156245350837708,
            "y": 0.6997998356819153,
            "z": 0.729383111000061
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperLink",
        "kind": "structure",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.7815861105918884,
            "y": 0.05239730328321457,
            "z": 0.1502440720796585
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperLink.good_of_iter",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.6147227883338928,
            "y": 0.07607366889715195,
            "z": 0.20638850331306458
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperLink.semiconj_iter",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.7423678636550903,
            "y": 0.05817362293601036,
            "z": 0.23549139499664307
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.headIndex",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.5019163489341736,
            "y": 0.07308921217918396,
            "z": 0.10458116978406906
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.headIndex",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.6701182126998901,
            "y": 0.0622987300157547,
            "z": 0.10724063217639923
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.headStep",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.2651360332965851,
            "y": 0.4585742652416229,
            "z": 0.3440999686717987
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.headStep",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.7936951518058777,
            "y": 0.05373659357428551,
            "z": 0.15903626382350922
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.headStep",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.9568875432014465,
            "y": 0.02269130013883114,
            "z": 0.5228598117828369
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.paperF",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.09268385916948318,
            "y": 0.8288635611534119,
            "z": 0.6314579844474792
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.paperF",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.6595789194107056,
            "y": 0.06410273909568787,
            "z": 0.09967909753322601
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.paperF",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.9765964150428772,
            "y": 0.0162526722997427,
            "z": 0.6536991596221924
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.paperF",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.7865036725997925,
            "y": 0.05412688106298447,
            "z": 0.14484503865242004
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.writeDelta",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.784531831741333,
            "y": 0.051719456911087036,
            "z": 0.15580931305885315
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.paperWriteF",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.23440507054328918,
            "y": 0.5373507738113403,
            "z": 0.42829611897468567
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.paperWriteF",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.9723809957504272,
            "y": 0.019335735589265823,
            "z": 0.6151400208473206
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.toGenShiftCtrlCfg",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.27317944169044495,
            "y": 0.48582834005355835,
            "z": 0.499441921710968
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.tapeUpdate_eq_write",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.3091866374015808,
            "y": 0.41390547156333923,
            "z": 0.47468093037605286
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.encodeCfgCtrl",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.7302155494689941,
            "y": 0.05561119690537453,
            "z": 0.15544945001602173
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.paperFctrl",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.2727597951889038,
            "y": 0.4475501477718353,
            "z": 0.3477533161640167
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.paperFctrl",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.9727191925048828,
            "y": 0.010808706283569336,
            "z": 0.599330723285675
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.insetAffine",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.48929363489151,
            "y": 0.07324210554361343,
            "z": 0.14321595430374146
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.insetAffine_apply",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.45318326354026794,
            "y": 0.11914361268281937,
            "z": 0.28482216596603394
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.tauStateAffine",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.9523099660873413,
            "y": 0.020453648641705513,
            "z": 0.5100890398025513
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.tauStateAffine_apply",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.28385403752326965,
            "y": 0.48885011672973633,
            "z": 0.5667495727539062
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.CtrlCantorBlock",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.9733275771141052,
            "y": 0.016038106754422188,
            "z": 0.6173461079597473
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.CtrlCantorBlockExplicit",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.888745129108429,
            "y": 0.050302762538194656,
            "z": 0.41174325346946716
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.CtrlCantorBlockExplicit_subset_CtrlCantorBlock",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.7077077627182007,
            "y": 0.079307422041893,
            "z": 0.4786723852157593
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.paperFctrlAffine",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.37121063470840454,
            "y": 0.2489597350358963,
            "z": 0.35754430294036865
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.paperFctrlAffine_apply",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.44139036536216736,
            "y": 0.18092764914035797,
            "z": 0.4295770227909088
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.paperFctrl",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.7808977961540222,
            "y": 0.05265829339623451,
            "z": 0.15041106939315796
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.paperFctrl",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.9808335900306702,
            "y": 0.015166315250098705,
            "z": 0.6955739855766296
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.encodeCfgCtrl_mem_CtrlCantorBlock",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.916052520275116,
            "y": 0.01513015478849411,
            "z": 0.5877133011817932
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.paperFctrl",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.9928663372993469,
            "y": 0.005998463369905949,
            "z": 0.7983267307281494
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.paperFctrlAffine_encodeCfgCtrl_eq_encodeCfgCtrl_step",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.9696200489997864,
            "y": 0.01572541706264019,
            "z": 0.7771188020706177
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.paperFctrl",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.7677790522575378,
            "y": 0.05121253430843353,
            "z": 0.14216569066047668
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.paperFctrlAffine_encodeCfgCtrl_eq_encodeCfgCtrl_step_cfg",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.9093368649482727,
            "y": 0.008993378840386868,
            "z": 0.692857027053833
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.decodeTape",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.495240181684494,
            "y": 0.07022752612829208,
            "z": 0.1411573588848114
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.decodeTape",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.5561254024505615,
            "y": 0.07440385222434998,
            "z": 0.06267955154180527
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.paperFfull",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.28443291783332825,
            "y": 0.42249467968940735,
            "z": 0.336313933134079
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.paperFfull",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.9521892666816711,
            "y": 0.02242196351289749,
            "z": 0.5014982223510742
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.paperFfull",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.8358591794967651,
            "y": 0.0558885894715786,
            "z": 0.2232961356639862
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.paperFfull",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.7794994115829468,
            "y": 0.049750566482543945,
            "z": 0.1516520082950592
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.toGenShiftCfg",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.28386208415031433,
            "y": 0.4283156991004944,
            "z": 0.3572377860546112
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.tapeUpdate_eq_write",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.3089085519313812,
            "y": 0.412163645029068,
            "z": 0.46685221791267395
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.encodeCfg",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.6950922012329102,
            "y": 0.05797641724348068,
            "z": 0.13282528519630432
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.paperFgen",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.2422807514667511,
            "y": 0.5139694809913635,
            "z": 0.40218299627304077
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.paperFgen",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.909217894077301,
            "y": 0.039087750017642975,
            "z": 0.3506430685520172
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.paperFpiece",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.2246062010526657,
            "y": 0.5594633221626282,
            "z": 0.45166268944740295
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.paperFpiece",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.9163395166397095,
            "y": 0.035071223974227905,
            "z": 0.36601391434669495
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.paperFpiece",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.91146320104599,
            "y": 0.03548759967088699,
            "z": 0.35300928354263306
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.paperFpiece",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.9161665439605713,
            "y": 0.03701162710785866,
            "z": 0.36358699202537537
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.rwWallUnion",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.5313296318054199,
            "y": 0.06756438314914703,
            "z": 0.10890030860900879
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.tildeWallUnion",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.7042781710624695,
            "y": 0.05736647918820381,
            "z": 0.1582697629928589
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.rwWallRewriteUnion",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.6100519299507141,
            "y": 0.07352956384420395,
            "z": 0.17554567754268646
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.paperReadWriteBoundary",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.6867610812187195,
            "y": 0.06610817462205887,
            "z": 0.247165709733963
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.rwDigits",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.8693345189094543,
            "y": 0.05044097825884819,
            "z": 0.2802587151527405
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.rwWallUnionCanonical",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.8488288521766663,
            "y": 0.06366200000047684,
            "z": 0.29323598742485046
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.tildeWallUnionCanonical",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.945618212223053,
            "y": 0.019542725756764412,
            "z": 0.5206425786018372
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.rwWallRewriteUnionCanonical",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.921320915222168,
            "y": 0.025740407407283783,
            "z": 0.48582541942596436
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.paperReadWriteBoundaryCanonical",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.1773051917552948,
            "y": 0.7076190114021301,
            "z": 0.7272299528121948
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.Plane.mk",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.04329267889261246,
            "y": 0.944337010383606,
            "z": 0.8146920204162598
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.Plane.mk_x",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.052579283714294434,
            "y": 0.9236547946929932,
            "z": 0.789104163646698
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.Plane.mk_y",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.015461922623217106,
            "y": 0.9529446363449097,
            "z": 0.9878268837928772
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.rwWallConst",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.9040406942367554,
            "y": 0.04182618483901024,
            "z": 0.3389144837856293
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.rwWallLine",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.6310240626335144,
            "y": 0.06684721261262894,
            "z": 0.12228935956954956
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.mem_rwWallLine_iff",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.713072657585144,
            "y": 0.058695316314697266,
            "z": 0.17947359383106232
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.rwWall_subset_rwWallLine",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.751481831073761,
            "y": 0.05849360302090645,
            "z": 0.26642411947250366
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.ReadOnlyCollision.State",
        "kind": "structure",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.02978258579969406,
            "y": 0.9349493980407715,
            "z": 0.9664746522903442
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.ReadOnlyCollision.pos",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.042986154556274414,
            "y": 0.9288043975830078,
            "z": 0.9006885886192322
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.ReadOnlyCollision.vel",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.4210589528083801,
            "y": 0.1969260424375534,
            "z": 0.42110973596572876
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.ReadOnlyCollision.Good",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.413699746131897,
            "y": 0.21340115368366241,
            "z": 0.43038278818130493
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.ReadOnlyCollision.Good",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.8513274192810059,
            "y": 0.06216185539960861,
            "z": 0.3168589174747467
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.ReadOnlyCollision.inner_rwWallNormal_vel_ne_zero",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.8299440145492554,
            "y": 0.0534464456140995,
            "z": 0.5189617872238159
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.ReadOnlyCollision.inner_rwWallNormal_eY",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.7823659181594849,
            "y": 0.06191860884428024,
            "z": 0.458426833152771
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.ReadOnlyCollision.norm_rwWallNormal_sq",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.623982310295105,
            "y": 0.11130047589540482,
            "z": 0.47402137517929077
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.ReadOnlyCollision.reflect_rwWallNormal_eY",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.8328256607055664,
            "y": 0.05655722692608833,
            "z": 0.47869765758514404
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.ReadOnlyCollision.hitTime",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.4538194537162781,
            "y": 0.17796362936496735,
            "z": 0.4451240301132202
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.ReadOnlyCollision.hitPoint",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.17716805636882782,
            "y": 0.6938635110855103,
            "z": 0.6558570265769958
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.ReadOnlyCollision.hitTime",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.43214815855026245,
            "y": 0.19927966594696045,
            "z": 0.4482805132865906
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.ReadOnlyCollision.hitPoint",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.30776557326316833,
            "y": 0.45166096091270447,
            "z": 0.5809060335159302
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.ReadOnlyCollision.hitPoint_mem_rwWall",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.9620043039321899,
            "y": 0.014465737156569958,
            "z": 0.6995252966880798
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.ReadOnlyCollision.next",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.12769946455955505,
            "y": 0.7821264266967773,
            "z": 0.7148057222366333
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.ReadOnlyCollision.next",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.9611154198646545,
            "y": 0.01765795424580574,
            "z": 0.565498948097229
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.ReadOnlyCollision.tildeWall_subset_rwWallLine",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.7814697027206421,
            "y": 0.06241191178560257,
            "z": 0.49038752913475037
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.ReadOnlyCollision.next2",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.11085737496614456,
            "y": 0.8139459490776062,
            "z": 0.7569977641105652
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.ReadOnlyCollision.next2",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.3977130651473999,
            "y": 0.23202556371688843,
            "z": 0.42024365067481995
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.ReadOnlyCollision.next2",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.834481418132782,
            "y": 0.06901302188634872,
            "z": 0.29780465364456177
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.ReadOnlyCollision.hitTime_unique",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.5186493992805481,
            "y": 0.15128697454929352,
            "z": 0.4702281057834625
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.ReadOnlyCollisionCanonical.State",
        "kind": "structure",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.0363645926117897,
            "y": 0.919613242149353,
            "z": 0.9582415223121643
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.ReadOnlyCollisionCanonical.ds",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.3411591351032257,
            "y": 0.40194347500801086,
            "z": 0.5886500477790833
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.ReadOnlyCollisionCanonical.ds_length",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.2929137051105499,
            "y": 0.5029720067977905,
            "z": 0.6389833688735962
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.ReadOnlyCollisionCanonical.pos",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.5218197703361511,
            "y": 0.1503199338912964,
            "z": 0.47216740250587463
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.ReadOnlyCollisionCanonical.vel",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.34916412830352783,
            "y": 0.3837853968143463,
            "z": 0.5785555839538574
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.ReadOnlyCollisionCanonical.Good",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.44720321893692017,
            "y": 0.21904300153255463,
            "z": 0.5151448845863342
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.ReadOnlyCollisionCanonical.Good",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.4680807292461395,
            "y": 0.1948644071817398,
            "z": 0.5042924284934998
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.ReadOnlyCollisionCanonical.rwWallConst",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.47669053077697754,
            "y": 0.22202353179454803,
            "z": 0.567490816116333
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.ReadOnlyCollisionCanonical.hitTime",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.4394555687904358,
            "y": 0.25567930936813354,
            "z": 0.5631712079048157
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.ReadOnlyCollisionCanonical.hitPoint",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.17686964571475983,
            "y": 0.7104715704917908,
            "z": 0.7411468625068665
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.ReadOnlyCollisionCanonical.hitTime",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.46501561999320984,
            "y": 0.2173149585723877,
            "z": 0.5451387166976929
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.ReadOnlyCollisionCanonical.hitPoint",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.341034859418869,
            "y": 0.4090921878814697,
            "z": 0.607171893119812
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.ReadOnlyCollisionCanonical.hitPoint_mem_rwWall",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.8090224862098694,
            "y": 0.05805123224854469,
            "z": 0.5056772232055664
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.ReadOnlyCollisionCanonical.next",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.1378752887248993,
            "y": 0.7744887471199036,
            "z": 0.7562370896339417
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.ReadOnlyCollisionCanonical.next",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.9582531452178955,
            "y": 0.015286499634385109,
            "z": 0.6037871241569519
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.ReadOnlyCollisionCanonical.next",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.9561426639556885,
            "y": 0.015718989074230194,
            "z": 0.5915045142173767
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.ReadOnlyCollisionCanonical.rwWallUnionCanonical_unique_of_hit",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.7853328585624695,
            "y": 0.05944107100367546,
            "z": 0.5728975534439087
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.AppendixStraight.State",
        "kind": "structure",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.08198799192905426,
            "y": 0.866595983505249,
            "z": 0.8201119899749756
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.AppendixStraight.endpointY",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.6694269180297852,
            "y": 0.0926714539527893,
            "z": 0.4698929190635681
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.AppendixStraight.upperEndpoint",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.3223848044872284,
            "y": 0.4590083956718445,
            "z": 0.6436821818351746
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.AppendixStraight.vel",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.5291427969932556,
            "y": 0.15672795474529266,
            "z": 0.49490609765052795
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.AppendixStraight.flightRay",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.6292675733566284,
            "y": 0.11021507531404495,
            "z": 0.4827478229999542
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.AppendixStraight.traj",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.8753315210342407,
            "y": 0.040800925344228745,
            "z": 0.5214704275131226
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.AppendixStraight.upperEndpoint_mem_rwWall",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.9442740082740784,
            "y": 0.016126638278365135,
            "z": 0.7425312995910645
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.AppendixStraight.traj_subset_flightRay",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.36732548475265503,
            "y": 0.39243289828300476,
            "z": 0.6411671042442322
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.rwWallRewriteNormal",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.868980884552002,
            "y": 0.04549366980791092,
            "z": 0.500285267829895
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.rwWallRewriteConst",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.8531295657157898,
            "y": 0.05510101467370987,
            "z": 0.4538917541503906
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.rwWallRewriteLine",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.7008796334266663,
            "y": 0.06965873390436172,
            "z": 0.34644344449043274
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.rwWallRewrite_subset_rwWallRewriteLine",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.6083398461341858,
            "y": 0.1367167830467224,
            "z": 0.5448129773139954
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.RewriteCollision.State",
        "kind": "structure",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.03297199308872223,
            "y": 0.9315464496612549,
            "z": 0.9618825316429138
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.RewriteCollision.pos",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.6191991567611694,
            "y": 0.10991178452968597,
            "z": 0.45454129576683044
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.RewriteCollision.vel",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.4583905041217804,
            "y": 0.23513519763946533,
            "z": 0.5664913058280945
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.RewriteCollision.Good",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.4582025408744812,
            "y": 0.23695090413093567,
            "z": 0.5679791569709778
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.RewriteCollision.Good",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.750714898109436,
            "y": 0.06343036144971848,
            "z": 0.4081421196460724
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.RewriteCollision.inner_rwWallRewriteNormal_vel",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.7769445180892944,
            "y": 0.06102447211742401,
            "z": 0.5682048201560974
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.RewriteCollision.inner_rwWallRewriteNormal_vel_ne_zero",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.8789011240005493,
            "y": 0.03119080141186714,
            "z": 0.6597897410392761
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.RewriteCollision.hitTime",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.5630770921707153,
            "y": 0.14547553658485413,
            "z": 0.5102204084396362
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.RewriteCollision.hitPoint",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.1779937595129013,
            "y": 0.7079824805259705,
            "z": 0.7459090948104858
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.RewriteCollision.hitTime",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.463822603225708,
            "y": 0.23679916560649872,
            "z": 0.5787345767021179
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.RewriteCollision.hitPoint",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.19033324718475342,
            "y": 0.6830356121063232,
            "z": 0.735848605632782
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.RewriteCollision.hitPoint_mem_rwWallRewrite",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.7408434748649597,
            "y": 0.07218749821186066,
            "z": 0.5297532677650452
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.RewriteCollision.next",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.18042738735675812,
            "y": 0.7038974165916443,
            "z": 0.7369336485862732
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.RewriteCollision.next",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.6887428760528564,
            "y": 0.07687630504369736,
            "z": 0.38251909613609314
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.RewriteCollision.rewriteSlope_lt_one",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.8591964244842529,
            "y": 0.040293239057064056,
            "z": 0.5760548114776611
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.RewriteCollision.y_reflect_rwWallRewriteNormal_eY_neg",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.7470517158508301,
            "y": 0.07091649621725082,
            "z": 0.5751312375068665
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.RewriteCollisionCanonical.State",
        "kind": "structure",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.03892143815755844,
            "y": 0.9227641224861145,
            "z": 0.9472553730010986
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.RewriteCollisionCanonical.ds",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.571014404296875,
            "y": 0.14889173209667206,
            "z": 0.5270870327949524
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.RewriteCollisionCanonical.toNoncanonical",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.7811488509178162,
            "y": 0.06064770743250847,
            "z": 0.55301433801651
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.RewriteCollisionCanonical.Good",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.6265111565589905,
            "y": 0.11680036038160324,
            "z": 0.5114241242408752
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.RewriteCollisionCanonical.Good",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.5658379793167114,
            "y": 0.1570909172296524,
            "z": 0.5356988310813904
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.RewriteCollisionCanonical.next",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.6618614196777344,
            "y": 0.09774249792098999,
            "z": 0.4850490093231201
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.RewriteCollisionCanonical.next",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.9541459083557129,
            "y": 0.013345137238502502,
            "z": 0.7263941168785095
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.RewriteCollisionCanonical.next",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.9553918838500977,
            "y": 0.014780345372855663,
            "z": 0.7343936562538147
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.RewriteCollisionCanonical.rwWallRewriteUnionCanonical_unique_of_hit",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.9012045860290527,
            "y": 0.02660941705107689,
            "z": 0.7174880504608154
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.ReadOnlyCollisionCanonical.toNoncanonical",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.09895224869251251,
            "y": 0.8387378454208374,
            "z": 0.8026390671730042
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.ReadOnlyCollisionCanonical.toNoncanonical_k",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.9767369627952576,
            "y": 0.015344241634011269,
            "z": 0.7883920073509216
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.ReadOnlyCollisionCanonical.toNoncanonical_ds",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.967909574508667,
            "y": 0.015940558165311813,
            "z": 0.776080846786499
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.ReadOnlyCollisionCanonical.toNoncanonical_cur",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.8450770378112793,
            "y": 0.04351106286048889,
            "z": 0.5916257500648499
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.ReadOnlyCollisionCanonical.toNoncanonical_x0",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.8647607564926147,
            "y": 0.03587251529097557,
            "z": 0.6115385293960571
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.ReadOnlyCollisionCanonical.Good",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.9067261815071106,
            "y": 0.010105825029313564,
            "z": 0.6597282290458679
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.ReadOnlyCollisionCanonical.next2",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.39085957407951355,
            "y": 0.3631304204463959,
            "z": 0.6387276649475098
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.ReadOnlyCollisionCanonical.next2",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.42183029651641846,
            "y": 0.3191501498222351,
            "z": 0.6340118646621704
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.ReadOnlyCollisionCanonical.next2",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.6659720540046692,
            "y": 0.09734530001878738,
            "z": 0.4933564364910126
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.ReadOnlyCollisionCanonical.next2",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.8777788281440735,
            "y": 0.031798914074897766,
            "z": 0.5902383923530579
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.ReadOnlyCollisionCanonical.tildeWallUnionCanonical_unique_of_hit",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.896817684173584,
            "y": 0.027051882818341255,
            "z": 0.7067461013793945
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.ReadOnlyCorridor.Entry",
        "kind": "structure",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.038045767694711685,
            "y": 0.9241200089454651,
            "z": 0.9482406973838806
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.ReadOnlyCorridor.block",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.8023127317428589,
            "y": 0.06137332320213318,
            "z": 0.4548521041870117
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.ReadOnlyCorridor.block_spec",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.6316905617713928,
            "y": 0.11188480257987976,
            "z": 0.49404850602149963
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.ReadOnlyCorridor.pref",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.18502116203308105,
            "y": 0.695502758026123,
            "z": 0.7322514653205872
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.ReadOnlyCorridor.cur",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.1673831194639206,
            "y": 0.7302625179290771,
            "z": 0.7511278390884399
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.ReadOnlyCorridor.pref_length",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.5758259892463684,
            "y": 0.14705318212509155,
            "z": 0.5287007689476013
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.ReadOnlyCorridor.x0_mem_block_Ioo",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.46390488743782043,
            "y": 0.2721705138683319,
            "z": 0.6318132281303406
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.ReadOnlyCorridor.x0_mem_block_Icc",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.7800523042678833,
            "y": 0.06251867115497589,
            "z": 0.512925386428833
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.ReadOnlyCorridor.state",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.14539679884910583,
            "y": 0.7617570757865906,
            "z": 0.7681770324707031
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.ReadOnlyCorridor.state_Good",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.8798372745513916,
            "y": 0.03236396238207817,
            "z": 0.5801966786384583
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.ReadOnlyCorridor.next2",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.3068990111351013,
            "y": 0.4781089425086975,
            "z": 0.6309430003166199
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.ReadOnlyCorridor.next2",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.47665753960609436,
            "y": 0.21848398447036743,
            "z": 0.5623157024383545
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.ReadOnlyCorridor.block_unique",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.31519681215286255,
            "y": 0.47242143750190735,
            "z": 0.6507452726364136
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.flightLineLeft0",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.6969302296638489,
            "y": 0.06917224824428558,
            "z": 0.32959145307540894
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.mem_flightLineLeft0_iff",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.8397617936134338,
            "y": 0.05697561800479889,
            "z": 0.46318429708480835
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.flightRayLeft0",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.48974037170410156,
            "y": 0.16257084906101227,
            "z": 0.46439623832702637
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.flightRayLeft0_subset_flightLineLeft0",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.35067737102508545,
            "y": 0.41363921761512756,
            "z": 0.6396855711936951
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.rwWall_false_mem_flightLineLeft0_imp_rightEndpoint",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.9639085531234741,
            "y": 0.016829902306199074,
            "z": 0.7782307267189026
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.rwWall_false_mem_flightLineLeft0_imp_rightEndpoint_of_endpointSep",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.9399340152740479,
            "y": 0.022853879258036613,
            "z": 0.7596907019615173
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.rwWall_false_disjoint_flightLineLeft0_of_endpointSep",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.7838940620422363,
            "y": 0.05997811257839203,
            "z": 0.576206624507904
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.rwBlockLeft_ne_of_length_eq",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.9828429222106934,
            "y": 0.014405980706214905,
            "z": 0.7883760929107666
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.rwWall_false_disjoint_flightRayLeft0_of_ne",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.9982869625091553,
            "y": 0.004683440085500479,
            "z": 0.8226797580718994
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.flightLineRight1",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.8681828379631042,
            "y": 0.0499996654689312,
            "z": 0.46218594908714294
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.mem_flightLineRight1_iff",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.8990901112556458,
            "y": 0.020401662215590477,
            "z": 0.5958706736564636
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.flightRayRight1",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.5896902084350586,
            "y": 0.11925218999385834,
            "z": 0.4404776394367218
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.flightRayRight1_subset_flightLineRight1",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.47411856055259705,
            "y": 0.2694280445575714,
            "z": 0.6432230472564697
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.rwWall_true_mem_flightLineRight1_imp_leftEndpoint",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.9507315754890442,
            "y": 0.017650185152888298,
            "z": 0.7579417824745178
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.rwWall_true_mem_flightLineRight1_imp_leftEndpoint_of_endpointSep",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.8657066822052002,
            "y": 0.03641041740775108,
            "z": 0.6555473804473877
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.rwWall_true_disjoint_flightLineRight1_of_endpointSep",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.7304914593696594,
            "y": 0.07804706692695618,
            "z": 0.5594911575317383
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.rwWall_true_disjoint_flightRayRight1_of_ne",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.9003958106040955,
            "y": 0.01706298068165779,
            "z": 0.6750433444976807
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.rwWall_disjoint_flightRayLeft0_of_k_lt",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.4726937711238861,
            "y": 0.2683838903903961,
            "z": 0.6442927122116089
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.rwWall_disjoint_flightRayRight1_of_k_gt",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.4746651351451874,
            "y": 0.2666641175746918,
            "z": 0.6392293572425842
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.rwWallRewrite_disjoint_flightRayLeft0_of_k_lt",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.4908687174320221,
            "y": 0.252288818359375,
            "z": 0.6363909244537354
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.rwWallRewrite_disjoint_flightRayRight1_of_k_gt",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.6046140789985657,
            "y": 0.14731906354427338,
            "z": 0.559357762336731
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.rewriteSlope_lt_one",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.8341610431671143,
            "y": 0.06040734052658081,
            "z": 0.42638099193573
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.rwWallRewrite_false_disjoint_flightRayLeft0_self",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.6238877177238464,
            "y": 0.12846234440803528,
            "z": 0.5459926128387451
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.rwWallRewrite_true_disjoint_flightRayRight1_self",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.6631033420562744,
            "y": 0.10571838915348053,
            "z": 0.5361489057540894
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.rwWall_false_disjoint_flightRayLeft0_of_lt_canonical",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.9124985337257385,
            "y": 0.01726047322154045,
            "z": 0.7201464176177979
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.rwWall_true_disjoint_flightRayRight1_of_lt_canonical",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.9144322872161865,
            "y": 0.016186969354748726,
            "z": 0.7209489941596985
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.rwWallRewrite_disjoint_flightRayLeft0_of_k_lt_canonical",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.9272908568382263,
            "y": 0.02078830450773239,
            "z": 0.7425413131713867
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.rwWallRewrite_disjoint_flightRayRight1_of_k_gt_canonical",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.9271557331085205,
            "y": 0.020916065201163292,
            "z": 0.7436883449554443
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.endpointSepCross",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.700536847114563,
            "y": 0.06918644160032272,
            "z": 0.3423350751399994
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.cantorWidth_le_one_third_of_length_pos",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.9113115668296814,
            "y": 0.011116215959191322,
            "z": 0.693812906742096
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.negSucc_lt_negSucc_iff",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.789810061454773,
            "y": 0.06156112626194954,
            "z": 0.4601777493953705
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.headScale_ofNat_le_div_three_of_lt",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.6828578114509583,
            "y": 0.08958503603935242,
            "z": 0.48952415585517883
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.headLeft_sub_headRight_ofNat_ge",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.9048481583595276,
            "y": 0.012145310640335083,
            "z": 0.6527247428894043
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.rwBlockLeft_mem_headInterval",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.9047880172729492,
            "y": 0.014309680089354515,
            "z": 0.6272732019424438
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.rwBlockRight_mem_headInterval",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.8885433673858643,
            "y": 0.024926358833909035,
            "z": 0.603587806224823
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.endpointSepCross_ofNat_of_lt",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.9094808101654053,
            "y": 0.00824474636465311,
            "z": 0.6442424058914185
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.headScale_negSucc_le_div_three_of_lt",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.9203837513923645,
            "y": 0.008484730497002602,
            "z": 0.7045371532440186
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.headLeft_sub_headRight_negSucc_ge",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.9961219429969788,
            "y": 0.010795085690915585,
            "z": 0.8178894519805908
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.endpointSepCross_negSucc_of_lt",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.9194316267967224,
            "y": 0.006726090330630541,
            "z": 0.6893384456634521
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.headScale_le_one_ninth_of_negSucc",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.993863046169281,
            "y": 0.009873609989881516,
            "z": 0.8128542304039001
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.headLeft_ofNat_ge_one_third",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.9972836971282959,
            "y": 0.002835213439539075,
            "z": 0.8200886249542236
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.headRight_negSucc_le_two_ninth",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.8776569366455078,
            "y": 0.03252001851797104,
            "z": 0.584924578666687
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.endpointSepCross_ofNat_negSucc",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.9073352813720703,
            "y": 0.009907852858304977,
            "z": 0.6531469821929932
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.rwWall_false_disjoint_flightRayLeft0_of_ofNat_lt",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.7793853878974915,
            "y": 0.07014158368110657,
            "z": 0.5672188401222229
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.rwWall_true_disjoint_flightRayRight1_of_ofNat_lt",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.9088961482048035,
            "y": 0.012578856199979782,
            "z": 0.714518666267395
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.rwWall_false_disjoint_flightRayLeft0_of_negSucc",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.6515174508094788,
            "y": 0.11197899281978607,
            "z": 0.5343897342681885
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.rwWall_true_disjoint_flightRayRight1_of_negSucc",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.6640814542770386,
            "y": 0.10350730270147324,
            "z": 0.5265442132949829
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.rwWall_false_disjoint_flightRayLeft0_of_negSucc_lt",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.7172906398773193,
            "y": 0.0826171338558197,
            "z": 0.5486857295036316
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.rwWall_true_disjoint_flightRayRight1_of_negSucc_lt",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.726856529712677,
            "y": 0.07833539694547653,
            "z": 0.5571879744529724
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.rwWall_false_disjoint_flightRayLeft0_of_lt",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.6767650246620178,
            "y": 0.09723518788814545,
            "z": 0.5243001580238342
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.rwWall_true_disjoint_flightRayRight1_of_lt",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.6282737851142883,
            "y": 0.12379904836416245,
            "z": 0.5419933199882507
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.rwWall_false_mem_flightLineLeft0_imp_rightEndpoint_of_endpointSepCross",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.9107149839401245,
            "y": 0.030126504600048065,
            "z": 0.7423478960990906
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.rwWall_false_disjoint_flightLineLeft0_of_endpointSepCross",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.7238239645957947,
            "y": 0.07792602479457855,
            "z": 0.5666261911392212
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.rwWall_true_mem_flightLineRight1_imp_leftEndpoint_of_endpointSepCross",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.8976352214813232,
            "y": 0.02731105126440525,
            "z": 0.7127684950828552
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.rwWall_true_disjoint_flightLineRight1_of_endpointSepCross",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.7283447980880737,
            "y": 0.07741469144821167,
            "z": 0.56760174036026
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.belowFlightLineLeft0",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.8791232109069824,
            "y": 0.03473052754998207,
            "z": 0.5368601679801941
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.belowFlightLineRight1",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.8755771517753601,
            "y": 0.038846999406814575,
            "z": 0.5387986898422241
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.rwWall_false_mem_belowFlightLineLeft0_imp_rightEndpoint_of_endpointSep",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.9536072611808777,
            "y": 0.01928461156785488,
            "z": 0.7673693895339966
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.rwWall_false_disjoint_belowFlightLineLeft0_of_endpointSep",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.7413524389266968,
            "y": 0.07310359925031662,
            "z": 0.5732094049453735
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.rwWall_true_mem_belowFlightLineRight1_imp_leftEndpoint_of_endpointSep",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.8951162099838257,
            "y": 0.0268719419836998,
            "z": 0.7008150219917297
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.rwWall_true_disjoint_belowFlightLineRight1_of_endpointSep",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.7178667187690735,
            "y": 0.083403080701828,
            "z": 0.5590787529945374
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.rwWall_false_mem_belowFlightLineLeft0_imp_rightEndpoint_of_endpointSepCross",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.9086272716522217,
            "y": 0.0271297674626112,
            "z": 0.7309575080871582
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.rwWall_false_disjoint_belowFlightLineLeft0_of_endpointSepCross",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.7282857894897461,
            "y": 0.0797630250453949,
            "z": 0.5695976614952087
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.rwWall_true_mem_belowFlightLineRight1_imp_leftEndpoint_of_endpointSepCross",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.8993769884109497,
            "y": 0.025741558521986008,
            "z": 0.7111135125160217
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.rwWall_true_disjoint_belowFlightLineRight1_of_endpointSepCross",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.7326755523681641,
            "y": 0.07669607549905777,
            "z": 0.5718368291854858
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.tauOffset",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.4147658944129944,
            "y": 0.21231402456760406,
            "z": 0.4329797029495239
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.tau_eq_affine",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.28535792231559753,
            "y": 0.5065011382102966,
            "z": 0.6153731346130371
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.tau_sub",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.9675594568252563,
            "y": 0.01736339181661606,
            "z": 0.5944585800170898
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.rwBlockLeft_separated_of_length_eq",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.9587363600730896,
            "y": 0.014306130819022655,
            "z": 0.7488224506378174
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.rwBlockLeft_separated_of_append_singleton_of_length_eq",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.9980475306510925,
            "y": 0.006950440816581249,
            "z": 0.8232282400131226
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.rwBlockLen_eq_of_length_eq",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.9140852689743042,
            "y": 0.006682639941573143,
            "z": 0.6420618891716003
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.rwBlockLeft_sub_right_ge_len_of_left_gt",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.9949961304664612,
            "y": 0.015559383668005466,
            "z": 0.8153908252716064
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.endpointSep",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.9266871213912964,
            "y": 0.023470530286431313,
            "z": 0.4995035231113434
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.endpointSep_of_length_eq_of_left_gt",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.9598687887191772,
            "y": 0.015834281221032143,
            "z": 0.7582414746284485
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.endpointSepCross",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.8453304171562195,
            "y": 0.05961449071764946,
            "z": 0.4145735800266266
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.rwBlockInterval_eq_image_tau",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.6510239839553833,
            "y": 0.10188304632902145,
            "z": 0.4831927716732025
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.rwBlockInterval_disjoint_of_length_eq",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.9880815744400024,
            "y": 0.015232305973768234,
            "z": 0.800165593624115
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.rwBlockInterval_disjoint_of_rwDigits",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.9861742854118347,
            "y": 0.016798920929431915,
            "z": 0.7977438569068909
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.rwBlockInterval_eq_of_mem_of_rwDigits",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.8272245526313782,
            "y": 0.05155256390571594,
            "z": 0.5502205491065979
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.rwBlockInterval_subset_headInterval",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.9191002249717712,
            "y": 0.011798282153904438,
            "z": 0.7052457928657532
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.rwBlockInterval_disjoint_of_k_ne",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.9981133341789246,
            "y": 0.0039479476399719715,
            "z": 0.8222925066947937
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.rwWall_disjoint_of_length_eq",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.4913233518600464,
            "y": 0.2223975956439972,
            "z": 0.5832783579826355
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.mem_tildeWall_iff",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.8466022610664368,
            "y": 0.057603299617767334,
            "z": 0.43978655338287354
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.tildeWall_disjoint_of_length_eq",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.5587217807769775,
            "y": 0.16860230267047882,
            "z": 0.5475795865058899
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.rwWallRewrite_disjoint_of_length_eq",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.6173674464225769,
            "y": 0.1284966766834259,
            "z": 0.5353589653968811
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.RewriteBetween.Entry",
        "kind": "structure",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.04242908954620361,
            "y": 0.9181836843490601,
            "z": 0.9343188405036926
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.RewriteBetween.ds",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.5597630143165588,
            "y": 0.13693584501743317,
            "z": 0.47477200627326965
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.RewriteBetween.endpointY",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.46410220861434937,
            "y": 0.23598003387451172,
            "z": 0.5772438645362854
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.RewriteBetween.startPos",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.1865280717611313,
            "y": 0.6884856224060059,
            "z": 0.7352271676063538
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.RewriteBetween.startVel",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.1682613492012024,
            "y": 0.7279693484306335,
            "z": 0.7532570362091064
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.RewriteBetween.startState",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.5740870237350464,
            "y": 0.14202865958213806,
            "z": 0.5148578882217407
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.RewriteBetween.rwWallUnionCanonicalNoEndpoint",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.7836524248123169,
            "y": 0.059998638927936554,
            "z": 0.573390781879425
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.RewriteBetween.tildeWallRewriteAppendixUnionCanonicalAt",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.606346607208252,
            "y": 0.14891397953033447,
            "z": 0.5628980994224548
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.RewriteBetween.table",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.3656422197818756,
            "y": 0.36491140723228455,
            "z": 0.5869901180267334
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.RewriteBetween.table_boundary",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.3782682418823242,
            "y": 0.37415629625320435,
            "z": 0.6366174221038818
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.RewriteBetween.hitPoint\u2082",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.3491027355194092,
            "y": 0.4095742404460907,
            "z": 0.6260152459144592
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.RewriteBetween.hitPoint\u2082_mem_tildeWallRewriteAppendix",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.48013728857040405,
            "y": 0.2637068033218384,
            "z": 0.6470786929130554
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.RewriteBetween.hitPoint\u2082_mem_boundary",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.6336565017700195,
            "y": 0.11897806078195572,
            "z": 0.5334174633026123
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.RewriteBetween.rewriteSlope_lt_one",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.9122273325920105,
            "y": 0.009289667010307312,
            "z": 0.6875952482223511
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.RewriteBetween.endpointSepCross_of_lt",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.7868620157241821,
            "y": 0.06092270463705063,
            "z": 0.5363350510597229
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.RewriteBetween.hitPoint_mem_belowFlightLine",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.9033659100532532,
            "y": 0.014433125033974648,
            "z": 0.690902590751648
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.RewriteBetween.no_rwWallSameKCanonicalNoEndpoint_hit_before_two",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.7254607081413269,
            "y": 0.07871369272470474,
            "z": 0.5674818158149719
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.RewriteBetween.y_le_rewriteSlope_mul_half_rwBlockLen_of_mem_tildeWallRewriteAppendix",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.9066736102104187,
            "y": 0.031046830117702484,
            "z": 0.7396868467330933
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.RewriteBetween.no_tildeWallRewriteAppendixUnionCanonicalAt_hit_before_two",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.634695291519165,
            "y": 0.12462757527828217,
            "z": 0.5518162250518799
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.RewriteBetween.no_boundary_hit_before_two",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.911320686340332,
            "y": 0.01348297018557787,
            "z": 0.6993880867958069
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.RewriteBetween.start_Good_firstHit",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.45655304193496704,
            "y": 0.2793397307395935,
            "z": 0.6313742995262146
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.RewriteBetween.next",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.8779483437538147,
            "y": 0.03860720619559288,
            "z": 0.5287224650382996
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.RewriteBetweenGlobal.tildeWallRewriteAppendixUnionCanonicalCur",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.7267852425575256,
            "y": 0.07509953528642654,
            "z": 0.570468008518219
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.RewriteBetweenGlobal.hitPoint\u2082_mem_tildeWallRewriteAppendixUnionCanonicalCur",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.7303268313407898,
            "y": 0.07635749131441116,
            "z": 0.5715907216072083
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.RewriteBetweenGlobal.table",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.49406006932258606,
            "y": 0.21543286740779877,
            "z": 0.5768604874610901
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.RewriteBetweenGlobal.table_boundary",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.7548434734344482,
            "y": 0.06741207093000412,
            "z": 0.5024148225784302
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.RewriteBetweenGlobal.hitPoint\u2082_mem_boundary",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.6292241215705872,
            "y": 0.12417235225439072,
            "z": 0.5439063310623169
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.RewriteBetweenGlobal.NoOtherKRedirectingHitsBeforeTwo",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.477367103099823,
            "y": 0.2682189345359802,
            "z": 0.6534135937690735
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.RewriteBetweenGlobal.noOtherKRedirectingHitsBeforeTwo",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.36417466402053833,
            "y": 0.3988315463066101,
            "z": 0.6435531377792358
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.RewriteBetweenGlobal.no_boundary_hit_before_two",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.7927628755569458,
            "y": 0.05726739764213562,
            "z": 0.580983579158783
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.RewriteBetweenGlobal.start_Good_firstHit",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.6071929335594177,
            "y": 0.13826870918273926,
            "z": 0.5463132262229919
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.RewriteBetweenGlobal.next",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.9061529040336609,
            "y": 0.013152056373655796,
            "z": 0.6238051652908325
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.RewriteBetween.tildeWallRewriteAppendixUnionCanonicalCur",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.4490254819393158,
            "y": 0.298299103975296,
            "z": 0.6469047665596008
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.RewriteBetween.tableGlobal",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.563579797744751,
            "y": 0.1548706293106079,
            "z": 0.5304042100906372
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.RewriteBetween.tableGlobal_boundary",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.4349746108055115,
            "y": 0.3082566261291504,
            "z": 0.6390930414199829
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.RewriteBetween.next",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.8806469440460205,
            "y": 0.04075699672102928,
            "z": 0.52098548412323
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.RewriteDeterministic.Entry",
        "kind": "structure",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.037722256034612656,
            "y": 0.9165768623352051,
            "z": 0.952245831489563
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.RewriteDeterministic.startPos",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.39250117540359497,
            "y": 0.3551568388938904,
            "z": 0.6355547904968262
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.RewriteDeterministic.startVel",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.3847314119338989,
            "y": 0.36818066239356995,
            "z": 0.6371198296546936
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.RewriteDeterministic.startState",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.4759870767593384,
            "y": 0.2525251507759094,
            "z": 0.6204028725624084
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.RewriteDeterministic.table",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.3356665372848511,
            "y": 0.4339030385017395,
            "z": 0.6321640610694885
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.RewriteDeterministic.hitTime",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.4330993890762329,
            "y": 0.30168095231056213,
            "z": 0.6262756586074829
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.RewriteDeterministic.hitTime_pos",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.7459590435028076,
            "y": 0.06762126833200455,
            "z": 0.4728638827800751
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.RewriteDeterministic.hitPoint",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.6964338421821594,
            "y": 0.08304367959499359,
            "z": 0.47224104404449463
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.RewriteDeterministic.hitPoint_eq_mk",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.7719570994377136,
            "y": 0.06381930410861969,
            "z": 0.5270051956176758
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.RewriteDeterministic.hitPoint_mem_boundary",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.7126606106758118,
            "y": 0.08101972937583923,
            "z": 0.5152673721313477
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.RewriteDeterministic.no_boundary_hit_before_hitTime",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.9974442720413208,
            "y": 0.013179008848965168,
            "z": 0.8222250938415527
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.RewriteDeterministic.isFirstHitTime_hitTime",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.7660838961601257,
            "y": 0.0656130462884903,
            "z": 0.546880841255188
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.RewriteDeterministic.start_Good_firstHit",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.47374653816223145,
            "y": 0.2718108296394348,
            "z": 0.6435812711715698
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.RewriteDeterministic.next",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.8765156269073486,
            "y": 0.034327004104852676,
            "z": 0.5595359206199646
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.AppendixBetween.Entry",
        "kind": "structure",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.04293185472488403,
            "y": 0.9189993739128113,
            "z": 0.9330644011497498
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.AppendixBetween.ds",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.18356245756149292,
            "y": 0.6969389915466309,
            "z": 0.7246023416519165
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.AppendixBetween.wallState",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.17356978356838226,
            "y": 0.7154932022094727,
            "z": 0.7497338652610779
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.AppendixBetween.startPos",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.10164815932512283,
            "y": 0.8335443139076233,
            "z": 0.7984392642974854
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.AppendixBetween.startVel",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.09994984418153763,
            "y": 0.8370543122291565,
            "z": 0.8007226586341858
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.AppendixBetween.startState",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.562096118927002,
            "y": 0.1587982326745987,
            "z": 0.5339853167533875
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.AppendixBetween.rwWallUnionCanonicalNoEndpoint",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.7823472023010254,
            "y": 0.06020553037524223,
            "z": 0.5771744847297668
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.AppendixBetween.table",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.608924150466919,
            "y": 0.11515863984823227,
            "z": 0.4618460536003113
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.AppendixBetween.table_inside",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.673800528049469,
            "y": 0.09141264110803604,
            "z": 0.4754674732685089
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.AppendixBetween.table_boundary",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.48776310682296753,
            "y": 0.23121985793113708,
            "z": 0.5968733429908752
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.AppendixBetween.hitPoint\u2082",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.46927109360694885,
            "y": 0.23158319294452667,
            "z": 0.5797247290611267
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.AppendixBetween.hitPoint\u2082_mem_tildeWallAppendix",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.7857502698898315,
            "y": 0.05937527120113373,
            "z": 0.5749260783195496
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.AppendixBetween.hitPoint\u2082_mem_boundary",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.47822305560112,
            "y": 0.26246947050094604,
            "z": 0.6403018236160278
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.AppendixBetween.hitPoint_mem_flightRay",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.7642300128936768,
            "y": 0.06559396535158157,
            "z": 0.5270626544952393
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.AppendixBetween.no_rwWallUnionCanonicalNoEndpoint_hit_before_two",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.7288267016410828,
            "y": 0.07724654674530029,
            "z": 0.5705284476280212
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.AppendixBetween.no_boundary_hit_before_two",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.8744466304779053,
            "y": 0.03225807100534439,
            "z": 0.6156979203224182
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.AppendixBetween.start_Good_firstHit",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.46060237288475037,
            "y": 0.28020089864730835,
            "z": 0.6388444304466248
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.AppendixBetween.start_isFirstHitTime_two",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.7849685549736023,
            "y": 0.05880245566368103,
            "z": 0.5706720948219299
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.AppendixBetween.next",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.8725566267967224,
            "y": 0.042169470340013504,
            "z": 0.5226515531539917
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.AppendixBetween.afterState",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.7310107946395874,
            "y": 0.07022330164909363,
            "z": 0.4473666250705719
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.AppendixBetween.afterState_pos",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.7910898327827454,
            "y": 0.06127452850341797,
            "z": 0.4859340786933899
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.AppendixBetween.afterState_vel",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.7844498753547668,
            "y": 0.061863746494054794,
            "z": 0.4896835386753082
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.AppendixBetween.reflect_startVel_eq_neg",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.9118841290473938,
            "y": 0.003409469034522772,
            "z": 0.6968613862991333
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.AppendixBetween.after_hitPoint_eq",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.9069019556045532,
            "y": 0.003858265234157443,
            "z": 0.6658625602722168
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.AppendixBetween.startPos_mem_rwWallUnionCanonicalNoEndpoint",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.7814651727676392,
            "y": 0.059499867260456085,
            "z": 0.5876015424728394
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.AppendixBetween.after_isFirstHitTime_two",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.7416896224021912,
            "y": 0.07134227454662323,
            "z": 0.5114536881446838
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.AppendixBetween.after_Good_firstHit",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.39229047298431396,
            "y": 0.3590869605541229,
            "z": 0.6408830881118774
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.AppendixBetween.after_next",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.6571409702301025,
            "y": 0.09678639471530914,
            "z": 0.4647887945175171
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.AppendixBetween.next",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.768687903881073,
            "y": 0.06190575659275055,
            "z": 0.4344114363193512
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.AppendixBetween.next",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.35369446873664856,
            "y": 0.38925135135650635,
            "z": 0.6034935712814331
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWriteTableCanonical.boundary",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.4620126187801361,
            "y": 0.23325541615486145,
            "z": 0.5715668797492981
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWriteTableCanonical.normal",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.302537739276886,
            "y": 0.48324933648109436,
            "z": 0.6271767020225525
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWriteTableCanonical.table",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.1647127866744995,
            "y": 0.7345831990242004,
            "z": 0.7467800378799438
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWriteTableCanonical.table_boundary",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.5564491152763367,
            "y": 0.16560795903205872,
            "z": 0.5447244048118591
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWriteTableCanonical.table_inside",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.39316195249557495,
            "y": 0.35100823640823364,
            "z": 0.631676971912384
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWriteTableCanonical.CollisionState",
        "kind": "structure",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.10582868754863739,
            "y": 0.8250794410705566,
            "z": 0.7915429472923279
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWriteTableCanonical.CollisionState",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.6192334890365601,
            "y": 0.12023764103651047,
            "z": 0.5105246305465698
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWriteTableCanonical.Good",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.571107804775238,
            "y": 0.12970274686813354,
            "z": 0.4627242386341095
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWriteTableCanonical.next",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.7398528456687927,
            "y": 0.06386592239141464,
            "z": 0.3834441304206848
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWriteTableCanonical.next",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.6004507541656494,
            "y": 0.11588934063911438,
            "z": 0.4445273280143738
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.ReadOnlyWallTable.table",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.7857394814491272,
            "y": 0.06180418282747269,
            "z": 0.46484968066215515
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.ReadOnlyWallTable.table_inside",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.47102078795433044,
            "y": 0.25732696056365967,
            "z": 0.6237016320228577
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.ReadOnlyWallTable.table_boundary",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.37685808539390564,
            "y": 0.37514805793762207,
            "z": 0.6357749700546265
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.ReadOnlyWallTable.entryPos",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.3972063362598419,
            "y": 0.3465208411216736,
            "z": 0.6311516761779785
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.ReadOnlyWallTable.entryVel",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.390055388212204,
            "y": 0.3526758551597595,
            "z": 0.6306573748588562
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.ReadOnlyWallTable.entryState",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.7254424095153809,
            "y": 0.07288672775030136,
            "z": 0.4607201814651489
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.ReadOnlyWallTable.hitTime",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.5586729645729065,
            "y": 0.15583036839962006,
            "z": 0.5275295972824097
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.ReadOnlyWallTable.hitPoint",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.34447020292282104,
            "y": 0.41909459233283997,
            "z": 0.6299600005149841
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.ReadOnlyWallTable.hitVel",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.660532534122467,
            "y": 0.09534428268671036,
            "z": 0.4611656367778778
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.ReadOnlyWallTable.hitTime_pos",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.9153239727020264,
            "y": 0.0017975822556763887,
            "z": 0.6778526902198792
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.ReadOnlyWallTable.hitPoint_mem_rwWall",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.9560338258743286,
            "y": 0.016519417986273766,
            "z": 0.7547779679298401
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.ReadOnlyWallTable.hitPoint_mem_boundary",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.46838077902793884,
            "y": 0.27472421526908875,
            "z": 0.643722653388977
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.ReadOnlyWallTable.entry_Flight_to_hitPoint",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.7363221645355225,
            "y": 0.07354404777288437,
            "z": 0.5171396136283875
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.ReadOnlyWallTable.entry_Step_to_hitPoint",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.478003591299057,
            "y": 0.26298415660858154,
            "z": 0.6403571963310242
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.ReadOnlyWallTable.entry_hitPoint_unique",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.643716037273407,
            "y": 0.11356507241725922,
            "z": 0.5301278829574585
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.ReadOnlyWallTable.entry_decode_digit",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.9976362586021423,
            "y": 0.004012308083474636,
            "z": 0.8215295672416687
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.ReadOnlyWallTable.entry_Good_firstHit",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.7191299796104431,
            "y": 0.0783604308962822,
            "z": 0.5107908248901367
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.ReadOnlyTwoBounceTable.boundary",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.18307285010814667,
            "y": 0.69796222448349,
            "z": 0.7417011260986328
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.ReadOnlyTwoBounceTable.table",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.45229169726371765,
            "y": 0.27182042598724365,
            "z": 0.6125226616859436
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.ReadOnlyTwoBounceTable.table_inside",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.6192418336868286,
            "y": 0.12375205010175705,
            "z": 0.5286509990692139
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.ReadOnlyTwoBounceTable.table_boundary",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.47467663884162903,
            "y": 0.2610594928264618,
            "z": 0.6381703615188599
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.ReadOnlyTwoBounceTable.hitPoint\u2082",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.09911859035491943,
            "y": 0.8378876447677612,
            "z": 0.800534725189209
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.ReadOnlyTwoBounceTable.hitState\u2081",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.17923665046691895,
            "y": 0.7092626094818115,
            "z": 0.7505441904067993
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.ReadOnlyTwoBounceTable.hitState\u2082",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.7340764999389648,
            "y": 0.07150465995073318,
            "z": 0.47881507873535156
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.ReadOnlyTwoBounceTable.hitPoint\u2082_x",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.952553391456604,
            "y": 0.015477278269827366,
            "z": 0.742004930973053
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.ReadOnlyTwoBounceTable.hitPoint\u2082_y",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.8726269602775574,
            "y": 0.03505587577819824,
            "z": 0.5895886421203613
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.ReadOnlyTwoBounceTable.hitPoint\u2082_mem_tildeWall",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.908561646938324,
            "y": 0.017840195447206497,
            "z": 0.7142546772956848
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.ReadOnlyTwoBounceTable.hitPoint\u2082_mem_boundary",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.46834349632263184,
            "y": 0.28131103515625,
            "z": 0.651229202747345
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.ReadOnlyTwoBounceTable.entry_Step\u2081",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.8599069118499756,
            "y": 0.040187153965234756,
            "z": 0.5733360052108765
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.ReadOnlyTwoBounceTable.hitState\u2081_Step\u2082",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.9109624624252319,
            "y": 0.0022853207774460316,
            "z": 0.7012282609939575
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.ReadOnlyTwoBounceTable.entry_Reaches_hitState\u2082",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.6249819397926331,
            "y": 0.1294809877872467,
            "z": 0.5462782979011536
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.Plane.x",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.07704374194145203,
            "y": 0.8664557933807373,
            "z": 0.6895968914031982
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.Plane.y",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.12312142550945282,
            "y": 0.7759173512458801,
            "z": 0.6174713373184204
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.Plane.eX",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.4412204623222351,
            "y": 0.1079467311501503,
            "z": 0.1776726096868515
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.Plane.eY",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.4628159701824188,
            "y": 0.08560754358768463,
            "z": 0.15926411747932434
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.Plane.eX_x",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.3015274405479431,
            "y": 0.38519346714019775,
            "z": 0.3255305290222168
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.Plane.eX_y",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.11023110151290894,
            "y": 0.8052867650985718,
            "z": 0.6436881422996521
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.Plane.eY_x",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.0375497005879879,
            "y": 0.9518818259239197,
            "z": 0.8736686110496521
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.Plane.eY_y",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.014031740836799145,
            "y": 0.9495576024055481,
            "z": 0.9954281449317932
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.rwBlockLeft",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.5339851975440979,
            "y": 0.06993133574724197,
            "z": 0.09814529120922089
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.rwBlockLen",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.4661038815975189,
            "y": 0.08949679136276245,
            "z": 0.1456911563873291
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.rwBlockLen_pos",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.4976155459880829,
            "y": 0.07171999663114548,
            "z": 0.15898950397968292
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.rwBlockInterval",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.6230145692825317,
            "y": 0.06898462772369385,
            "z": 0.15031643211841583
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.rwBlockCenter",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.6149793863296509,
            "y": 0.06874378025531769,
            "z": 0.13722482323646545
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.rwWall",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.318848580121994,
            "y": 0.3423682153224945,
            "z": 0.2453884482383728
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.rwWallNormal",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.47285905480384827,
            "y": 0.08397052437067032,
            "z": 0.1817368119955063
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.shift",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.43080031871795654,
            "y": 0.13204331696033478,
            "z": 0.14540621638298035
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.tildeWall",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.7825998067855835,
            "y": 0.04717768728733063,
            "z": 0.14991499483585358
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.rewriteSlope",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.5572553277015686,
            "y": 0.07090316712856293,
            "z": 0.08580462634563446
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.rwWallRewrite",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.2950107157230377,
            "y": 0.402022123336792,
            "z": 0.33383500576019287
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.tildeWallAppendix",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.7106391787528992,
            "y": 0.06712710112333298,
            "z": 0.3485028147697449
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.mem_tildeWallAppendix_iff",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.8730074167251587,
            "y": 0.0379040390253067,
            "z": 0.5562190413475037
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.tildeWallAppendixUnionCanonical",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.6327521204948425,
            "y": 0.1143278107047081,
            "z": 0.5105342268943787
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.tildeWallAppendix_eq_image_translate_rwWall",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.476605623960495,
            "y": 0.26934173703193665,
            "z": 0.6489279270172119
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.shiftRewrite",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.6538300514221191,
            "y": 0.07455127686262131,
            "z": 0.2697775661945343
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.ds_length_eq_of_rwDigits",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.8985744714736938,
            "y": 0.020086094737052917,
            "z": 0.6026811003684998
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.rwBlockLen_eq_of_rwDigits",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.9622882008552551,
            "y": 0.01445182878524065,
            "z": 0.720423698425293
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.shiftRewrite_eq_of_rwDigits",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.9630392789840698,
            "y": 0.015219165943562984,
            "z": 0.7325051426887512
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.rewriteSlope_eq_of_rwDigits",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.987849235534668,
            "y": 0.01963384635746479,
            "z": 0.7988477349281311
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.cantorWidth_le_inv_pow_of_le_length",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.8877305388450623,
            "y": 0.023672914132475853,
            "z": 0.6182641386985779
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.cantorWidth_le_one_ninth_of_length_ge_two",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.7814086675643921,
            "y": 0.06147537752985954,
            "z": 0.5654274225234985
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.cantorWidth_le_one_twentyseven_of_length_ge_three",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.8036853075027466,
            "y": 0.05404007434844971,
            "z": 0.5876478552818298
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.rwBlockLen_le_headScale_div_ninth_of_rwDigits_neg",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.9989338517189026,
            "y": 0.005743707530200481,
            "z": 0.8254337906837463
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.rwBlockLen_le_headScale_div_twentyseven_of_rwDigits_pos",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 1.0,
            "y": 0.0,
            "z": 0.8281199932098389
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.rwBlockLen_eq_headScale_mul_inv_pow_length",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.7772620320320129,
            "y": 0.05607399716973305,
            "z": 0.5609921216964722
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.rwBlockLen_eq_headScale_mul_inv_pow_indexNat_succ",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.9534255266189575,
            "y": 0.018394501879811287,
            "z": 0.7643743753433228
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.shiftRewrite_eq_of_rwBlockLen_eq",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.6843113303184509,
            "y": 0.08877673745155334,
            "z": 0.4884319007396698
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.shiftRewrite_eq_of_length_eq",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.8445095419883728,
            "y": 0.052408237010240555,
            "z": 0.4976018965244293
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.tildeWallRewriteAppendix",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.48480474948883057,
            "y": 0.21806828677654266,
            "z": 0.5706723928451538
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.mem_tildeWallRewriteAppendix_iff",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.6726725697517395,
            "y": 0.09371474385261536,
            "z": 0.48819491267204285
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.mem_tildeWallRewriteAppendix_iff_sub_shiftRewrite",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.7827016115188599,
            "y": 0.05810302868485451,
            "z": 0.5813114643096924
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.tildeWallRewriteAppendixUnionCanonical",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.7514383792877197,
            "y": 0.06830496340990067,
            "z": 0.5066568851470947
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.tildeWallRewriteAppendix_eq_image_translate_rwWallRewrite",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.6518274545669556,
            "y": 0.11277817189693451,
            "z": 0.5420403480529785
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.tildeWallRewriteAppendix_disjoint_of_length_eq",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.7190753221511841,
            "y": 0.08139035850763321,
            "z": 0.5429303646087646
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.cantorWidth_le_one",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.8662757873535156,
            "y": 0.04641389846801758,
            "z": 0.4895918369293213
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.rwBlockLen_le_one_third",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.8733601570129395,
            "y": 0.04147205874323845,
            "z": 0.530307412147522
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.rwBlockLeft_le_one",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.9621865153312683,
            "y": 0.014326753094792366,
            "z": 0.6676807403564453
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.tildeWallRewriteAppendix_x_le_zero",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.9943512082099915,
            "y": 0.008443006314337254,
            "z": 0.8145984411239624
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.PaperReadWrite.tildeWallRewriteAppendix_one_le_x",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.9852879643440247,
            "y": 0.02021711878478527,
            "z": 0.797376811504364
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.CtrlDomain",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.6892951130867004,
            "y": 0.059832990169525146,
            "z": 0.133874773979187
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.mem_CtrlDomain_of_paperFctrl",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.44184067845344543,
            "y": 0.20148536562919617,
            "z": 0.47247782349586487
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.paperFctrl",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.4261261820793152,
            "y": 0.12974782288074493,
            "z": 0.18990668654441833
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.eq_paperFctrl",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.9070320129394531,
            "y": 0.037829797714948654,
            "z": 0.3544365465641022
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.Parabola.xShiftVec",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.0665791928768158,
            "y": 0.8944324851036072,
            "z": 0.7919370532035828
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.Parabola.xShiftVec_x",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.30003753304481506,
            "y": 0.45745569467544556,
            "z": 0.5573217868804932
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.Parabola.xShiftVec_y",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.604031503200531,
            "y": 0.07585296779870987,
            "z": 0.1926477998495102
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.Parabola.x_sub_xShiftVec",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.8816574811935425,
            "y": 0.051135800778865814,
            "z": 0.4045897126197815
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.Parabola.y_sub_xShiftVec",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.8436752557754517,
            "y": 0.06409189850091934,
            "z": 0.33014801144599915
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.Parabola.setWithFocusX",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.19725988805294037,
            "y": 0.6490784883499146,
            "z": 0.6086035370826721
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.Parabola.focusWithX",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.28476682305336,
            "y": 0.48435178399086,
            "z": 0.5603370070457458
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.Parabola.normalX",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.24208217859268188,
            "y": 0.5340451002120972,
            "z": 0.47356700897216797
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.Parabola.mem_setWithFocusX_iff",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.9228162169456482,
            "y": 0.02295200154185295,
            "z": 0.5052202343940735
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.Parabola.sub_xShiftVec_mem_setWithFocus_iff",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.884713351726532,
            "y": 0.027639662846922874,
            "z": 0.5966116189956665
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.Parabola.normalX_eq_normal_sub_xShiftVec",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.7643164992332458,
            "y": 0.06336120516061783,
            "z": 0.4490997791290283
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.Parabola.focusWithX_sub_eq_focusWith_sub",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.6421334147453308,
            "y": 0.10361520946025848,
            "z": 0.4706469476222992
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.Parabola.reflect_neg_eY_eq_smul_focusWithX_sub",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.767656683921814,
            "y": 0.06471613049507141,
            "z": 0.5003990530967712
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.Parabola.reflect_focusWithX_sub_eq_smul_neg_eY",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.7024829387664795,
            "y": 0.0814104974269867,
            "z": 0.48052582144737244
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.Parabola.pointOn",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.43206894397735596,
            "y": 0.13849163055419922,
            "z": 0.29647478461265564
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.Parabola.pointOn_mem_setWithFocusX",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.6695751547813416,
            "y": 0.08189728111028671,
            "z": 0.3732844293117523
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.Parabola.affineUpdate",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.43920615315437317,
            "y": 0.17175932228565216,
            "z": 0.40927594900131226
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.Parabola.affineUpdateInv",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.6835172772407532,
            "y": 0.06820674240589142,
            "z": 0.2725735008716583
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.Parabola.innerHit",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.851313591003418,
            "y": 0.06236913427710533,
            "z": 0.2877781391143799
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.Parabola.x_innerHit",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.6353359222412109,
            "y": 0.06971944868564606,
            "z": 0.18251559138298035
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.Parabola.innerHit_eq_pointOn",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.9742277264595032,
            "y": 0.015625758096575737,
            "z": 0.6813886165618896
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.Parabola.innerHit_mem_setWithFocusX",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.7985829710960388,
            "y": 0.06200148165225983,
            "z": 0.441647469997406
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.Parabola.affineUpdate_one_three_one",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.5608175992965698,
            "y": 0.1460278332233429,
            "z": 0.5008633732795715
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.Parabola.affineUpdateInv_zero_three_one",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.6282892823219299,
            "y": 0.11016136407852173,
            "z": 0.4780239760875702
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.Parabola.headShift_eq_affineUpdate",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.5892306566238403,
            "y": 0.1219702884554863,
            "z": 0.45486947894096375
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.ParabolicShiftCorridor.CollisionState",
        "kind": "structure",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.18428346514701843,
            "y": 0.7027488946914673,
            "z": 0.7451580762863159
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.ParabolicShiftCorridor.Good",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.6769948601722717,
            "y": 0.0708678662776947,
            "z": 0.29180222749710083
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.ParabolicShiftCorridor.nextCoord",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.5101583003997803,
            "y": 0.15765701234340668,
            "z": 0.47626569867134094
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.ParabolicShiftCorridor.nextCoord_eq_headShift",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.5930019617080688,
            "y": 0.13842064142227173,
            "z": 0.5291928648948669
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.ParabolicShiftCorridor.next",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.4817861020565033,
            "y": 0.16128095984458923,
            "z": 0.44993358850479126
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.ParabolicShiftCorridor.next",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.6685307025909424,
            "y": 0.07325063645839691,
            "z": 0.2934589087963104
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.ParabolicShiftCorridor.semiconj_headShift",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.5048311948776245,
            "y": 0.1983494609594345,
            "z": 0.561735987663269
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.ParabolicShiftCorridor.nextCoord_tau",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.3581133782863617,
            "y": 0.3863533139228821,
            "z": 0.6100326180458069
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.ParabolicShiftCorridor.Entry",
        "kind": "structure",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.02504095621407032,
            "y": 0.9302574992179871,
            "z": 0.9812278747558594
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.ParabolicShiftCorridor.Entry.hf\u2081ne",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.1832423359155655,
            "y": 0.6980571746826172,
            "z": 0.7370697855949402
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.ParabolicShiftCorridor.Entry.hf\u2082ne",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.06790068745613098,
            "y": 0.8885389566421509,
            "z": 0.8443304300308228
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.ParabolicShiftCorridor.table\u2081",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.11288657039403915,
            "y": 0.8133459091186523,
            "z": 0.7730693221092224
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.ParabolicShiftCorridor.start\u2081",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.11146503686904907,
            "y": 0.8158633708953857,
            "z": 0.7765043377876282
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.ParabolicShiftCorridor.hit\u2081",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.3524816930294037,
            "y": 0.3650069534778595,
            "z": 0.5493883490562439
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.ParabolicShiftCorridor.start\u2081_isFirstHitTime_one",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.38023504614830017,
            "y": 0.3735284209251404,
            "z": 0.6382404565811157
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.ParabolicShiftCorridor.start\u2081_Good_firstHit",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.4691348373889923,
            "y": 0.24530912935733795,
            "z": 0.597526490688324
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.ParabolicShiftCorridor.next",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.6472290754318237,
            "y": 0.07760585099458694,
            "z": 0.2748660445213318
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.ParabolicShiftCorridor.table\u2082",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.1119416356086731,
            "y": 0.8154102563858032,
            "z": 0.7752389311790466
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.ParabolicShiftCorridor.start\u2082",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.12089306861162186,
            "y": 0.8003915548324585,
            "z": 0.761989414691925
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.ParabolicShiftCorridor.hit\u2082",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.30115658044815063,
            "y": 0.46991416811943054,
            "z": 0.5937543511390686
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.ParabolicShiftCorridor.hitTime\u2082",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.6886544823646545,
            "y": 0.07189849764108658,
            "z": 0.3361399471759796
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.ParabolicShiftCorridor.hitTime\u2082_pos",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.8456485867500305,
            "y": 0.05619686841964722,
            "z": 0.4569363594055176
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.ParabolicShiftCorridor.start\u2082_vel_eq_smul_focus_sub",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.9101877808570862,
            "y": 0.0016286723548546433,
            "z": 0.684181272983551
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.ParabolicShiftCorridor.hitPoint\u2082_eq_innerHit",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.83978670835495,
            "y": 0.05336683243513107,
            "z": 0.5019872784614563
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.ParabolicShiftCorridor.hitPoint\u2082_mem_boundary",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.9866443872451782,
            "y": 0.01760481670498848,
            "z": 0.7960193157196045
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.ParabolicShiftCorridor.start\u2082_noHit_before_hitTime\u2082",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.839661717414856,
            "y": 0.048841848969459534,
            "z": 0.5470108985900879
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.ParabolicShiftCorridor.start\u2082_Good_firstHit",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.6165592670440674,
            "y": 0.12388920783996582,
            "z": 0.5168451070785522
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.ParabolicShiftCorridor.next",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.844534158706665,
            "y": 0.06238937005400658,
            "z": 0.3639495372772217
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.ParabolicShiftCorridor.next2",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.7214124202728271,
            "y": 0.06539445370435715,
            "z": 0.33957546949386597
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.ParabolicShiftCorridor.next2",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.8815198540687561,
            "y": 0.04970423877239227,
            "z": 0.4341713488101959
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.ParabolicShiftCorridor.hit\u2082_vel_is_vertical",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.7928308248519897,
            "y": 0.060962509363889694,
            "z": 0.4758886992931366
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.ParabolicShiftCorridor.x_hitPoint\u2082_eq_affineUpdate",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.9153226017951965,
            "y": 0.00376743171364069,
            "z": 0.7019860148429871
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.ParabolicShiftCorridor.x_hit\u2082_eq_affineUpdate",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.5415387749671936,
            "y": 0.17588414251804352,
            "z": 0.5525233149528503
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.ParabolicShiftCorridor.parabolaTable",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.6406674385070801,
            "y": 0.1014212965965271,
            "z": 0.4513716995716095
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.ParabolicShiftCorridor.parabolaTable_inside",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.617526650428772,
            "y": 0.11944440752267838,
            "z": 0.5020934343338013
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.ParabolicShiftCorridor.parabolaTable_boundary",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.36319833993911743,
            "y": 0.39367157220840454,
            "z": 0.6338435411453247
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.ParabolicShiftCorridor.startPos",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.1393016129732132,
            "y": 0.7720658779144287,
            "z": 0.7627941370010376
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.ParabolicShiftCorridor.startState",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.4535827040672302,
            "y": 0.22913500666618347,
            "z": 0.5467657446861267
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.ParabolicShiftCorridor.hitState\u2081",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.8478825688362122,
            "y": 0.05748618394136429,
            "z": 0.43982040882110596
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.ParabolicShiftCorridor.startStep_to_pointOn",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.7876229882240295,
            "y": 0.06170682609081268,
            "z": 0.4843177795410156
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.ParabolicShiftCorridor.hitState\u2082",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.7225151062011719,
            "y": 0.06550648808479309,
            "z": 0.35611432790756226
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.ParabolicShiftCorridor.pointOn_to_innerHit_Flight",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.6670452356338501,
            "y": 0.09776244312524796,
            "z": 0.4983973205089569
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.ParabolicShiftCorridor.pointOn_to_innerHit_Step",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.8929898142814636,
            "y": 0.01970357820391655,
            "z": 0.6255840063095093
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.ParabolicShiftCorridor.reflect_at_innerHit_is_vertical",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.6542935371398926,
            "y": 0.10868078470230103,
            "z": 0.5257164835929871
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.Plane.x",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.024929072707891464,
            "y": 0.9685224890708923,
            "z": 0.9138035178184509
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.Plane.y",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.01795131340622902,
            "y": 0.9702996611595154,
            "z": 0.9544009566307068
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.Plane.mk",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.017705343663692474,
            "y": 0.9612959027290344,
            "z": 0.975653350353241
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.Plane.eX",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.22843605279922485,
            "y": 0.5358592867851257,
            "z": 0.3908741772174835
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.Plane.eY",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.41274240612983704,
            "y": 0.14543621242046356,
            "z": 0.1907668560743332
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.Plane.mk_x",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.8577336668968201,
            "y": 0.054743628948926926,
            "z": 0.260942280292511
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.Plane.mk_y",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.7971408367156982,
            "y": 0.05503799766302109,
            "z": 0.17247368395328522
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.Plane.eX_x",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.4602636694908142,
            "y": 0.08765566349029541,
            "z": 0.1639474481344223
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.Plane.eX_y",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.2110099047422409,
            "y": 0.5941199064254761,
            "z": 0.49108967185020447
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.Plane.eY_x",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.06355833262205124,
            "y": 0.8986582159996033,
            "z": 0.7626909017562866
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.Plane.eY_y",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.01247785147279501,
            "y": 0.9542734622955322,
            "z": 1.0
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.Parabola.set",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.044621191918849945,
            "y": 0.9363793134689331,
            "z": 0.8617643117904663
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.Parabola.focus",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.3336695730686188,
            "y": 0.3233981132507324,
            "z": 0.33976683020591736
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.Parabola.setWithFocus",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.1806323379278183,
            "y": 0.6815845966339111,
            "z": 0.6200535893440247
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.Parabola.focusWith",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.1358652114868164,
            "y": 0.7639812231063843,
            "z": 0.6781489849090576
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.Parabola.shiftVec",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.3865272104740143,
            "y": 0.21695929765701294,
            "z": 0.3508506119251251
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.Parabola.normal",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.1707562357187271,
            "y": 0.6881606578826904,
            "z": 0.5872411727905273
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.Parabola.mem_setWithFocus_iff",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.5604600310325623,
            "y": 0.1318090856075287,
            "z": 0.45406365394592285
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.Parabola.mem_set_iff",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.940552830696106,
            "y": 0.021818742156028748,
            "z": 0.4912424087524414
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.Parabola.sub_shiftVec_mem_set_iff",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.7944819927215576,
            "y": 0.06244279816746712,
            "z": 0.4292617440223694
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.Parabola.inner_normal_neg_eY",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.6574118733406067,
            "y": 0.07567513734102249,
            "z": 0.28656134009361267
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.Parabola.norm_normal_sq",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.7636378407478333,
            "y": 0.05837869271636009,
            "z": 0.2781127989292145
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.Parabola.reflect_neg_eY_eq_smul_focus_sub",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.9234337210655212,
            "y": 0.004662050399929285,
            "z": 0.6694173812866211
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.Parabola.reflect_neg_eY_eq_smul_focusWith_sub",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.8980053067207336,
            "y": 0.01652766764163971,
            "z": 0.62760990858078
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.Parabola.reflect_focus_sub_eq_smul_neg_eY",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.7785104513168335,
            "y": 0.062268611043691635,
            "z": 0.4705715477466583
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.Parabola.reflect_focusWith_sub_eq_smul_neg_eY",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.746222734451294,
            "y": 0.06765253096818924,
            "z": 0.4633256793022156
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.iter",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.11238030344247818,
            "y": 0.7870653867721558,
            "z": 0.5934744477272034
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.iter",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.45891857147216797,
            "y": 0.1073213517665863,
            "z": 0.10707662999629974
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.iter",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.16762147843837738,
            "y": 0.6586939692497253,
            "z": 0.45028090476989746
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.iter",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.8126848340034485,
            "y": 0.05508346110582352,
            "z": 0.17702868580818176
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.iter",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.6633786559104919,
            "y": 0.06340465694665909,
            "z": 0.09670880436897278
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.ReturnRel",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.8157228827476501,
            "y": 0.05538301169872284,
            "z": 0.1896364837884903
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.ReturnRel",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.8366744518280029,
            "y": 0.055685341358184814,
            "z": 0.22298455238342285
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.return",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.46297624707221985,
            "y": 0.10551523417234421,
            "z": 0.09439115226268768
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.return",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.5401377081871033,
            "y": 0.07545778900384903,
            "z": 0.05421127751469612
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.return",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.34302201867103577,
            "y": 0.2856660485267639,
            "z": 0.2591845691204071
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.V",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.5107505321502686,
            "y": 0.08593787997961044,
            "z": 0.03871667757630348
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.reflect",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.5310373902320862,
            "y": 0.06835426390171051,
            "z": 0.06895900517702103
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.reflect_apply",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.6474385857582092,
            "y": 0.0661076009273529,
            "z": 0.1531381607055664
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.reflect_reflect",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.35285577178001404,
            "y": 0.2864656150341034,
            "z": 0.3572671413421631
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.norm_reflect",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.802655041217804,
            "y": 0.05466660484671593,
            "z": 0.17759494483470917
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.reflect_eq_self_iff",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.9177922010421753,
            "y": 0.033594388514757156,
            "z": 0.4326007664203644
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.reflect_normal_eq_neg",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.3360348343849182,
            "y": 0.37482309341430664,
            "z": 0.5065146684646606
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.UnitSquare.x",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.24722659587860107,
            "y": 0.5086533427238464,
            "z": 0.4171311557292938
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.UnitSquare.y",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.13032366335391998,
            "y": 0.7663096785545349,
            "z": 0.6330764889717102
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.UnitSquare.region",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.23721708357334137,
            "y": 0.5558399558067322,
            "z": 0.5198971629142761
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.UnitSquare.mem_region_iff",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.5004763603210449,
            "y": 0.14339087903499603,
            "z": 0.42770853638648987
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.UnitSquare.boundary",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.12978054583072662,
            "y": 0.7773658633232117,
            "z": 0.6932134628295898
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.UnitSquare.boundary_subset_region",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.16544100642204285,
            "y": 0.7319955229759216,
            "z": 0.7477895617485046
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.UnitSquare.convex_region",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.5464186072349548,
            "y": 0.07419034093618393,
            "z": 0.21803933382034302
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.UnitSquare.segment_subset_region",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.4956376850605011,
            "y": 0.17094939947128296,
            "z": 0.48921656608581543
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.UnitSquare.eX",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.2062067985534668,
            "y": 0.6115610599517822,
            "z": 0.5229651927947998
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.UnitSquare.eY",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.4629625380039215,
            "y": 0.08651980757713318,
            "z": 0.1707887053489685
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.UnitSquare.eX_x",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.4619162678718567,
            "y": 0.09278646111488342,
            "z": 0.19978372752666473
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.UnitSquare.eX_y",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.244329035282135,
            "y": 0.5293879508972168,
            "z": 0.4733129143714905
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.UnitSquare.eY_x",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.4843589961528778,
            "y": 0.08037680387496948,
            "z": 0.1984332799911499
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.UnitSquare.eY_y",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.45387640595436096,
            "y": 0.11299436539411545,
            "z": 0.2585834264755249
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.UnitSquare.normal",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.21037043631076813,
            "y": 0.6133376359939575,
            "z": 0.5578824877738953
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.UnitSquare.table",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.0247608982026577,
            "y": 0.9480981230735779,
            "z": 0.9703991413116455
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.UnitSquareMap.vx",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.08169106394052505,
            "y": 0.8592512607574463,
            "z": 0.7335401773452759
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.UnitSquareMap.vy",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.2671619653701782,
            "y": 0.4798632562160492,
            "z": 0.4358033835887909
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.UnitSquareMap.x_add_smul",
        "kind": "lemma",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.18768124282360077,
            "y": 0.6713801622390747,
            "z": 0.6314468383789062
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.UnitSquareMap.y_add_smul",
        "kind": "lemma",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.13307659327983856,
            "y": 0.773892343044281,
            "z": 0.7091372013092041
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.UnitSquareMap.IsCorner",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.11959131807088852,
            "y": 0.7985938787460327,
            "z": 0.7295210957527161
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.UnitSquareMap.Inward",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.05615408346056938,
            "y": 0.913334310054779,
            "z": 0.844181478023529
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.UnitSquareMap.region_of_boundary",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.47763121128082275,
            "y": 0.19266828894615173,
            "z": 0.5130635499954224
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.UnitSquareMap.x_bounds_of_boundary",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.6831509470939636,
            "y": 0.07633427530527115,
            "z": 0.3616234064102173
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.UnitSquareMap.y_bounds_of_boundary",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.36706843972206116,
            "y": 0.3572123348712921,
            "z": 0.5797925591468811
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.UnitSquareMap.timeToX",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.06642312556505203,
            "y": 0.894408106803894,
            "z": 0.8109357953071594
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.UnitSquareMap.timeToY",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.06738518923521042,
            "y": 0.8935684561729431,
            "z": 0.8067609667778015
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.UnitSquareMap.HitKind",
        "kind": "inductive",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.07869022339582443,
            "y": 0.868973433971405,
            "z": 0.7800610661506653
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.UnitSquareMap.nextHit",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.3664175271987915,
            "y": 0.2806016206741333,
            "z": 0.41454237699508667
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.UnitSquareMap.CollisionState",
        "kind": "structure",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.033014118671417236,
            "y": 0.9243037700653076,
            "z": 0.9643848538398743
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.UnitSquareMap.CollisionState",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.09309995174407959,
            "y": 0.8491830229759216,
            "z": 0.7937420010566711
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.UnitSquareMap.Good",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.20598192512989044,
            "y": 0.6276220083236694,
            "z": 0.5824195742607117
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.UnitSquareMap.eq_zero_of_x_eq_zero_of_y_eq_zero",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.416932612657547,
            "y": 0.3306465744972229,
            "z": 0.6408648490905762
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.UnitSquareMap.timeToX",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.47802218794822693,
            "y": 0.1418040245771408,
            "z": 0.39592108130455017
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.UnitSquareMap.timeToY",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.4776401221752167,
            "y": 0.1423371285200119,
            "z": 0.3967088758945465
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.UnitSquareMap.timeToX",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.7686746120452881,
            "y": 0.05710913613438606,
            "z": 0.2572501301765442
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.UnitSquareMap.timeToY",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.7682421207427979,
            "y": 0.05706961825489998,
            "z": 0.25658470392227173
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.UnitSquareMap.nextHit",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.7611236572265625,
            "y": 0.05704554170370102,
            "z": 0.25101438164711
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.UnitSquareMap.nextHit",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.7625358700752258,
            "y": 0.05667769908905029,
            "z": 0.24908261001110077
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.UnitSquareMap.x_eq_zero_or_one_of_timeToX",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.7484769821166992,
            "y": 0.06560489535331726,
            "z": 0.43857330083847046
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.UnitSquareMap.y_eq_zero_or_one_of_timeToY",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.7491118311882019,
            "y": 0.06501653790473938,
            "z": 0.4314982295036316
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.UnitSquareMap.timeToX",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.9628660082817078,
            "y": 0.01736176200211048,
            "z": 0.575309157371521
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.UnitSquareMap.timeToY",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.8616572618484497,
            "y": 0.05836420878767967,
            "z": 0.3284156918525696
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.UnitSquareMap.nextHit",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.46251094341278076,
            "y": 0.1513318568468094,
            "z": 0.39663493633270264
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.UnitSquareMap.y_mem_Icc_of_time_le_timeToY",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.9508202075958252,
            "y": 0.012733282521367073,
            "z": 0.7166101932525635
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.UnitSquareMap.x_mem_Icc_of_time_le_timeToX",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.9507352113723755,
            "y": 0.013283271342515945,
            "z": 0.7231501936912537
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.UnitSquareMap.eX_eq_single",
        "kind": "lemma",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.33772793412208557,
            "y": 0.3873679041862488,
            "z": 0.5455384850502014
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.UnitSquareMap.eY_eq_single",
        "kind": "lemma",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.3387863337993622,
            "y": 0.38436341285705566,
            "z": 0.5448614954948425
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.UnitSquareMap.inner_eX",
        "kind": "lemma",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.9376721382141113,
            "y": 0.021705271676182747,
            "z": 0.5019112825393677
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.UnitSquareMap.inner_eY",
        "kind": "lemma",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.36063137650489807,
            "y": 0.29911860823631287,
            "z": 0.4363383650779724
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.UnitSquareMap.norm_eX",
        "kind": "lemma",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.13299624621868134,
            "y": 0.7722448706626892,
            "z": 0.696126401424408
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.UnitSquareMap.norm_eY",
        "kind": "lemma",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.5508961081504822,
            "y": 0.07356946915388107,
            "z": 0.21316619217395782
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.UnitSquareMap.reflect_eX_x",
        "kind": "lemma",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.9885984659194946,
            "y": 0.02007218636572361,
            "z": 0.7911578416824341
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.UnitSquareMap.reflect_eX_y",
        "kind": "lemma",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.923723578453064,
            "y": 0.0256340354681015,
            "z": 0.4764852821826935
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.UnitSquareMap.reflect_eY_y",
        "kind": "lemma",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.9202176928520203,
            "y": 0.03723683953285217,
            "z": 0.4758870005607605
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.UnitSquareMap.reflect_eY_x",
        "kind": "lemma",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.9230483770370483,
            "y": 0.026285218074917793,
            "z": 0.4777472913265228
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.UnitSquareMap.reflect_ne_zero",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.46304887533187866,
            "y": 0.1922953575849533,
            "z": 0.4910271465778351
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.UnitSquareMap.next",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.15909282863140106,
            "y": 0.7204697728157043,
            "z": 0.6404053568840027
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.UnitSquareMap.stepRel",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.27953025698661804,
            "y": 0.5000373125076294,
            "z": 0.573639452457428
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.UnitSquareMap.next",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.6671198010444641,
            "y": 0.0660434290766716,
            "z": 0.1964178830385208
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.UnitSquareMap.pos_mem_boundary_of_nextHit_of_good",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.7748268246650696,
            "y": 0.06405257433652878,
            "z": 0.5080049633979797
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.UnitSquareMap.nextHit",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.8347129225730896,
            "y": 0.06667350977659225,
            "z": 0.2927558720111847
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.UnitSquareMap.nextHitData",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.8548992872238159,
            "y": 0.059627629816532135,
            "z": 0.3687693178653717
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.UnitSquareMap.nextHit",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.958431601524353,
            "y": 0.018496748059988022,
            "z": 0.5565941333770752
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.UnitSquareMap.nextGood",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.6412737965583801,
            "y": 0.07260703295469284,
            "z": 0.22076645493507385
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.UnitSquareMap.next",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.5508610606193542,
            "y": 0.0707506537437439,
            "z": 0.20176281034946442
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.UnitSquareMap.next",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.7650614380836487,
            "y": 0.055798523128032684,
            "z": 0.23191963136196136
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.UnitSquareMap.existsUnique_stepRel_of_good",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.46216920018196106,
            "y": 0.251066654920578,
            "z": 0.5973395705223083
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.UnitSquareMap.Reaches",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.1776467114686966,
            "y": 0.6865713000297546,
            "z": 0.6312544345855713
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.UnitSquareMap.Reaches",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.395219087600708,
            "y": 0.22724640369415283,
            "z": 0.40518736839294434
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.UnitSquareMap.Reaches",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.6880520582199097,
            "y": 0.06379992514848709,
            "z": 0.21037118136882782
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.UnitSquareMap.nextIter",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.16890913248062134,
            "y": 0.7066525220870972,
            "z": 0.6535054445266724
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.UnitSquareMap.nextIter",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.3683154284954071,
            "y": 0.280011922121048,
            "z": 0.4218529164791107
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.UnitSquareMap.nextIter",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.17910011112689972,
            "y": 0.6870478391647339,
            "z": 0.6383345127105713
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.UnitSquareMap.Reaches",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.3111885190010071,
            "y": 0.4273987114429474,
            "z": 0.5254620909690857
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.UnitSquareMap.nextIter",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.18449915945529938,
            "y": 0.6757298111915588,
            "z": 0.6276683211326599
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.UnitSquareMap.Reaches_iff_exists_nextIter",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.4556232988834381,
            "y": 0.25949278473854065,
            "z": 0.600978672504425
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.UnitSquareMap.stepRel_to_tableStep",
        "kind": "theorem",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.5082694888114929,
            "y": 0.169953390955925,
            "z": 0.501894474029541
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.WS73.DecodeGoal",
        "kind": "structure",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.4853549897670746,
            "y": 0.08080554753541946,
            "z": 0.20190247893333435
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.WS73.DecodeGoal.toLink",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.35992833971977234,
            "y": 0.30494770407676697,
            "z": 0.4434257447719574
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Billiards.WS73.DecodeGoal.paperLink",
        "kind": "def",
        "family": "Billiards/Geometry",
        "pos": {
            "x": 0.40061238408088684,
            "y": 0.22403107583522797,
            "z": 0.41984114050865173
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Computation.RealizesDetSysByFlow",
        "kind": "structure",
        "family": "Computation",
        "pos": {
            "x": 0.6436647772789001,
            "y": 0.0730324313044548,
            "z": 0.22407418489456177
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Computation.RealizesDetSysByFlow.iterate_enc",
        "kind": "theorem",
        "family": "Computation",
        "pos": {
            "x": 0.16623687744140625,
            "y": 0.7313018441200256,
            "z": 0.7524791359901428
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Computation.RealizesDetSysByFlow.stepMap",
        "kind": "def",
        "family": "Computation",
        "pos": {
            "x": 0.47458693385124207,
            "y": 0.17465601861476898,
            "z": 0.47171780467033386
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Computation.RealizesDetSysByFlow.stepMap_enc",
        "kind": "theorem",
        "family": "Computation",
        "pos": {
            "x": 0.7046558260917664,
            "y": 0.06940791010856628,
            "z": 0.3542439639568329
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Computation.RealizesDetSysByFlow.stepMap_iterate",
        "kind": "theorem",
        "family": "Computation",
        "pos": {
            "x": 0.16782411932945251,
            "y": 0.7298527359962463,
            "z": 0.754912257194519
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Computation.RealizesDetSysByFlow.enc_iterate_step",
        "kind": "theorem",
        "family": "Computation",
        "pos": {
            "x": 0.8759266138076782,
            "y": 0.03522469103336334,
            "z": 0.5454334020614624
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Computation.RealizesDetSysByFlow.isPeriodicPt_enc_of_isPeriodicPt",
        "kind": "theorem",
        "family": "Computation",
        "pos": {
            "x": 0.9548288583755493,
            "y": 0.012950439006090164,
            "z": 0.7537271976470947
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Computation.Tape",
        "kind": "def",
        "family": "Computation",
        "pos": {
            "x": 0.11731167882680893,
            "y": 0.7863487005233765,
            "z": 0.6205480694770813
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Computation.tapeUpdate",
        "kind": "def",
        "family": "Computation",
        "pos": {
            "x": 0.5799350142478943,
            "y": 0.0722537711262703,
            "z": 0.09561466425657272
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Computation.GenShiftRule",
        "kind": "structure",
        "family": "Computation",
        "pos": {
            "x": 0.29859456419944763,
            "y": 0.39569467306137085,
            "z": 0.3450200855731964
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Computation.GenShiftCfg",
        "kind": "structure",
        "family": "Computation",
        "pos": {
            "x": 0.018329648301005363,
            "y": 0.9511574506759644,
            "z": 0.9825832843780518
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Computation.GenShiftCfg.ext",
        "kind": "theorem",
        "family": "Computation",
        "pos": {
            "x": 0.13245967030525208,
            "y": 0.7694496512413025,
            "z": 0.6829803586006165
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Computation.GenShiftRule.step",
        "kind": "def",
        "family": "Computation",
        "pos": {
            "x": 0.39689749479293823,
            "y": 0.20073971152305603,
            "z": 0.3541165292263031
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Computation.genShiftDetSys",
        "kind": "def",
        "family": "Computation",
        "pos": {
            "x": 0.628254771232605,
            "y": 0.06938796490430832,
            "z": 0.1625133901834488
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Computation.genShiftHaltSys",
        "kind": "def",
        "family": "Computation",
        "pos": {
            "x": 0.5103597044944763,
            "y": 0.0722852349281311,
            "z": 0.19198068976402283
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Computation.Embed.embedTape",
        "kind": "def",
        "family": "Computation",
        "pos": {
            "x": 0.2990240752696991,
            "y": 0.416581392288208,
            "z": 0.41647329926490784
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Computation.Embed.embedCfg",
        "kind": "def",
        "family": "Computation",
        "pos": {
            "x": 0.1340489685535431,
            "y": 0.7673793435096741,
            "z": 0.6729390025138855
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Computation.Embed.rule",
        "kind": "def",
        "family": "Computation",
        "pos": {
            "x": 0.20929668843746185,
            "y": 0.601100742816925,
            "z": 0.5052616000175476
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Computation.Embed.haltsCfg",
        "kind": "def",
        "family": "Computation",
        "pos": {
            "x": 0.3897218108177185,
            "y": 0.20621830224990845,
            "z": 0.3401116132736206
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Computation.Embed.sys",
        "kind": "def",
        "family": "Computation",
        "pos": {
            "x": 0.3081778883934021,
            "y": 0.370551735162735,
            "z": 0.3193947970867157
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Computation.Embed.Rel",
        "kind": "def",
        "family": "Computation",
        "pos": {
            "x": 0.31831586360931396,
            "y": 0.35077592730522156,
            "z": 0.32277020812034607
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Computation.Embed.step_embedCfg",
        "kind": "theorem",
        "family": "Computation",
        "pos": {
            "x": 0.17673881351947784,
            "y": 0.6921036243438721,
            "z": 0.6313503384590149
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Computation.Embed.sim_step",
        "kind": "theorem",
        "family": "Computation",
        "pos": {
            "x": 0.5994423031806946,
            "y": 0.07291339337825775,
            "z": 0.15757469832897186
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Computation.Embed.sim_halts",
        "kind": "theorem",
        "family": "Computation",
        "pos": {
            "x": 0.17653144896030426,
            "y": 0.6845455765724182,
            "z": 0.6089341640472412
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Computation.GenShiftCtrlRule",
        "kind": "structure",
        "family": "Computation",
        "pos": {
            "x": 0.6379302144050598,
            "y": 0.07048746198415756,
            "z": 0.19031386077404022
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Computation.GenShiftCtrlCfg",
        "kind": "structure",
        "family": "Computation",
        "pos": {
            "x": 0.04533617943525314,
            "y": 0.9365648627281189,
            "z": 0.8623233437538147
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Computation.GenShiftCtrlCfg.ext",
        "kind": "theorem",
        "family": "Computation",
        "pos": {
            "x": 0.28389090299606323,
            "y": 0.49424776434898376,
            "z": 0.5788280963897705
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Computation.GenShiftCtrlRule.step",
        "kind": "def",
        "family": "Computation",
        "pos": {
            "x": 0.3580845892429352,
            "y": 0.31534796953201294,
            "z": 0.4602709114551544
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Computation.genShiftCtrlDetSys",
        "kind": "def",
        "family": "Computation",
        "pos": {
            "x": 0.8445296883583069,
            "y": 0.06186259537935257,
            "z": 0.2890515923500061
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Computation.genShiftCtrlHaltSys",
        "kind": "def",
        "family": "Computation",
        "pos": {
            "x": 0.6460000872612,
            "y": 0.07164796441793442,
            "z": 0.22183802723884583
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Computation.ControlledEmbed.embedTape",
        "kind": "def",
        "family": "Computation",
        "pos": {
            "x": 0.3416219651699066,
            "y": 0.38352450728416443,
            "z": 0.5544614195823669
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Computation.ControlledEmbed.embedCfg",
        "kind": "def",
        "family": "Computation",
        "pos": {
            "x": 0.3201022744178772,
            "y": 0.4287106692790985,
            "z": 0.5730620622634888
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Computation.ControlledEmbed.rule",
        "kind": "def",
        "family": "Computation",
        "pos": {
            "x": 0.47562527656555176,
            "y": 0.14782723784446716,
            "z": 0.40994885563850403
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Computation.ControlledEmbed.haltsCfg",
        "kind": "def",
        "family": "Computation",
        "pos": {
            "x": 0.6642493009567261,
            "y": 0.07296298444271088,
            "z": 0.27919963002204895
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Computation.ControlledEmbed.sys",
        "kind": "def",
        "family": "Computation",
        "pos": {
            "x": 0.3565386235713959,
            "y": 0.30673885345458984,
            "z": 0.4287247061729431
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Computation.ControlledEmbed.Rel",
        "kind": "def",
        "family": "Computation",
        "pos": {
            "x": 0.35839855670928955,
            "y": 0.3013603985309601,
            "z": 0.42665940523147583
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Computation.ControlledEmbed.step_embedCfg",
        "kind": "theorem",
        "family": "Computation",
        "pos": {
            "x": 0.36172881722450256,
            "y": 0.36459603905677795,
            "z": 0.574871301651001
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Computation.ControlledEmbed.sim_step",
        "kind": "theorem",
        "family": "Computation",
        "pos": {
            "x": 0.638222336769104,
            "y": 0.07569700479507446,
            "z": 0.2435111552476883
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Computation.ControlledEmbed.sim_halts",
        "kind": "theorem",
        "family": "Computation",
        "pos": {
            "x": 0.18516004085540771,
            "y": 0.6795956492424011,
            "z": 0.6592015624046326
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Computation.Embed.iterate_step_embedCfg",
        "kind": "theorem",
        "family": "Computation",
        "pos": {
            "x": 0.3256033658981323,
            "y": 0.42946380376815796,
            "z": 0.5940319299697876
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Computation.DetSys",
        "kind": "structure",
        "family": "Computation",
        "pos": {
            "x": 0.016113242134451866,
            "y": 0.9519370794296265,
            "z": 0.9867457747459412
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Computation.DetSys.stepN",
        "kind": "def",
        "family": "Computation",
        "pos": {
            "x": 0.19744864106178284,
            "y": 0.6305422782897949,
            "z": 0.5367452502250671
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Computation.DetSys.stepN_zero",
        "kind": "theorem",
        "family": "Computation",
        "pos": {
            "x": 0.3502886891365051,
            "y": 0.3127336800098419,
            "z": 0.4154966473579407
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Computation.DetSys.stepN_succ",
        "kind": "theorem",
        "family": "Computation",
        "pos": {
            "x": 0.606728196144104,
            "y": 0.0702655091881752,
            "z": 0.17931409180164337
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Computation.DetSys.stepN_eq_iterate",
        "kind": "theorem",
        "family": "Computation",
        "pos": {
            "x": 0.16714854538440704,
            "y": 0.7150155305862427,
            "z": 0.6800059080123901
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Computation.DetSys.IsReversible",
        "kind": "def",
        "family": "Computation",
        "pos": {
            "x": 0.08436620980501175,
            "y": 0.8589222431182861,
            "z": 0.7601712942123413
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Computation.HaltSys",
        "kind": "structure",
        "family": "Computation",
        "pos": {
            "x": 0.034919898957014084,
            "y": 0.9577928185462952,
            "z": 0.8796090483665466
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Computation.HaltSys.stepN",
        "kind": "def",
        "family": "Computation",
        "pos": {
            "x": 0.15292643010616302,
            "y": 0.7287652492523193,
            "z": 0.6308121681213379
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Computation.HaltSys.stepN_zero",
        "kind": "theorem",
        "family": "Computation",
        "pos": {
            "x": 0.35577303171157837,
            "y": 0.3020155131816864,
            "z": 0.41586506366729736
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Computation.HaltSys.stepN_succ",
        "kind": "theorem",
        "family": "Computation",
        "pos": {
            "x": 0.6068805456161499,
            "y": 0.07563062757253647,
            "z": 0.1919029802083969
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Computation.HaltSys.stepN_eq_iterate",
        "kind": "theorem",
        "family": "Computation",
        "pos": {
            "x": 0.8370230793952942,
            "y": 0.0668579563498497,
            "z": 0.31975647807121277
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Computation.HaltSys.haltsAt",
        "kind": "def",
        "family": "Computation",
        "pos": {
            "x": 0.42426598072052,
            "y": 0.14925621449947357,
            "z": 0.3108428120613098
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Computation.HaltSys.haltsFrom",
        "kind": "def",
        "family": "Computation",
        "pos": {
            "x": 0.027052851393818855,
            "y": 0.9340493083000183,
            "z": 0.9763087630271912
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Computation.BennettConstruction",
        "kind": "structure",
        "family": "Computation",
        "pos": {
            "x": 0.292752742767334,
            "y": 0.4691067337989807,
            "z": 0.5568167567253113
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Computation.HasBennettConstruction",
        "kind": "class",
        "family": "Computation",
        "pos": {
            "x": 0.11915350705385208,
            "y": 0.8017798662185669,
            "z": 0.7564168572425842
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Demo.succRel",
        "kind": "def",
        "family": "Other",
        "pos": {
            "x": 0.08065441995859146,
            "y": 0.845564067363739,
            "z": 0.6174777746200562
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Demo.succ2Rel",
        "kind": "def",
        "family": "Other",
        "pos": {
            "x": 0.19580206274986267,
            "y": 0.6010032892227173,
            "z": 0.4151414632797241
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Demo.succ2Rel_spec",
        "kind": "theorem",
        "family": "Other",
        "pos": {
            "x": 0.21412289142608643,
            "y": 0.5758810639381409,
            "z": 0.44439294934272766
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Demo.main",
        "kind": "def",
        "family": "Other",
        "pos": {
            "x": 0.7859588265419006,
            "y": 0.049654364585876465,
            "z": 0.13603575527668
        }
    },
    {
        "name": "main",
        "kind": "def",
        "family": "Other",
        "pos": {
            "x": 0.0014237508876249194,
            "y": 0.9804221987724304,
            "z": 0.9881425499916077
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Discrete.showState",
        "kind": "def",
        "family": "Discrete",
        "pos": {
            "x": 0.34031254053115845,
            "y": 0.2920215129852295,
            "z": 0.269382119178772
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Discrete.printPrefix",
        "kind": "def",
        "family": "Discrete",
        "pos": {
            "x": 0.3888561427593231,
            "y": 0.1851387917995453,
            "z": 0.25268781185150146
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Discrete.main",
        "kind": "def",
        "family": "Discrete",
        "pos": {
            "x": 0.49751415848731995,
            "y": 0.08719737082719803,
            "z": 0.06174508109688759
        }
    },
    {
        "name": "main",
        "kind": "def",
        "family": "Discrete",
        "pos": {
            "x": 0.0021175809670239687,
            "y": 0.977110743522644,
            "z": 0.9864020347595215
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Discrete.stepFlow",
        "kind": "def",
        "family": "Discrete",
        "pos": {
            "x": 0.7683437466621399,
            "y": 0.050135768949985504,
            "z": 0.13100437819957733
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Discrete.stepFlow_apply",
        "kind": "theorem",
        "family": "Discrete",
        "pos": {
            "x": 0.14440234005451202,
            "y": 0.7411378026008606,
            "z": 0.6295406222343445
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Discrete.cycleSet",
        "kind": "def",
        "family": "Discrete",
        "pos": {
            "x": 0.08687379956245422,
            "y": 0.8417956829071045,
            "z": 0.6534133553504944
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Discrete.ReachesCycle",
        "kind": "def",
        "family": "Discrete",
        "pos": {
            "x": 0.33016952872276306,
            "y": 0.32541677355766296,
            "z": 0.3244377374649048
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Discrete.reachesCycle_of_reachesPeriod2",
        "kind": "theorem",
        "family": "Discrete",
        "pos": {
            "x": 0.360447496175766,
            "y": 0.36213135719299316,
            "z": 0.5700876712799072
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Discrete.reachesPeriod2_of_reachesCycle",
        "kind": "theorem",
        "family": "Discrete",
        "pos": {
            "x": 0.3609737157821655,
            "y": 0.35999202728271484,
            "z": 0.5675072073936462
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Discrete.reachesCycle_iff_halts",
        "kind": "theorem",
        "family": "Discrete",
        "pos": {
            "x": 0.4025142788887024,
            "y": 0.21905411779880524,
            "z": 0.41161587834358215
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Discrete.reachingRel_cycle",
        "kind": "def",
        "family": "Discrete",
        "pos": {
            "x": 0.9392251372337341,
            "y": 0.023104222491383553,
            "z": 0.4793837368488312
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Discrete.reachesCycle_iff_exists_reachingRel",
        "kind": "theorem",
        "family": "Discrete",
        "pos": {
            "x": 0.5606280565261841,
            "y": 0.1418105512857437,
            "z": 0.49313968420028687
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Discrete.ShiftPeriodic.shiftStep",
        "kind": "def",
        "family": "Discrete",
        "pos": {
            "x": 0.555558979511261,
            "y": 0.0723719447851181,
            "z": 0.2077232301235199
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Discrete.ShiftPeriodic.startCfg",
        "kind": "def",
        "family": "Discrete",
        "pos": {
            "x": 0.4186708629131317,
            "y": 0.1979517936706543,
            "z": 0.41628554463386536
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Discrete.ShiftPeriodic.ReachesPeriod2Shift",
        "kind": "def",
        "family": "Discrete",
        "pos": {
            "x": 0.6128359436988831,
            "y": 0.10832368582487106,
            "z": 0.4307500123977661
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Discrete.ShiftPeriodic.reachesPeriod2Shift_iff_reachesPeriod2",
        "kind": "theorem",
        "family": "Discrete",
        "pos": {
            "x": 0.6216481924057007,
            "y": 0.12380863726139069,
            "z": 0.5292208194732666
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Discrete.ShiftPeriodic.reachesPeriod2Shift_iff_halting",
        "kind": "theorem",
        "family": "Discrete",
        "pos": {
            "x": 0.6285991668701172,
            "y": 0.11090894043445587,
            "z": 0.49164050817489624
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Discrete.ShiftPeriodic.haltingReducesToReachesPeriod2Shift",
        "kind": "def",
        "family": "Discrete",
        "pos": {
            "x": 0.6219537258148193,
            "y": 0.1193874329328537,
            "z": 0.5175265073776245
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Discrete.ShiftPeriodic.not_computable_reachesPeriod2Shift",
        "kind": "theorem",
        "family": "Discrete",
        "pos": {
            "x": 0.4425903558731079,
            "y": 0.29269254207611084,
            "z": 0.6293380856513977
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Discrete.HaltSysBridge.haltsState",
        "kind": "def",
        "family": "Computation",
        "pos": {
            "x": 0.28229716420173645,
            "y": 0.5020807385444641,
            "z": 0.5932260751724243
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Discrete.HaltSysBridge.sys",
        "kind": "def",
        "family": "Computation",
        "pos": {
            "x": 0.3645874857902527,
            "y": 0.264319509267807,
            "z": 0.36252278089523315
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Discrete.HaltSysBridge.haltsState_iff_inr",
        "kind": "theorem",
        "family": "Computation",
        "pos": {
            "x": 0.5198803544044495,
            "y": 0.15138116478919983,
            "z": 0.4722864031791687
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Discrete.HaltSysBridge.haltsFrom_start_iff_reachesPeriod2",
        "kind": "theorem",
        "family": "Computation",
        "pos": {
            "x": 0.735537588596344,
            "y": 0.07019385695457458,
            "z": 0.4790753722190857
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Discrete.HaltSysBridge.haltsFrom_start_iff_halting",
        "kind": "theorem",
        "family": "Computation",
        "pos": {
            "x": 0.8818443417549133,
            "y": 0.03182385489344597,
            "z": 0.570048987865448
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Discrete.HaltSysBridge.simRel",
        "kind": "def",
        "family": "Computation",
        "pos": {
            "x": 0.9628536105155945,
            "y": 0.017295675352215767,
            "z": 0.5720894932746887
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Discrete.HaltSysBridge.simRel_step",
        "kind": "theorem",
        "family": "Computation",
        "pos": {
            "x": 0.7644262909889221,
            "y": 0.05451956391334534,
            "z": 0.2726784646511078
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Discrete.HaltSysBridge.simRel_halts",
        "kind": "theorem",
        "family": "Computation",
        "pos": {
            "x": 0.6425309777259827,
            "y": 0.07402114570140839,
            "z": 0.241681769490242
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Discrete.HaltSysBridge.simRelCtrl",
        "kind": "def",
        "family": "Computation",
        "pos": {
            "x": 0.8445041179656982,
            "y": 0.06389402598142624,
            "z": 0.3198358416557312
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Discrete.HaltSysBridge.simRelCtrl_step",
        "kind": "theorem",
        "family": "Computation",
        "pos": {
            "x": 0.9173064827919006,
            "y": 0.02632972225546837,
            "z": 0.4818499684333801
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Discrete.HaltSysBridge.simRelCtrl_halts",
        "kind": "theorem",
        "family": "Computation",
        "pos": {
            "x": 0.8308957815170288,
            "y": 0.06522420048713684,
            "z": 0.3594648838043213
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Discrete.State",
        "kind": "def",
        "family": "Discrete",
        "pos": {
            "x": 0.21034660935401917,
            "y": 0.5615128874778748,
            "z": 0.36502066254615784
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Discrete.step",
        "kind": "def",
        "family": "Discrete",
        "pos": {
            "x": 0.19473832845687866,
            "y": 0.6021844148635864,
            "z": 0.414829283952713
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Discrete.start",
        "kind": "def",
        "family": "Discrete",
        "pos": {
            "x": 0.042380500584840775,
            "y": 0.9454509615898132,
            "z": 0.7881597280502319
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Discrete.HitsAt",
        "kind": "def",
        "family": "Discrete",
        "pos": {
            "x": 0.256944864988327,
            "y": 0.47163259983062744,
            "z": 0.32586920261383057
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Discrete.not_hitsAt_iff_evaln_eq_none",
        "kind": "theorem",
        "family": "Discrete",
        "pos": {
            "x": 0.29575157165527344,
            "y": 0.4847134053707123,
            "z": 0.6069837212562561
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Discrete.iterate_step_inl_of_noHitsBefore",
        "kind": "theorem",
        "family": "Discrete",
        "pos": {
            "x": 0.7539317011833191,
            "y": 0.06140526384115219,
            "z": 0.37864500284194946
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Discrete.halts_iff_exists_evaln",
        "kind": "theorem",
        "family": "Discrete",
        "pos": {
            "x": 0.4279561936855316,
            "y": 0.19317205250263214,
            "z": 0.4289684593677521
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Discrete.ReachesPeriod2",
        "kind": "def",
        "family": "Discrete",
        "pos": {
            "x": 0.7007408738136292,
            "y": 0.05743362382054329,
            "z": 0.154092937707901
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Discrete.periodic2_inr",
        "kind": "theorem",
        "family": "Discrete",
        "pos": {
            "x": 0.567622721195221,
            "y": 0.073012575507164,
            "z": 0.08169786632061005
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Discrete.not_periodic2_inl",
        "kind": "theorem",
        "family": "Discrete",
        "pos": {
            "x": 0.6812454462051392,
            "y": 0.06189415231347084,
            "z": 0.16561976075172424
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Discrete.reachesPeriod2_of_halting",
        "kind": "theorem",
        "family": "Discrete",
        "pos": {
            "x": 0.6726620197296143,
            "y": 0.07020661234855652,
            "z": 0.2743723392486572
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Discrete.halting_of_reachesPeriod2",
        "kind": "theorem",
        "family": "Discrete",
        "pos": {
            "x": 0.6840421557426453,
            "y": 0.06776753813028336,
            "z": 0.2692336142063141
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Discrete.reachesPeriod2_iff_halts",
        "kind": "theorem",
        "family": "Discrete",
        "pos": {
            "x": 0.4554934799671173,
            "y": 0.1708187609910965,
            "z": 0.43393099308013916
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Discrete.haltingReducesToReachesPeriod2",
        "kind": "def",
        "family": "Discrete",
        "pos": {
            "x": 0.5263015627861023,
            "y": 0.1422717124223709,
            "z": 0.4575190246105194
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Discrete.not_computable_reachesPeriod2",
        "kind": "theorem",
        "family": "Discrete",
        "pos": {
            "x": 0.476703405380249,
            "y": 0.16867022216320038,
            "z": 0.45968788862228394
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Dynamics.PartialFlow",
        "kind": "structure",
        "family": "Other",
        "pos": {
            "x": 0.8201065063476562,
            "y": 0.057936325669288635,
            "z": 0.199956014752388
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.PartialFlowDemo.addFlow",
        "kind": "def",
        "family": "Other",
        "pos": {
            "x": 0.3504972457885742,
            "y": 0.2849481999874115,
            "z": 0.33114829659461975
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.PartialFlowDemo.main",
        "kind": "def",
        "family": "Other",
        "pos": {
            "x": 0.4260351359844208,
            "y": 0.12611716985702515,
            "z": 0.19549979269504547
        }
    },
    {
        "name": "main",
        "kind": "def",
        "family": "Other",
        "pos": {
            "x": 0.0012578830355778337,
            "y": 0.9895066618919373,
            "z": 0.9759393930435181
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Dynamics.PartialFlow.ofFlow",
        "kind": "def",
        "family": "Other",
        "pos": {
            "x": 0.13936661183834076,
            "y": 0.7548717856407166,
            "z": 0.661908745765686
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Dynamics.PartialFlow.ofFlow_dom",
        "kind": "theorem",
        "family": "Other",
        "pos": {
            "x": 0.39678218960762024,
            "y": 0.2150890976190567,
            "z": 0.3873245120048523
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Dynamics.PartialFlow.ofFlow_map",
        "kind": "theorem",
        "family": "Other",
        "pos": {
            "x": 0.06559531390666962,
            "y": 0.8971154689788818,
            "z": 0.8125845193862915
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.External.TKFTUniversalityClaim",
        "kind": "structure",
        "family": "External",
        "pos": {
            "x": 0.6420778036117554,
            "y": 0.07100972533226013,
            "z": 0.20866794884204865
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.External.BilliardsComputesClaim",
        "kind": "structure",
        "family": "External",
        "pos": {
            "x": 0.8572795391082764,
            "y": 0.059475984424352646,
            "z": 0.3236770033836365
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.External.EulerTuringCompleteClaim",
        "kind": "structure",
        "family": "External",
        "pos": {
            "x": 0.9737224578857422,
            "y": 0.015753615647554398,
            "z": 0.6667152047157288
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.External.NavierStokesTuringCompleteClaim",
        "kind": "structure",
        "family": "External",
        "pos": {
            "x": 0.3620492219924927,
            "y": 0.3620133697986603,
            "z": 0.5699887275695801
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.External.not_computable_of_billiardsComputes",
        "kind": "theorem",
        "family": "External",
        "pos": {
            "x": 0.9940797090530396,
            "y": 0.0019545026589185,
            "z": 0.8116193413734436
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.External.not_computable_of_eulerTuringComplete",
        "kind": "theorem",
        "family": "External",
        "pos": {
            "x": 0.9990919828414917,
            "y": 0.0022190420422703028,
            "z": 0.8251427412033081
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.External.not_computable_of_navierStokesTuringComplete",
        "kind": "theorem",
        "family": "External",
        "pos": {
            "x": 0.7815704941749573,
            "y": 0.06225335970520973,
            "z": 0.48320239782333374
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.External.TKFTReaching",
        "kind": "structure",
        "family": "External",
        "pos": {
            "x": 0.8985354900360107,
            "y": 0.04281988739967346,
            "z": 0.3325422704219818
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.External.TKFTReachingFunctional",
        "kind": "structure",
        "family": "External",
        "pos": {
            "x": 0.9262105226516724,
            "y": 0.02540460228919983,
            "z": 0.46414172649383545
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.External.TKFTConstruction",
        "kind": "def",
        "family": "External",
        "pos": {
            "x": 0.694310188293457,
            "y": 0.061357878148555756,
            "z": 0.17244116961956024
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.External.reachingImage",
        "kind": "def",
        "family": "External",
        "pos": {
            "x": 0.7889096736907959,
            "y": 0.052810803055763245,
            "z": 0.1653820127248764
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.External.reachingFunction",
        "kind": "def",
        "family": "External",
        "pos": {
            "x": 0.773517370223999,
            "y": 0.053463421761989594,
            "z": 0.17976795136928558
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.External.reachingFunction_spec",
        "kind": "theorem",
        "family": "External",
        "pos": {
            "x": 0.6478294730186462,
            "y": 0.06987656652927399,
            "z": 0.2117053121328354
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.External.HaltingToPredicate",
        "kind": "structure",
        "family": "External",
        "pos": {
            "x": 0.8791482448577881,
            "y": 0.05106233060359955,
            "z": 0.33775144815444946
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.External.HaltingReduction",
        "kind": "def",
        "family": "External",
        "pos": {
            "x": 0.935876190662384,
            "y": 0.026780148968100548,
            "z": 0.45751795172691345
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.External.not_computable_of_haltingReduction",
        "kind": "theorem",
        "family": "External",
        "pos": {
            "x": 0.5615236163139343,
            "y": 0.1375773400068283,
            "z": 0.4792276620864868
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.FixedPoint.unionNucleus",
        "kind": "def",
        "family": "FixedPoint",
        "pos": {
            "x": 0.12221629172563553,
            "y": 0.7851406931877136,
            "z": 0.652592122554779
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.FixedPoint.isFixedPoint_unionNucleus_iff",
        "kind": "theorem",
        "family": "FixedPoint",
        "pos": {
            "x": 0.3418111503124237,
            "y": 0.3968132436275482,
            "z": 0.5806500911712646
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Flow.FlowTraj",
        "kind": "def",
        "family": "FixedPoint",
        "pos": {
            "x": 0.4889090657234192,
            "y": 0.09020993113517761,
            "z": 0.07371960580348969
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Flow.periodicNucleus",
        "kind": "def",
        "family": "FixedPoint",
        "pos": {
            "x": 0.7768429517745972,
            "y": 0.054499804973602295,
            "z": 0.14406532049179077
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Flow.periodicNucleus_eq_flowNucleusOsc",
        "kind": "theorem",
        "family": "FixedPoint",
        "pos": {
            "x": 0.1747550517320633,
            "y": 0.7065569758415222,
            "z": 0.6965894103050232
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Fluids.ContactLinear",
        "kind": "structure",
        "family": "Fluids",
        "pos": {
            "x": 0.20846930146217346,
            "y": 0.6011208891868591,
            "z": 0.4990604817867279
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Fluids.ContactLinear.reeb_unique",
        "kind": "theorem",
        "family": "Fluids",
        "pos": {
            "x": 0.8851326107978821,
            "y": 0.05074167996644974,
            "z": 0.39943185448646545
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Fluids.ContactLinear.reebFlow",
        "kind": "def",
        "family": "Fluids",
        "pos": {
            "x": 0.48492321372032166,
            "y": 0.09841650724411011,
            "z": 0.2673620581626892
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Fluids.ContactLinear.reebFlow_apply",
        "kind": "theorem",
        "family": "Fluids",
        "pos": {
            "x": 0.07732351869344711,
            "y": 0.8757390379905701,
            "z": 0.8090064525604248
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Fluids.VectorCalculus.R3.V",
        "kind": "def",
        "family": "Fluids",
        "pos": {
            "x": 0.3901185095310211,
            "y": 0.20376992225646973,
            "z": 0.333556592464447
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Fluids.VectorCalculus.R3.basisVec",
        "kind": "def",
        "family": "Fluids",
        "pos": {
            "x": 0.41275033354759216,
            "y": 0.21205274760723114,
            "z": 0.4276047945022583
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Fluids.VectorCalculus.R3.dcoord",
        "kind": "def",
        "family": "Fluids",
        "pos": {
            "x": 0.23680436611175537,
            "y": 0.578554093837738,
            "z": 0.5903831720352173
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Fluids.VectorCalculus.R3.basisVec_apply_self",
        "kind": "theorem",
        "family": "Fluids",
        "pos": {
            "x": 0.33956778049468994,
            "y": 0.4137290120124817,
            "z": 0.6085066199302673
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Fluids.VectorCalculus.R3.basisVec_apply_ne",
        "kind": "theorem",
        "family": "Fluids",
        "pos": {
            "x": 0.4759545624256134,
            "y": 0.192764014005661,
            "z": 0.5086773633956909
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Fluids.VectorCalculus.R3.i0",
        "kind": "def",
        "family": "Fluids",
        "pos": {
            "x": 0.4076690375804901,
            "y": 0.1656096875667572,
            "z": 0.3012710511684418
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Fluids.VectorCalculus.R3.i1",
        "kind": "def",
        "family": "Fluids",
        "pos": {
            "x": 0.2757481038570404,
            "y": 0.486213356256485,
            "z": 0.5164922475814819
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Fluids.VectorCalculus.R3.i2",
        "kind": "def",
        "family": "Fluids",
        "pos": {
            "x": 0.3538104295730591,
            "y": 0.2945299446582794,
            "z": 0.3860183358192444
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Fluids.VectorCalculus.R3.curl",
        "kind": "def",
        "family": "Fluids",
        "pos": {
            "x": 0.5004447102546692,
            "y": 0.08338917046785355,
            "z": 0.23447200655937195
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Fluids.VectorCalculus.R3.curl_const",
        "kind": "theorem",
        "family": "Fluids",
        "pos": {
            "x": 0.47412946820259094,
            "y": 0.15690156817436218,
            "z": 0.430009663105011
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Fluids.VectorCalculus.R3.IsBeltrami",
        "kind": "def",
        "family": "Fluids",
        "pos": {
            "x": 0.03525738790631294,
            "y": 0.9249683022499084,
            "z": 0.9579359889030457
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Fluids.VectorCalculus.R3.i0",
        "kind": "def",
        "family": "Fluids",
        "pos": {
            "x": 0.4276456832885742,
            "y": 0.14370203018188477,
            "z": 0.3015701472759247
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Fluids.VectorCalculus.R3.i1",
        "kind": "def",
        "family": "Fluids",
        "pos": {
            "x": 0.45606398582458496,
            "y": 0.11557204276323318,
            "z": 0.2798309922218323
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Fluids.VectorCalculus.R3.i2",
        "kind": "def",
        "family": "Fluids",
        "pos": {
            "x": 0.274464875459671,
            "y": 0.4782405495643616,
            "z": 0.4810270369052887
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Fluids.VectorCalculus.R3.grad",
        "kind": "def",
        "family": "Fluids",
        "pos": {
            "x": 0.4848521053791046,
            "y": 0.09777606278657913,
            "z": 0.26592281460762024
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Fluids.VectorCalculus.R3.div",
        "kind": "def",
        "family": "Fluids",
        "pos": {
            "x": 0.3228939473628998,
            "y": 0.3769037425518036,
            "z": 0.44372910261154175
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Fluids.VectorCalculus.R3.grad_const",
        "kind": "theorem",
        "family": "Fluids",
        "pos": {
            "x": 0.3519646227359772,
            "y": 0.3455432653427124,
            "z": 0.5074043273925781
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Fluids.VectorCalculus.R3.div_const",
        "kind": "theorem",
        "family": "Fluids",
        "pos": {
            "x": 0.4825915992259979,
            "y": 0.14738908410072327,
            "z": 0.41734305024147034
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Fluids.VectorCalculus.R3.IsEulerSteadyBernoulli",
        "kind": "def",
        "family": "Fluids",
        "pos": {
            "x": 0.45425188541412354,
            "y": 0.24476642906665802,
            "z": 0.5747167468070984
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Fluids.VectorCalculus.R3.eulerSteadyBernoulli_const",
        "kind": "theorem",
        "family": "Fluids",
        "pos": {
            "x": 0.5330139994621277,
            "y": 0.17960552871227264,
            "z": 0.55036461353302
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Fluids.VectorCalculus.R3.eulerSteadyBernoulli_const_of_beltrami",
        "kind": "theorem",
        "family": "Fluids",
        "pos": {
            "x": 0.6587357521057129,
            "y": 0.10461562871932983,
            "z": 0.5194756984710693
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Geometry.Contact.eval1",
        "kind": "def",
        "family": "Fluids",
        "pos": {
            "x": 0.919028639793396,
            "y": 0.03378075361251831,
            "z": 0.37800249457359314
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Geometry.Contact.eval_d",
        "kind": "def",
        "family": "Fluids",
        "pos": {
            "x": 0.7064580917358398,
            "y": 0.05810360237956047,
            "z": 0.1530236005783081
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Geometry.Contact.eval1_apply",
        "kind": "theorem",
        "family": "Fluids",
        "pos": {
            "x": 0.6349818706512451,
            "y": 0.06909330189228058,
            "z": 0.17437994480133057
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Geometry.Contact.vecCons_eq_vec2",
        "kind": "theorem",
        "family": "Fluids",
        "pos": {
            "x": 0.11941657960414886,
            "y": 0.7982186079025269,
            "z": 0.7256736755371094
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Geometry.Contact.eval_d_add_left",
        "kind": "theorem",
        "family": "Fluids",
        "pos": {
            "x": 0.9656707048416138,
            "y": 0.020786480978131294,
            "z": 0.5891767740249634
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Geometry.Contact.eval_d_smul_left",
        "kind": "theorem",
        "family": "Fluids",
        "pos": {
            "x": 0.973895251750946,
            "y": 0.015786418691277504,
            "z": 0.6672561168670654
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Geometry.Contact.NondegKer",
        "kind": "def",
        "family": "Fluids",
        "pos": {
            "x": 0.7356544137001038,
            "y": 0.0551031269133091,
            "z": 0.15698456764221191
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Geometry.Contact.IsReebAt",
        "kind": "def",
        "family": "Fluids",
        "pos": {
            "x": 0.8095128536224365,
            "y": 0.05783896893262863,
            "z": 0.21974904835224152
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Geometry.Contact.reeb_unique_of_nondegKer",
        "kind": "theorem",
        "family": "Fluids",
        "pos": {
            "x": 0.748686671257019,
            "y": 0.06613685190677643,
            "z": 0.3849039673805237
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Geometry.Forms.Form",
        "kind": "def",
        "family": "Geometry",
        "pos": {
            "x": 0.5363953113555908,
            "y": 0.07373809069395065,
            "z": 0.0726865604519844
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Geometry.Forms.d",
        "kind": "def",
        "family": "Geometry",
        "pos": {
            "x": 0.20529013872146606,
            "y": 0.5877557992935181,
            "z": 0.42956069111824036
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Geometry.Forms.d_def",
        "kind": "theorem",
        "family": "Geometry",
        "pos": {
            "x": 0.6853364109992981,
            "y": 0.06085757538676262,
            "z": 0.13144905865192413
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Geometry.Forms.d_d_eq_zero",
        "kind": "theorem",
        "family": "Geometry",
        "pos": {
            "x": 0.854417622089386,
            "y": 0.05598019063472748,
            "z": 0.2780810296535492
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Geometry.Forms.dWithin",
        "kind": "def",
        "family": "Geometry",
        "pos": {
            "x": 0.485670268535614,
            "y": 0.07166637480258942,
            "z": 0.1462818682193756
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Geometry.Forms.dWithin_def",
        "kind": "theorem",
        "family": "Geometry",
        "pos": {
            "x": 0.435502290725708,
            "y": 0.11512602865695953,
            "z": 0.2239803969860077
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Geometry.Forms.dWithin_univ",
        "kind": "theorem",
        "family": "Geometry",
        "pos": {
            "x": 0.8433736562728882,
            "y": 0.06090620532631874,
            "z": 0.26846975088119507
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Geometry.Forms.dWithin_dWithin_eqOn",
        "kind": "theorem",
        "family": "Geometry",
        "pos": {
            "x": 0.9871721267700195,
            "y": 0.013988933525979519,
            "z": 0.7699527144432068
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Geometry.Forms.dWithin_dWithin_eq_zero",
        "kind": "theorem",
        "family": "Geometry",
        "pos": {
            "x": 0.9749077558517456,
            "y": 0.015587391331791878,
            "z": 0.6819103360176086
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.HeytingTuring.predSet",
        "kind": "def",
        "family": "Other",
        "pos": {
            "x": 0.47846853733062744,
            "y": 0.08081696182489395,
            "z": 0.16784930229187012
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.HeytingTuring.predNucleus",
        "kind": "def",
        "family": "Other",
        "pos": {
            "x": 0.5816519856452942,
            "y": 0.07269643247127533,
            "z": 0.11358805000782013
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.HeytingTuring.predNucleus_fixed_iff",
        "kind": "theorem",
        "family": "Other",
        "pos": {
            "x": 0.9099928140640259,
            "y": 0.03514210507273674,
            "z": 0.4572403132915497
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.HeytingTuring.sInf_supersets_eq",
        "kind": "theorem",
        "family": "Other",
        "pos": {
            "x": 0.04895922169089317,
            "y": 0.9248848557472229,
            "z": 0.8647759556770325
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.HeytingTuring.sInf_fixedPoints_unionNucleus_eq",
        "kind": "theorem",
        "family": "Other",
        "pos": {
            "x": 0.6306750774383545,
            "y": 0.10486213117837906,
            "z": 0.4498545527458191
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.HeytingTuring.PredFrame",
        "kind": "def",
        "family": "Other",
        "pos": {
            "x": 0.2218039482831955,
            "y": 0.570507824420929,
            "z": 0.4743085503578186
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.DiscreteExample.reachesPeriod2Set",
        "kind": "def",
        "family": "Other",
        "pos": {
            "x": 0.763900637626648,
            "y": 0.05768406391143799,
            "z": 0.2654568552970886
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.DiscreteExample.period2Nucleus",
        "kind": "def",
        "family": "Other",
        "pos": {
            "x": 0.9672940373420715,
            "y": 0.017883166670799255,
            "z": 0.5986083149909973
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.DiscreteExample.not_computable_mem_reachesPeriod2Set",
        "kind": "theorem",
        "family": "Other",
        "pos": {
            "x": 0.5599305629730225,
            "y": 0.16196675598621368,
            "z": 0.5398834943771362
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.ReachSystem",
        "kind": "structure",
        "family": "Other",
        "pos": {
            "x": 0.08514925837516785,
            "y": 0.8362765908241272,
            "z": 0.611038088798523
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.ReachSystem.K",
        "kind": "def",
        "family": "Other",
        "pos": {
            "x": 0.11102569103240967,
            "y": 0.7833679914474487,
            "z": 0.5730364918708801
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.ReachSystem.K_contract",
        "kind": "lemma",
        "family": "Other",
        "pos": {
            "x": 0.10257925093173981,
            "y": 0.8184204697608948,
            "z": 0.6639351844787598
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.ReachSystem.K_monotone",
        "kind": "lemma",
        "family": "Other",
        "pos": {
            "x": 0.08315370976924896,
            "y": 0.8535676002502441,
            "z": 0.6954504251480103
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.ReachSystem.K_idem",
        "kind": "lemma",
        "family": "Other",
        "pos": {
            "x": 0.10141707956790924,
            "y": 0.815520703792572,
            "z": 0.6340808272361755
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.ReachSystem.K_meet",
        "kind": "lemma",
        "family": "Other",
        "pos": {
            "x": 0.11565069854259491,
            "y": 0.791397750377655,
            "z": 0.6288160085678101
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.ReachSystem.IsInvariant",
        "kind": "def",
        "family": "Other",
        "pos": {
            "x": 0.2118670493364334,
            "y": 0.5951410531997681,
            "z": 0.5005442500114441
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.ReachSystem.K_eq_of_invariant",
        "kind": "lemma",
        "family": "Other",
        "pos": {
            "x": 0.18517716228961945,
            "y": 0.6726576089859009,
            "z": 0.6196322441101074
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Realizability.Simulation",
        "kind": "structure",
        "family": "Other",
        "pos": {
            "x": 0.857707679271698,
            "y": 0.0550265833735466,
            "z": 0.2833513617515564
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Realizability.Realizable",
        "kind": "def",
        "family": "Other",
        "pos": {
            "x": 0.621046781539917,
            "y": 0.06897177547216415,
            "z": 0.14944396913051605
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Realizability.realizable_invariant_of_simulation",
        "kind": "theorem",
        "family": "Other",
        "pos": {
            "x": 0.7724302411079407,
            "y": 0.06192733719944954,
            "z": 0.44000327587127686
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Seismic.Station",
        "kind": "structure",
        "family": "Seismic",
        "pos": {
            "x": 0.025225894525647163,
            "y": 0.9755823612213135,
            "z": 0.8891929388046265
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Seismic.Station.key",
        "kind": "def",
        "family": "Seismic",
        "pos": {
            "x": 0.08303099125623703,
            "y": 0.8533437252044678,
            "z": 0.679681658744812
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Seismic.ObservationWindow",
        "kind": "structure",
        "family": "Seismic",
        "pos": {
            "x": 0.07911600917577744,
            "y": 0.8658190965652466,
            "z": 0.7375327348709106
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Seismic.Waveform",
        "kind": "structure",
        "family": "Seismic",
        "pos": {
            "x": 0.044296517968177795,
            "y": 0.9420083165168762,
            "z": 0.7851381897926331
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Seismic.SeismicEvent",
        "kind": "structure",
        "family": "Seismic",
        "pos": {
            "x": 0.028024723753333092,
            "y": 0.962794303894043,
            "z": 0.910954475402832
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Seismic.CategoricalValidation.ValidationPair",
        "kind": "structure",
        "family": "Seismic",
        "pos": {
            "x": 0.09110133349895477,
            "y": 0.8525025248527527,
            "z": 0.814032256603241
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Seismic.CategoricalValidation.mean",
        "kind": "def",
        "family": "Seismic",
        "pos": {
            "x": 0.05611495301127434,
            "y": 0.9097784757614136,
            "z": 0.8602250218391418
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Seismic.CategoricalValidation.std",
        "kind": "def",
        "family": "Seismic",
        "pos": {
            "x": 0.20793578028678894,
            "y": 0.6308561563491821,
            "z": 0.6037494540214539
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Seismic.CategoricalValidation.roundTo",
        "kind": "def",
        "family": "Seismic",
        "pos": {
            "x": 0.42557650804519653,
            "y": 0.21233531832695007,
            "z": 0.45719751715660095
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Seismic.CategoricalValidation.fmt",
        "kind": "def",
        "family": "Seismic",
        "pos": {
            "x": 0.1277514100074768,
            "y": 0.7840508818626404,
            "z": 0.7189841270446777
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Seismic.CategoricalValidation.StandardMetrics",
        "kind": "structure",
        "family": "Seismic",
        "pos": {
            "x": 0.11099392175674438,
            "y": 0.8167833685874939,
            "z": 0.7844098806381226
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Seismic.CategoricalValidation.computeStandardMetrics",
        "kind": "def",
        "family": "Seismic",
        "pos": {
            "x": 0.840507447719574,
            "y": 0.05571334809064865,
            "z": 0.4823668897151947
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Seismic.CategoricalValidation.formatStandardReport",
        "kind": "def",
        "family": "Seismic",
        "pos": {
            "x": 0.16536924242973328,
            "y": 0.7312437295913696,
            "z": 0.7567065358161926
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Seismic.CategoricalValidation.CategoricalSummary",
        "kind": "structure",
        "family": "Seismic",
        "pos": {
            "x": 0.09911755472421646,
            "y": 0.8390407562255859,
            "z": 0.8028133511543274
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Seismic.CategoricalValidation.summarizeCategorically",
        "kind": "def",
        "family": "Seismic",
        "pos": {
            "x": 0.9441513419151306,
            "y": 0.010551744140684605,
            "z": 0.7033145427703857
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Seismic.CategoricalValidation.generateCategoricalReport",
        "kind": "def",
        "family": "Seismic",
        "pos": {
            "x": 0.3874095380306244,
            "y": 0.3656146824359894,
            "z": 0.6368809938430786
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Seismic.CategoricalValidation.StandardMetrics",
        "kind": "def",
        "family": "Seismic",
        "pos": {
            "x": 0.9062454700469971,
            "y": 0.018510080873966217,
            "z": 0.5853211879730225
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Seismic.CategoricalValidation.CategoricalSummary",
        "kind": "def",
        "family": "Seismic",
        "pos": {
            "x": 0.9003893733024597,
            "y": 0.019921118393540382,
            "z": 0.5937886834144592
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Seismic.Kernel",
        "kind": "structure",
        "family": "Seismic",
        "pos": {
            "x": 0.4112919867038727,
            "y": 0.15332770347595215,
            "z": 0.16635623574256897
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Seismic.Kernel.toFun_eq_coe",
        "kind": "lemma",
        "family": "Seismic",
        "pos": {
            "x": 0.3930298388004303,
            "y": 0.19598031044006348,
            "z": 0.32860276103019714
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Seismic.Kernel.monotone",
        "kind": "lemma",
        "family": "Seismic",
        "pos": {
            "x": 0.4025505483150482,
            "y": 0.16208051145076752,
            "z": 0.2696693241596222
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Seismic.Kernel.map_inf",
        "kind": "lemma",
        "family": "Seismic",
        "pos": {
            "x": 0.21063244342803955,
            "y": 0.5946760177612305,
            "z": 0.49980542063713074
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Seismic.Kernel.idempotent",
        "kind": "lemma",
        "family": "Seismic",
        "pos": {
            "x": 0.12218348681926727,
            "y": 0.7923456430435181,
            "z": 0.680115282535553
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Seismic.Kernel.apply_le",
        "kind": "lemma",
        "family": "Seismic",
        "pos": {
            "x": 0.05730484798550606,
            "y": 0.9149829149246216,
            "z": 0.8130346536636353
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Seismic.obsKey",
        "kind": "def",
        "family": "Seismic",
        "pos": {
            "x": 0.33841049671173096,
            "y": 0.2960147261619568,
            "z": 0.24472029507160187
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Seismic.ObsEq",
        "kind": "def",
        "family": "Seismic",
        "pos": {
            "x": 0.3342193067073822,
            "y": 0.3047126829624176,
            "z": 0.22569692134857178
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Seismic.obsKernelSet",
        "kind": "def",
        "family": "Seismic",
        "pos": {
            "x": 0.3830571174621582,
            "y": 0.19611229002475739,
            "z": 0.25637876987457275
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Seismic.obsKernelSet_subset",
        "kind": "theorem",
        "family": "Seismic",
        "pos": {
            "x": 0.3861108720302582,
            "y": 0.22054563462734222,
            "z": 0.35749953985214233
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Seismic.obsKernelSet_mono",
        "kind": "theorem",
        "family": "Seismic",
        "pos": {
            "x": 0.6336618661880493,
            "y": 0.06847579032182693,
            "z": 0.15521468222141266
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Seismic.obsKernelSet_inf",
        "kind": "theorem",
        "family": "Seismic",
        "pos": {
            "x": 0.36044803261756897,
            "y": 0.2668607532978058,
            "z": 0.34381103515625
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Seismic.obsKernelSet_idem",
        "kind": "theorem",
        "family": "Seismic",
        "pos": {
            "x": 0.2566443383693695,
            "y": 0.4962919354438782,
            "z": 0.43448108434677124
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Seismic.obsKernel",
        "kind": "def",
        "family": "Seismic",
        "pos": {
            "x": 0.5494294762611389,
            "y": 0.07976638525724411,
            "z": 0.048293523490428925
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Seismic.TravelTimeModel",
        "kind": "structure",
        "family": "Seismic",
        "pos": {
            "x": 0.22802232205867767,
            "y": 0.5545758008956909,
            "z": 0.4566437304019928
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Seismic.DetectionModel",
        "kind": "structure",
        "family": "Seismic",
        "pos": {
            "x": 0.2375928908586502,
            "y": 0.5304110050201416,
            "z": 0.43158793449401855
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Seismic.reaches",
        "kind": "def",
        "family": "Seismic",
        "pos": {
            "x": 0.3825829327106476,
            "y": 0.19545391201972961,
            "z": 0.2082563042640686
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Seismic.reachingRelOfDetection",
        "kind": "def",
        "family": "Seismic",
        "pos": {
            "x": 0.5562386512756348,
            "y": 0.07181859761476517,
            "z": 0.20453377068042755
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Seismic.reachingRelOfDetection_functional",
        "kind": "theorem",
        "family": "Seismic",
        "pos": {
            "x": 0.3285660445690155,
            "y": 0.42604801058769226,
            "z": 0.5954777002334595
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Seismic.absF",
        "kind": "def",
        "family": "Seismic",
        "pos": {
            "x": 0.201600581407547,
            "y": 0.5823408961296082,
            "z": 0.38268235325813293
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Seismic.sumAbs",
        "kind": "def",
        "family": "Seismic",
        "pos": {
            "x": 0.39420798420906067,
            "y": 0.1728326380252838,
            "z": 0.17161710560321808
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Seismic.sumAbsRange",
        "kind": "def",
        "family": "Seismic",
        "pos": {
            "x": 0.3369251787662506,
            "y": 0.30383238196372986,
            "z": 0.2875535190105438
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Seismic.detectSTA_LTA",
        "kind": "def",
        "family": "Seismic",
        "pos": {
            "x": 0.45470157265663147,
            "y": 0.099066823720932,
            "z": 0.16489750146865845
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Seismic.observedArrivalMsSTA_LTA",
        "kind": "def",
        "family": "Seismic",
        "pos": {
            "x": 0.43776735663414,
            "y": 0.1844480037689209,
            "z": 0.43142738938331604
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.TKFT.BordismSemantics",
        "kind": "structure",
        "family": "TKFT",
        "pos": {
            "x": 0.2099626362323761,
            "y": 0.5981787443161011,
            "z": 0.49927419424057007
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.TKFT.BordismSemantics.ext",
        "kind": "theorem",
        "family": "TKFT",
        "pos": {
            "x": 0.1772049516439438,
            "y": 0.6726738810539246,
            "z": 0.5673239827156067
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.TKFT.BordismSemantics.id",
        "kind": "def",
        "family": "TKFT",
        "pos": {
            "x": 0.6306265592575073,
            "y": 0.06818286329507828,
            "z": 0.14950866997241974
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.TKFT.BordismSemantics.comp",
        "kind": "def",
        "family": "TKFT",
        "pos": {
            "x": 0.958986759185791,
            "y": 0.0192963145673275,
            "z": 0.5382875204086304
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.TKFT.BordismSemantics.id_reach",
        "kind": "theorem",
        "family": "TKFT",
        "pos": {
            "x": 0.5349728465080261,
            "y": 0.07359162718057632,
            "z": 0.21455666422843933
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.TKFT.BordismSemantics.comp_reach",
        "kind": "theorem",
        "family": "TKFT",
        "pos": {
            "x": 0.278818815946579,
            "y": 0.5122636556625366,
            "z": 0.5998877882957458
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.TKFT.SemObj",
        "kind": "structure",
        "family": "TKFT",
        "pos": {
            "x": 0.021405819803476334,
            "y": 0.9769039154052734,
            "z": 0.9084676504135132
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.TKFT.Obj",
        "kind": "structure",
        "family": "TKFT",
        "pos": {
            "x": 0.010775010101497173,
            "y": 0.9799663424491882,
            "z": 0.9683025479316711
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.TKFT.DiscreteBordism",
        "kind": "structure",
        "family": "TKFT",
        "pos": {
            "x": 0.3729543685913086,
            "y": 0.21893653273582458,
            "z": 0.26434990763664246
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.TKFT.DiscreteBordism.reachingRel",
        "kind": "def",
        "family": "TKFT",
        "pos": {
            "x": 0.7619456648826599,
            "y": 0.056270916014909744,
            "z": 0.24585165083408356
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.TKFT.DiscreteBordism.reachingRel_rel",
        "kind": "theorem",
        "family": "TKFT",
        "pos": {
            "x": 0.8323055505752563,
            "y": 0.06688538938760757,
            "z": 0.3278307616710663
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.TKFT.DiscreteBordism.done_iter_of_done",
        "kind": "theorem",
        "family": "TKFT",
        "pos": {
            "x": 0.3591260612010956,
            "y": 0.34952229261398315,
            "z": 0.5449249148368835
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.TKFT.DiscreteBordism.reachingRel_functional",
        "kind": "theorem",
        "family": "TKFT",
        "pos": {
            "x": 0.5499705672264099,
            "y": 0.1405310183763504,
            "z": 0.47699281573295593
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.TKFT.DiscreteBordism.semantics",
        "kind": "def",
        "family": "TKFT",
        "pos": {
            "x": 0.28017833828926086,
            "y": 0.49602797627449036,
            "z": 0.5691974759101868
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.TKFT.DiscreteBordism.semantics_reach",
        "kind": "theorem",
        "family": "TKFT",
        "pos": {
            "x": 0.890965461730957,
            "y": 0.04525598883628845,
            "z": 0.4329879581928253
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.TKFT.DiscreteBordism.glue",
        "kind": "def",
        "family": "TKFT",
        "pos": {
            "x": 0.3439216911792755,
            "y": 0.30731531977653503,
            "z": 0.3608875274658203
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.TKFT.DiscreteBordism.glue_init",
        "kind": "theorem",
        "family": "TKFT",
        "pos": {
            "x": 0.613384485244751,
            "y": 0.07396368682384491,
            "z": 0.18718694150447845
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.TKFT.DiscreteBordism.glue_done_inl",
        "kind": "theorem",
        "family": "TKFT",
        "pos": {
            "x": 0.7042619585990906,
            "y": 0.06457359343767166,
            "z": 0.2705782949924469
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.TKFT.DiscreteBordism.glue_done_inr",
        "kind": "theorem",
        "family": "TKFT",
        "pos": {
            "x": 0.3363702595233917,
            "y": 0.38750794529914856,
            "z": 0.541352391242981
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.TKFT.DiscreteBordism.glue_step_inr",
        "kind": "theorem",
        "family": "TKFT",
        "pos": {
            "x": 0.4816150665283203,
            "y": 0.15278193354606628,
            "z": 0.43070903420448303
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.TKFT.DiscreteBordism.glue_step_inl_none",
        "kind": "theorem",
        "family": "TKFT",
        "pos": {
            "x": 0.6792508959770203,
            "y": 0.0712452083826065,
            "z": 0.3037533164024353
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.TKFT.DiscreteBordism.glue_step_inl_some",
        "kind": "theorem",
        "family": "TKFT",
        "pos": {
            "x": 0.6497939825057983,
            "y": 0.07985079288482666,
            "z": 0.30096152424812317
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.TKFT.DiscreteBordism.glue_iter_inr",
        "kind": "theorem",
        "family": "TKFT",
        "pos": {
            "x": 0.19151636958122253,
            "y": 0.6599188446998596,
            "z": 0.6291044354438782
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.TKFT.DiscreteBordism.glue_iter_inl_of_no_done",
        "kind": "theorem",
        "family": "TKFT",
        "pos": {
            "x": 0.467781662940979,
            "y": 0.2175244390964508,
            "z": 0.5492659211158752
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.TKFT.reachingRel_glue_eq_comp",
        "kind": "theorem",
        "family": "TKFT",
        "pos": {
            "x": 0.7079617381095886,
            "y": 0.06004611775279045,
            "z": 0.19222886860370636
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.TKFT.reachingRelOfFlow",
        "kind": "def",
        "family": "TKFT",
        "pos": {
            "x": 0.806542694568634,
            "y": 0.05520661920309067,
            "z": 0.1850091516971588
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.TKFT.reachingRelOfFlow_spec",
        "kind": "theorem",
        "family": "TKFT",
        "pos": {
            "x": 0.893731951713562,
            "y": 0.04714382812380791,
            "z": 0.368875652551651
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.TKFT.reachingRelOfFlow_comp",
        "kind": "theorem",
        "family": "TKFT",
        "pos": {
            "x": 0.956301212310791,
            "y": 0.019562195986509323,
            "z": 0.5264366269111633
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.TKFT.PartialFlow.reachingRelOfPartialFlow",
        "kind": "def",
        "family": "TKFT",
        "pos": {
            "x": 0.7515074014663696,
            "y": 0.062408171594142914,
            "z": 0.38736453652381897
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.TKFT.PartialFlow.reachingRelOfPartialFlow_spec",
        "kind": "theorem",
        "family": "TKFT",
        "pos": {
            "x": 0.4901094436645508,
            "y": 0.20072148740291595,
            "z": 0.5451794266700745
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.TKFT.PartialFlow.reachingRelOfPartialFlow_comp",
        "kind": "theorem",
        "family": "TKFT",
        "pos": {
            "x": 0.9134262800216675,
            "y": 0.012568017467856407,
            "z": 0.6123161315917969
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.TKFT.PartialFlow.reachingRelOfPartialFlow_ofFlow_eq",
        "kind": "theorem",
        "family": "TKFT",
        "pos": {
            "x": 0.6672416925430298,
            "y": 0.09368760138750076,
            "z": 0.4667777717113495
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.TKFT.ReachingRel",
        "kind": "structure",
        "family": "TKFT",
        "pos": {
            "x": 0.13837023079395294,
            "y": 0.7415728569030762,
            "z": 0.5815655589103699
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.TKFT.ReachingRel.ext",
        "kind": "theorem",
        "family": "TKFT",
        "pos": {
            "x": 0.34154796600341797,
            "y": 0.29411232471466064,
            "z": 0.28739604353904724
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.TKFT.ReachingRel.id",
        "kind": "def",
        "family": "TKFT",
        "pos": {
            "x": 0.4175463020801544,
            "y": 0.1495746523141861,
            "z": 0.20398133993148804
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.TKFT.ReachingRel.comp",
        "kind": "def",
        "family": "TKFT",
        "pos": {
            "x": 0.4579959213733673,
            "y": 0.0874863713979721,
            "z": 0.17327092587947845
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.TKFT.ReachingRel.id_rel",
        "kind": "theorem",
        "family": "TKFT",
        "pos": {
            "x": 0.1725369095802307,
            "y": 0.6836408376693726,
            "z": 0.5680288672447205
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.TKFT.ReachingRel.id_left",
        "kind": "theorem",
        "family": "TKFT",
        "pos": {
            "x": 0.21039386093616486,
            "y": 0.6056819558143616,
            "z": 0.5261420011520386
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.TKFT.ReachingRel.id_right",
        "kind": "theorem",
        "family": "TKFT",
        "pos": {
            "x": 0.11064030975103378,
            "y": 0.8084713816642761,
            "z": 0.6797226667404175
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.TKFT.ReachingRel.assoc",
        "kind": "theorem",
        "family": "TKFT",
        "pos": {
            "x": 0.30942729115486145,
            "y": 0.3717907965183258,
            "z": 0.33256199955940247
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.TKFT.ReachingRel.Functional",
        "kind": "def",
        "family": "TKFT",
        "pos": {
            "x": 0.538358211517334,
            "y": 0.07010513544082642,
            "z": 0.18859273195266724
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.TKFT.ReachingRel.Image",
        "kind": "def",
        "family": "TKFT",
        "pos": {
            "x": 0.05285733565688133,
            "y": 0.9232891798019409,
            "z": 0.8170228600502014
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.TKFT.ReachingRel.Image.mk_rel",
        "kind": "theorem",
        "family": "TKFT",
        "pos": {
            "x": 0.27327194809913635,
            "y": 0.5125592947006226,
            "z": 0.5785723328590393
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.TKFT.ReachingRel.toPart",
        "kind": "def",
        "family": "TKFT",
        "pos": {
            "x": 0.4680171310901642,
            "y": 0.09303286671638489,
            "z": 0.18987633287906647
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.TKFT.ReachingRel.toPart_spec",
        "kind": "theorem",
        "family": "TKFT",
        "pos": {
            "x": 0.49481990933418274,
            "y": 0.07504764944314957,
            "z": 0.2084570825099945
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.TKFT.RelCatBridge.toSetRel",
        "kind": "def",
        "family": "TKFT",
        "pos": {
            "x": 0.3550298511981964,
            "y": 0.28604090213775635,
            "z": 0.3738597631454468
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.TKFT.RelCatBridge.mem_toSetRel",
        "kind": "theorem",
        "family": "TKFT",
        "pos": {
            "x": 0.4715523421764374,
            "y": 0.13243024051189423,
            "z": 0.3586040735244751
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.TKFT.RelCatBridge.ofSetRel",
        "kind": "def",
        "family": "TKFT",
        "pos": {
            "x": 0.3506218194961548,
            "y": 0.29568707942962646,
            "z": 0.36814653873443604
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.TKFT.RelCatBridge.ofSetRel_rel",
        "kind": "theorem",
        "family": "TKFT",
        "pos": {
            "x": 0.3196861147880554,
            "y": 0.39287546277046204,
            "z": 0.4692186117172241
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.TKFT.RelCatBridge.toRelCat",
        "kind": "def",
        "family": "TKFT",
        "pos": {
            "x": 0.16769544780254364,
            "y": 0.7025413513183594,
            "z": 0.5990772247314453
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.TKFT.RelCatBridge.fromRelCat",
        "kind": "def",
        "family": "TKFT",
        "pos": {
            "x": 0.07626736164093018,
            "y": 0.8741387128829956,
            "z": 0.7701436281204224
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.TKFT.RelCatBridge.toRelCat_obj",
        "kind": "theorem",
        "family": "TKFT",
        "pos": {
            "x": 0.8336175680160522,
            "y": 0.06499706953763962,
            "z": 0.2795094847679138
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.TKFT.RelCatBridge.fromRelCat_obj",
        "kind": "theorem",
        "family": "TKFT",
        "pos": {
            "x": 0.5522255897521973,
            "y": 0.0710546150803566,
            "z": 0.2061414122581482
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.TKFT.RelCatBridge.equivalence",
        "kind": "def",
        "family": "TKFT",
        "pos": {
            "x": 0.12516310811042786,
            "y": 0.7855247855186462,
            "z": 0.6949400901794434
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Topology.cycleRank",
        "kind": "def",
        "family": "Other",
        "pos": {
            "x": 0.40257880091667175,
            "y": 0.16113804280757904,
            "z": 0.18738418817520142
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Topology.connected_card_vert_le_card_edgeSet_add_one",
        "kind": "theorem",
        "family": "Other",
        "pos": {
            "x": 0.6792089939117432,
            "y": 0.08909202367067337,
            "z": 0.47565197944641113
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Topology.cycleRank_eq_zero_of_isTree",
        "kind": "theorem",
        "family": "Other",
        "pos": {
            "x": 0.6795452237129211,
            "y": 0.06981460005044937,
            "z": 0.29026877880096436
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Undecidability.ManyOne",
        "kind": "structure",
        "family": "Undecidability",
        "pos": {
            "x": 0.26586291193962097,
            "y": 0.4657471477985382,
            "z": 0.37403297424316406
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Undecidability.ManyOne.computable_of_reduces",
        "kind": "theorem",
        "family": "Undecidability",
        "pos": {
            "x": 0.9074293971061707,
            "y": 0.02439708821475506,
            "z": 0.54100501537323
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Undecidability.ManyOne.not_computable_of_reduces",
        "kind": "theorem",
        "family": "Undecidability",
        "pos": {
            "x": 0.3434078097343445,
            "y": 0.41291409730911255,
            "z": 0.6171004772186279
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Undecidability.Halting.Halts",
        "kind": "def",
        "family": "Undecidability",
        "pos": {
            "x": 0.07562984526157379,
            "y": 0.8763856887817383,
            "z": 0.7791953682899475
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Undecidability.Halting.not_computable",
        "kind": "theorem",
        "family": "Undecidability",
        "pos": {
            "x": 0.43688759207725525,
            "y": 0.20372465252876282,
            "z": 0.46470925211906433
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Undecidability.Halting.not_computable_of_halting_reduces",
        "kind": "theorem",
        "family": "Undecidability",
        "pos": {
            "x": 0.5042121410369873,
            "y": 0.2141030728816986,
            "z": 0.5859568119049072
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Wolfram.confluence_causal_invariance_independent",
        "kind": "def",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.7483675479888916,
            "y": 0.06407789885997772,
            "z": 0.4141933023929596
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Wolfram.CE1_confluentNF",
        "kind": "def",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.9207000732421875,
            "y": 0.03531178459525108,
            "z": 0.38835904002189636
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Wolfram.CE1_not_causalInvariant",
        "kind": "def",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.6638285517692566,
            "y": 0.06769243627786636,
            "z": 0.21462690830230713
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Wolfram.CE2_causalInvariant",
        "kind": "def",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.37362930178642273,
            "y": 0.24711927771568298,
            "z": 0.3660871386528015
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Wolfram.CE2_not_confluentNF",
        "kind": "def",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.0658007338643074,
            "y": 0.8934957385063171,
            "z": 0.7968865036964417
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Wolfram.TKFT.unreachableFrom",
        "kind": "def",
        "family": "Wolfram",
        "pos": {
            "x": 0.7703691124916077,
            "y": 0.05547691509127617,
            "z": 0.2405332624912262
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Wolfram.TKFT.reachabilityNucleus",
        "kind": "def",
        "family": "Wolfram",
        "pos": {
            "x": 0.2947617471218109,
            "y": 0.4706193506717682,
            "z": 0.5653099417686462
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Wolfram.TKFT.reachabilityNucleus_apply",
        "kind": "theorem",
        "family": "Wolfram",
        "pos": {
            "x": 0.28854119777679443,
            "y": 0.5003160238265991,
            "z": 0.6121342778205872
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Wolfram.reachingRelOfWppRule",
        "kind": "def",
        "family": "Wolfram/Multiway",
        "pos": {
            "x": 0.8309675455093384,
            "y": 0.06262724846601486,
            "z": 0.2635253965854645
        }
    },
    {
        "name": "HeytingLean.MirandaDynamics.Wolfram.reachingRelOfWppRule_rel_iff",
        "kind": "theorem",
        "family": "Wolfram/Multiway",
        "pos": {
            "x": 0.3530646860599518,
            "y": 0.3504091203212738,
            "z": 0.5244335532188416
        }
    },
    {
        "name": "HeytingLean.WPP.Edge",
        "kind": "structure",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.0026440054643899202,
            "y": 0.9820567965507507,
            "z": 0.9855170845985413
        }
    },
    {
        "name": "HeytingLean.WPP.LabeledEdge",
        "kind": "structure",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.005788538604974747,
            "y": 0.9731163382530212,
            "z": 0.9896894097328186
        }
    },
    {
        "name": "HeytingLean.WPP.MultiwayResult",
        "kind": "structure",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.344801664352417,
            "y": 0.2903882563114166,
            "z": 0.17686676979064941
        }
    },
    {
        "name": "HeytingLean.WPP.Build.dedup",
        "kind": "def",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.8191283941268921,
            "y": 0.05315495282411575,
            "z": 0.181658536195755
        }
    },
    {
        "name": "HeytingLean.WPP.Build.nextLevel",
        "kind": "def",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.7657582759857178,
            "y": 0.04862881824374199,
            "z": 0.11556826531887054
        }
    },
    {
        "name": "HeytingLean.WPP.Build.findIdxFuel",
        "kind": "def",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.16967472434043884,
            "y": 0.6404121518135071,
            "z": 0.4055887460708618
        }
    },
    {
        "name": "HeytingLean.WPP.Build.findIdx",
        "kind": "def",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.9156514406204224,
            "y": 0.03582848981022835,
            "z": 0.3584657311439514
        }
    },
    {
        "name": "HeytingLean.WPP.Build.buildMultiway",
        "kind": "def",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.9190523028373718,
            "y": 0.03456372767686844,
            "z": 0.3674967586994171
        }
    },
    {
        "name": "HeytingLean.WPP.Build.reachableWithinArr",
        "kind": "def",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.9969338774681091,
            "y": 0.0045956759713590145,
            "z": 0.8183416128158569
        }
    },
    {
        "name": "HeytingLean.WPP.Build.checkInvarianceDepth1",
        "kind": "def",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.39346158504486084,
            "y": 0.1787676066160202,
            "z": 0.17526160180568695
        }
    },
    {
        "name": "HeytingLean.WPP.Build.firstNonInvariantWitness",
        "kind": "def",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.6870399713516235,
            "y": 0.05897366628050804,
            "z": 0.11832911521196365
        }
    },
    {
        "name": "HeytingLean.WPP.Build.checkInvarianceAllLevels",
        "kind": "def",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.3551267683506012,
            "y": 0.25854089856147766,
            "z": 0.26903536915779114
        }
    },
    {
        "name": "HeytingLean.WPP.Examples.StrRule",
        "kind": "structure",
        "family": "Wolfram",
        "pos": {
            "x": 0.005607164930552244,
            "y": 0.970795750617981,
            "z": 0.9954807162284851
        }
    },
    {
        "name": "HeytingLean.WPP.Examples.StrSystem",
        "kind": "def",
        "family": "Wolfram",
        "pos": {
            "x": 0.14642992615699768,
            "y": 0.6942483186721802,
            "z": 0.44704416394233704
        }
    },
    {
        "name": "HeytingLean.WPP.Examples.StrRule.replaceAt",
        "kind": "def",
        "family": "Wolfram",
        "pos": {
            "x": 0.46530666947364807,
            "y": 0.10080445557832718,
            "z": 0.09826129674911499
        }
    },
    {
        "name": "HeytingLean.WPP.Examples.StrRule.enumerate",
        "kind": "def",
        "family": "Wolfram",
        "pos": {
            "x": 0.16977639496326447,
            "y": 0.6534582376480103,
            "z": 0.44346997141838074
        }
    },
    {
        "name": "HeytingLean.WPP.Examples.StrRule.stepOne",
        "kind": "def",
        "family": "Wolfram",
        "pos": {
            "x": 0.21095924079418182,
            "y": 0.5585912466049194,
            "z": 0.3580324649810791
        }
    },
    {
        "name": "HeytingLean.WPP.Examples.StrRule.step",
        "kind": "def",
        "family": "Wolfram",
        "pos": {
            "x": 0.5059443712234497,
            "y": 0.09257093071937561,
            "z": 0.043141692876815796
        }
    },
    {
        "name": "HeytingLean.WPP.Examples.StrRule.stepOneLabeled",
        "kind": "def",
        "family": "Wolfram",
        "pos": {
            "x": 0.37161001563072205,
            "y": 0.22212845087051392,
            "z": 0.25348275899887085
        }
    },
    {
        "name": "HeytingLean.WPP.Examples.StrRule.stepLabeled",
        "kind": "def",
        "family": "Wolfram",
        "pos": {
            "x": 0.4511012136936188,
            "y": 0.11040326207876205,
            "z": 0.12480558454990387
        }
    },
    {
        "name": "HeytingLean.WPP.Examples.StrRule.fibSys",
        "kind": "def",
        "family": "Wolfram",
        "pos": {
            "x": 0.09072145074605942,
            "y": 0.8245501518249512,
            "z": 0.6033019423484802
        }
    },
    {
        "name": "HeytingLean.WPP.Examples.StrRule.dupSys",
        "kind": "def",
        "family": "Wolfram",
        "pos": {
            "x": 0.025374682620167732,
            "y": 0.9771373867988586,
            "z": 0.8622439503669739
        }
    },
    {
        "name": "HeytingLean.WPP.Examples.StrRule.simpleSys",
        "kind": "def",
        "family": "Wolfram",
        "pos": {
            "x": 0.01134925615042448,
            "y": 0.9570573568344116,
            "z": 0.9969020485877991
        }
    },
    {
        "name": "HeytingLean.WPP.WppRule",
        "kind": "structure",
        "family": "Wolfram/Multiway",
        "pos": {
            "x": 0.022658158093690872,
            "y": 0.9923991560935974,
            "z": 0.7923792600631714
        }
    },
    {
        "name": "HeytingLean.WPP.WppRule.stepRel",
        "kind": "def",
        "family": "Wolfram/Multiway",
        "pos": {
            "x": 0.184225395321846,
            "y": 0.6045838594436646,
            "z": 0.3637959361076355
        }
    },
    {
        "name": "HeytingLean.WPP.WppRule.StepStar",
        "kind": "inductive",
        "family": "Wolfram/Multiway",
        "pos": {
            "x": 0.102066271007061,
            "y": 0.7936050295829773,
            "z": 0.5564771890640259
        }
    },
    {
        "name": "HeytingLean.WPP.WppRule.StepStar.trans",
        "kind": "theorem",
        "family": "Wolfram/Multiway",
        "pos": {
            "x": 0.16450592875480652,
            "y": 0.6656072735786438,
            "z": 0.4359872341156006
        }
    },
    {
        "name": "HeytingLean.WPP.WppRule.cone",
        "kind": "def",
        "family": "Wolfram/Multiway",
        "pos": {
            "x": 0.527499794960022,
            "y": 0.10380426049232483,
            "z": 0.011992552317678928
        }
    },
    {
        "name": "HeytingLean.WPP.WppRule.JR",
        "kind": "def",
        "family": "Wolfram/Multiway",
        "pos": {
            "x": 0.32777154445648193,
            "y": 0.3253995180130005,
            "z": 0.19531026482582092
        }
    },
    {
        "name": "HeytingLean.WPP.WppRule.JR_mem_iff",
        "kind": "lemma",
        "family": "Wolfram/Multiway",
        "pos": {
            "x": 0.08176718652248383,
            "y": 0.8423618078231812,
            "z": 0.6020952463150024
        }
    },
    {
        "name": "HeytingLean.WPP.WppRule.JR.mono",
        "kind": "lemma",
        "family": "Wolfram/Multiway",
        "pos": {
            "x": 0.10224093496799469,
            "y": 0.7880867123603821,
            "z": 0.550324022769928
        }
    },
    {
        "name": "HeytingLean.WPP.WppRule.JR.contractive",
        "kind": "lemma",
        "family": "Wolfram/Multiway",
        "pos": {
            "x": 0.18544457852840424,
            "y": 0.6179004311561584,
            "z": 0.4051109850406647
        }
    },
    {
        "name": "HeytingLean.WPP.WppRule.JR.idem",
        "kind": "lemma",
        "family": "Wolfram/Multiway",
        "pos": {
            "x": 0.1855936199426651,
            "y": 0.6080746650695801,
            "z": 0.3666045069694519
        }
    },
    {
        "name": "HeytingLean.WPP.WppRule.JR.inf",
        "kind": "lemma",
        "family": "Wolfram/Multiway",
        "pos": {
            "x": 0.08844581246376038,
            "y": 0.8239075541496277,
            "z": 0.5853419899940491
        }
    },
    {
        "name": "HeytingLean.WPP.WppRule.unreachableFrom",
        "kind": "def",
        "family": "Wolfram/Multiway",
        "pos": {
            "x": 0.4755582809448242,
            "y": 0.10193608701229095,
            "z": 0.07392795383930206
        }
    },
    {
        "name": "HeytingLean.WPP.WppRule.reachabilityNucleus",
        "kind": "def",
        "family": "Wolfram/Multiway",
        "pos": {
            "x": 0.0917370468378067,
            "y": 0.8282617926597595,
            "z": 0.6296129822731018
        }
    },
    {
        "name": "HeytingLean.WPP.WppRule.reachabilityNucleus_apply",
        "kind": "lemma",
        "family": "Wolfram/Multiway",
        "pos": {
            "x": 0.1106783077120781,
            "y": 0.8048384189605713,
            "z": 0.648254930973053
        }
    },
    {
        "name": "HeytingLean.WPP.WppRel",
        "kind": "structure",
        "family": "Wolfram/Multiway",
        "pos": {
            "x": 0.019581718370318413,
            "y": 1.0,
            "z": 0.7903608083724976
        }
    },
    {
        "name": "HeytingLean.WPP.WppRel.StepStar",
        "kind": "def",
        "family": "Wolfram/Multiway",
        "pos": {
            "x": 0.1794469803571701,
            "y": 0.617405116558075,
            "z": 0.3750365972518921
        }
    },
    {
        "name": "HeytingLean.WPP.WppRel.cone",
        "kind": "def",
        "family": "Wolfram/Multiway",
        "pos": {
            "x": 0.3738982081413269,
            "y": 0.23304228484630585,
            "z": 0.15120726823806763
        }
    },
    {
        "name": "HeytingLean.WPP.WppRel.JR",
        "kind": "def",
        "family": "Wolfram/Multiway",
        "pos": {
            "x": 0.0052220625802874565,
            "y": 0.9824304580688477,
            "z": 0.9703524112701416
        }
    },
    {
        "name": "HeytingLean.WPP.WppRel.JR.mono",
        "kind": "lemma",
        "family": "Wolfram/Multiway",
        "pos": {
            "x": 0.09991626441478729,
            "y": 0.7935532331466675,
            "z": 0.5522899031639099
        }
    },
    {
        "name": "HeytingLean.WPP.WppRel.JR.contractive",
        "kind": "lemma",
        "family": "Wolfram/Multiway",
        "pos": {
            "x": 0.2008948177099228,
            "y": 0.5761979818344116,
            "z": 0.34911420941352844
        }
    },
    {
        "name": "HeytingLean.WPP.WppRel.JR.idem",
        "kind": "lemma",
        "family": "Wolfram/Multiway",
        "pos": {
            "x": 0.1830323338508606,
            "y": 0.6103624701499939,
            "z": 0.3684242367744446
        }
    },
    {
        "name": "HeytingLean.WPP.WppRel.JR.inf",
        "kind": "lemma",
        "family": "Wolfram/Multiway",
        "pos": {
            "x": 0.08572456240653992,
            "y": 0.830812394618988,
            "z": 0.585827112197876
        }
    },
    {
        "name": "HeytingLean.WPP.WppRel.unreachableFrom",
        "kind": "def",
        "family": "Wolfram/Multiway",
        "pos": {
            "x": 0.4769760072231293,
            "y": 0.1067318469285965,
            "z": 0.06772610545158386
        }
    },
    {
        "name": "HeytingLean.WPP.WppRel.reachabilityNucleus",
        "kind": "def",
        "family": "Wolfram/Multiway",
        "pos": {
            "x": 0.09103681147098541,
            "y": 0.8287258148193359,
            "z": 0.6229279041290283
        }
    },
    {
        "name": "HeytingLean.WPP.WppRel.reachabilityNucleus_apply",
        "kind": "lemma",
        "family": "Wolfram/Multiway",
        "pos": {
            "x": 0.1051420196890831,
            "y": 0.8126850128173828,
            "z": 0.6494655013084412
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.System.pathsAtDepth",
        "kind": "def",
        "family": "Wolfram/Branchial",
        "pos": {
            "x": 0.28691762685775757,
            "y": 0.4108206033706665,
            "z": 0.2894282639026642
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.System.mem_pathsAtDepth_len",
        "kind": "lemma",
        "family": "Wolfram/Branchial",
        "pos": {
            "x": 0.43269315361976624,
            "y": 0.12678225338459015,
            "z": 0.23797431588172913
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.System.mem_stepStates_of_mem_stepEdges",
        "kind": "lemma",
        "family": "Wolfram/Branchial",
        "pos": {
            "x": 0.3087462782859802,
            "y": 0.44695237278938293,
            "z": 0.5727381110191345
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.System.image_snd_pathsAtDepth_eq_statesAtDepth",
        "kind": "theorem",
        "family": "Wolfram/Branchial",
        "pos": {
            "x": 0.17462623119354248,
            "y": 0.7150605916976929,
            "z": 0.7401244640350342
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.System.pathCountAtDepth",
        "kind": "def",
        "family": "Wolfram/Branchial",
        "pos": {
            "x": 0.46946531534194946,
            "y": 0.0963210016489029,
            "z": 0.10401122272014618
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.System.siblingEdges",
        "kind": "def",
        "family": "Wolfram/Branchial",
        "pos": {
            "x": 0.3904339075088501,
            "y": 0.18158967792987823,
            "z": 0.18423157930374146
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.System.branchialEdgesAtDepth",
        "kind": "def",
        "family": "Wolfram/Branchial",
        "pos": {
            "x": 0.08665280044078827,
            "y": 0.8491435050964355,
            "z": 0.7022069096565247
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.CausalGraph",
        "kind": "structure",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.006617283448576927,
            "y": 0.9684532284736633,
            "z": 0.9950957298278809
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.CausalGraph.Iso",
        "kind": "def",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.297098308801651,
            "y": 0.38924500346183777,
            "z": 0.25693994760513306
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.CausalGraph.Iso",
        "kind": "lemma",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.3259873390197754,
            "y": 0.3268043100833893,
            "z": 0.20692220330238342
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.CausalGraph.not_Iso_of_n_ne",
        "kind": "lemma",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.059407494962215424,
            "y": 0.9098737835884094,
            "z": 0.7921157479286194
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.System.causalGraphOf",
        "kind": "def",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.11487388610839844,
            "y": 0.7918395400047302,
            "z": 0.6223209500312805
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.SystemFresh.ConcreteEvent",
        "kind": "structure",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.042023833841085434,
            "y": 0.9374501705169678,
            "z": 0.8827107548713684
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.SystemFresh.ConcreteEvent.input",
        "kind": "def",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.10888892412185669,
            "y": 0.8131983876228333,
            "z": 0.6955883502960205
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.SystemFresh.ConcreteEvent.output",
        "kind": "def",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.5580281615257263,
            "y": 0.07184727489948273,
            "z": 0.1958618313074112
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.SystemFresh.ConcreteEvent.Causes",
        "kind": "def",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.13113613426685333,
            "y": 0.7735435962677002,
            "z": 0.6831514239311218
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.SystemFresh.causalGraphOf",
        "kind": "def",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.17152993381023407,
            "y": 0.6848137378692627,
            "z": 0.5722991824150085
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.System.Multiset.fold_or_eq_true_of_mem_true",
        "kind": "lemma",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.2988877296447754,
            "y": 0.4830246865749359,
            "z": 0.6160362362861633
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.System.Event.Created",
        "kind": "def",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.5527709126472473,
            "y": 0.0802404060959816,
            "z": 0.05000559240579605
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.System.Event.observableB",
        "kind": "def",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.7918907403945923,
            "y": 0.05681035295128822,
            "z": 0.16498646140098572
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.System.Event.Observable",
        "kind": "def",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.2431551218032837,
            "y": 0.5088748931884766,
            "z": 0.40122190117836
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.System.observableIdxs",
        "kind": "def",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.9714820981025696,
            "y": 0.015454546548426151,
            "z": 0.6010998487472534
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.System.causalGraphGCOf",
        "kind": "def",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.46133795380592346,
            "y": 0.08971615135669708,
            "z": 0.14066657423973083
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.Properties.GCausalInvariant",
        "kind": "def",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.5394482612609863,
            "y": 0.06943371146917343,
            "z": 0.12446698546409607
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.LabeledCausalGraph",
        "kind": "structure",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.03525112196803093,
            "y": 0.9610850811004639,
            "z": 0.8147658109664917
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.LabeledCausalGraph.edge",
        "kind": "def",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.25005418062210083,
            "y": 0.49461302161216736,
            "z": 0.38084229826927185
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.LabeledCausalGraph.forget",
        "kind": "def",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.0451333224773407,
            "y": 0.9419457912445068,
            "z": 0.850742518901825
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.System.Event",
        "kind": "def",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.3916853368282318,
            "y": 0.1872171312570572,
            "z": 0.1648813635110855
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.System.causeWitnesses_ne_zero_iff_causes",
        "kind": "lemma",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.4262769818305969,
            "y": 0.20587453246116638,
            "z": 0.44768020510673523
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.System.labeledCausalGraphOf",
        "kind": "def",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.2523925006389618,
            "y": 0.5003896951675415,
            "z": 0.42113980650901794
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.System.labeledCausalGraphOf_forget_edge_iff",
        "kind": "theorem",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.6819373965263367,
            "y": 0.07202644646167755,
            "z": 0.31133753061294556
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.System.labeledCausalGraphOf_forget_iso_causalGraphOf",
        "kind": "theorem",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.6352669596672058,
            "y": 0.10689250379800797,
            "z": 0.47056469321250916
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.SystemFresh.StepWith",
        "kind": "def",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.2837255299091339,
            "y": 0.4187030792236328,
            "z": 0.3082960247993469
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.SystemFresh.StepStarWith",
        "kind": "def",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.3747915029525757,
            "y": 0.2141120880842209,
            "z": 0.2584284543991089
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.SystemFresh.JoinableIso",
        "kind": "def",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.07587085664272308,
            "y": 0.8700796961784363,
            "z": 0.7163098454475403
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.SystemFresh.BranchResolves",
        "kind": "def",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.4315929412841797,
            "y": 0.12336626648902893,
            "z": 0.21130166947841644
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.SystemFresh.CausalInvariant",
        "kind": "def",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.09252550452947617,
            "y": 0.8370174765586853,
            "z": 0.6837657690048218
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.Properties.ConfluentNF",
        "kind": "def",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.09061895310878754,
            "y": 0.8337691426277161,
            "z": 0.6512057185173035
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.Properties.CausalInvariant",
        "kind": "def",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.49268168210983276,
            "y": 0.073379747569561,
            "z": 0.17197613418102264
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.Counterexamples.sigma2",
        "kind": "def",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.09166429936885834,
            "y": 0.834554135799408,
            "z": 0.6558054685592651
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.Counterexamples.sigma2_zero",
        "kind": "lemma",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.28651657700538635,
            "y": 0.4221639335155487,
            "z": 0.3564596176147461
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.Counterexamples.sigma2_one",
        "kind": "lemma",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.3823085129261017,
            "y": 0.20063267648220062,
            "z": 0.2764941155910492
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.Counterexamples.inj_sigma2",
        "kind": "lemma",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.24968098104000092,
            "y": 0.5032303929328918,
            "z": 0.4163803458213806
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.CE1.P",
        "kind": "def",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.15953218936920166,
            "y": 0.6639427542686462,
            "z": 0.4199860394001007
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.CE1.V",
        "kind": "def",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.08806236833333969,
            "y": 0.8243903517723083,
            "z": 0.5821471214294434
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.CE1.rule",
        "kind": "def",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.19217003881931305,
            "y": 0.590623140335083,
            "z": 0.35558196902275085
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.CE1.init",
        "kind": "def",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.0224064439535141,
            "y": 0.990420937538147,
            "z": 0.7978184223175049
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.CE1.sys",
        "kind": "def",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.009565857239067554,
            "y": 0.9868931174278259,
            "z": 0.9584832191467285
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.CE1.e12",
        "kind": "def",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.020192671567201614,
            "y": 0.992229163646698,
            "z": 0.803807258605957
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.CE1.e13",
        "kind": "def",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.021405482664704323,
            "y": 0.9968692660331726,
            "z": 0.7979283332824707
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.CE1.e23",
        "kind": "def",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.15951281785964966,
            "y": 0.660115659236908,
            "z": 0.41509515047073364
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.CE1.s0",
        "kind": "def",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.778591513633728,
            "y": 0.049514517188072205,
            "z": 0.1273629367351532
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.CE1.s1",
        "kind": "def",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.8045216202735901,
            "y": 0.053921811282634735,
            "z": 0.15955963730812073
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.CE1.s2",
        "kind": "def",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.5202456712722778,
            "y": 0.10404549539089203,
            "z": 0.01504584215581417
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.CE1.pair_le",
        "kind": "lemma",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.5328418612480164,
            "y": 0.09364664554595947,
            "z": 0.024189069867134094
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.CE1.e12_app_s0",
        "kind": "lemma",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.5142613053321838,
            "y": 0.08990098536014557,
            "z": 0.037615370005369186
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.CE1.e13_app_s0",
        "kind": "lemma",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.9244573712348938,
            "y": 0.030549978837370872,
            "z": 0.3793177902698517
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.CE1.e23_app_s1",
        "kind": "lemma",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.9147558212280273,
            "y": 0.036285918205976486,
            "z": 0.35510510206222534
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.CE1.e12_apply_s0",
        "kind": "lemma",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.027719629928469658,
            "y": 0.9791276454925537,
            "z": 0.7918350696563721
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.CE1.e13_apply_s0",
        "kind": "lemma",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.03137151896953583,
            "y": 0.970795750617981,
            "z": 0.7904366850852966
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.CE1.e23_apply_s1",
        "kind": "lemma",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.1678856462240219,
            "y": 0.6557222604751587,
            "z": 0.43888044357299805
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.CE1.idx_eq_zero",
        "kind": "lemma",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.20664507150650024,
            "y": 0.566537618637085,
            "z": 0.3523387014865875
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.CE1.mem_input_singleton",
        "kind": "lemma",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.9780025482177734,
            "y": 0.01579025574028492,
            "z": 0.6673416495323181
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.CE1.mem_input_pair",
        "kind": "lemma",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.8023244738578796,
            "y": 0.05444379150867462,
            "z": 0.15896457433700562
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.CE1.s2_normalForm",
        "kind": "lemma",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.39621901512145996,
            "y": 0.17439530789852142,
            "z": 0.17126064002513885
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.CE1.s0_not_normalForm",
        "kind": "lemma",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.07980149239301682,
            "y": 0.8587010502815247,
            "z": 0.6665210127830505
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.CE1.s1_not_normalForm",
        "kind": "lemma",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.3934578001499176,
            "y": 0.17122027277946472,
            "z": 0.19898535311222076
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.CE1.apply_eq_of_sigma_eq",
        "kind": "lemma",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.9500898122787476,
            "y": 0.022726597264409065,
            "z": 0.500921905040741
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.CE1.sigma0_eq_of_app_s0",
        "kind": "lemma",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.4758031666278839,
            "y": 0.07820206880569458,
            "z": 0.12835629284381866
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.CE1.sigma1_eq_one_or_two_of_app_s0",
        "kind": "lemma",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.9306848645210266,
            "y": 0.02452091872692108,
            "z": 0.4709320068359375
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.CE1.sigma_eq_e12_of_app_s0",
        "kind": "lemma",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.5645714402198792,
            "y": 0.07464613765478134,
            "z": 0.07090778648853302
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.CE1.sigma_eq_e13_of_app_s0",
        "kind": "lemma",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.564057469367981,
            "y": 0.07615462690591812,
            "z": 0.07124586403369904
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.CE1.sigma0_eq_of_app_s1",
        "kind": "lemma",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.4265136122703552,
            "y": 0.1274285465478897,
            "z": 0.19551397860050201
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.CE1.sigma1_eq_two_of_app_s1",
        "kind": "lemma",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.8570806384086609,
            "y": 0.053511861711740494,
            "z": 0.2735653519630432
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.CE1.sigma_eq_e23_of_app_s1",
        "kind": "lemma",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.6857548356056213,
            "y": 0.060726266354322433,
            "z": 0.13324373960494995
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.CE1.final_nf_eq_s2",
        "kind": "lemma",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.29068073630332947,
            "y": 0.4011891782283783,
            "z": 0.27643051743507385
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.CE1.terminatingFrom_init",
        "kind": "theorem",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.0737043023109436,
            "y": 0.8743739128112793,
            "z": 0.7147887349128723
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.CE1.confluentNF",
        "kind": "theorem",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.6705309748649597,
            "y": 0.05925940349698067,
            "z": 0.09662601351737976
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.CE1.not_causalInvariant",
        "kind": "theorem",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.5494562387466431,
            "y": 0.07348045706748962,
            "z": 0.06453873217105865
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.CE2.P",
        "kind": "def",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.09642193466424942,
            "y": 0.8051018118858337,
            "z": 0.5580816864967346
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.CE2.V",
        "kind": "def",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.021935436874628067,
            "y": 0.9945849180221558,
            "z": 0.7914563417434692
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.CE2.rule",
        "kind": "def",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.17245738208293915,
            "y": 0.6330741047859192,
            "z": 0.387975811958313
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.CE2.init",
        "kind": "def",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.02496342733502388,
            "y": 0.9852742552757263,
            "z": 0.7887516021728516
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.CE2.sys",
        "kind": "def",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.008660259656608105,
            "y": 0.9910426735877991,
            "z": 0.9567037224769592
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.CE2.e_id",
        "kind": "def",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.02387092262506485,
            "y": 0.9870776534080505,
            "z": 0.7923875451087952
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.CE2.e_swap",
        "kind": "def",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.1016850695014,
            "y": 0.793008029460907,
            "z": 0.5547503232955933
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.CE2.s0",
        "kind": "def",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.5078672170639038,
            "y": 0.1030513122677803,
            "z": 0.020827043801546097
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.CE2.nf1",
        "kind": "def",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.7947271466255188,
            "y": 0.05042093247175217,
            "z": 0.14497433602809906
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.CE2.nf2",
        "kind": "def",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.9211535453796387,
            "y": 0.030991965904831886,
            "z": 0.3731006979942322
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.CE2.sigma_eq_e_id_or_swap",
        "kind": "lemma",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.9774983525276184,
            "y": 0.016037147492170334,
            "z": 0.6451243162155151
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.CE2.e_id_app",
        "kind": "lemma",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.8997688889503479,
            "y": 0.042138684540987015,
            "z": 0.32432520389556885
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.CE2.e_swap_app",
        "kind": "lemma",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.9079377055168152,
            "y": 0.03833403438329697,
            "z": 0.34108245372772217
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.CE2.e_id_apply",
        "kind": "lemma",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.02924584038555622,
            "y": 0.9762336611747742,
            "z": 0.7796449661254883
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.CE2.e_swap_apply",
        "kind": "lemma",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.1777101755142212,
            "y": 0.6349565982818604,
            "z": 0.42269366979599
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.CE2.idx_eq_zero",
        "kind": "lemma",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.2096874862909317,
            "y": 0.5595017075538635,
            "z": 0.35375216603279114
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.CE2.apply_eq_of_sigma_eq",
        "kind": "lemma",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.9505652785301208,
            "y": 0.020200908184051514,
            "z": 0.4960319399833679
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.CE2.nf1_normalForm",
        "kind": "lemma",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.6574625372886658,
            "y": 0.06409602612257004,
            "z": 0.0946214348077774
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.CE2.nf2_normalForm",
        "kind": "lemma",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.7732117176055908,
            "y": 0.05033710226416588,
            "z": 0.1295790821313858
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.CE2.length_eq_one_of_nf",
        "kind": "lemma",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.5293025374412537,
            "y": 0.06921444833278656,
            "z": 0.08744000643491745
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.CE2.edge_iff_false_of_len_eq_one",
        "kind": "lemma",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.5796501040458679,
            "y": 0.07278861105442047,
            "z": 0.1839999109506607
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.CE2.terminatingFrom_init",
        "kind": "theorem",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.0776624083518982,
            "y": 0.8647275567054749,
            "z": 0.7106718420982361
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.CE2.causalInvariant",
        "kind": "theorem",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.9728994369506836,
            "y": 0.015921855345368385,
            "z": 0.6038647890090942
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.CE2.not_confluentNF",
        "kind": "theorem",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.7574732899665833,
            "y": 0.05050332471728325,
            "z": 0.13221770524978638
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.confluence_causal_invariance_independent",
        "kind": "theorem",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.9255861043930054,
            "y": 0.024900270625948906,
            "z": 0.48599615693092346
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.Counterexamples.CE1.e13_observableB",
        "kind": "lemma",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.2827136814594269,
            "y": 0.4910297393798828,
            "z": 0.565563976764679
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.Counterexamples.CE1.e23_observableB",
        "kind": "lemma",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.28357207775115967,
            "y": 0.48874786496162415,
            "z": 0.5615139603614807
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.Counterexamples.CE1.e12_observableB",
        "kind": "lemma",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.2074737250804901,
            "y": 0.6276074051856995,
            "z": 0.5971809029579163
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.Counterexamples.CE1.idxs_short",
        "kind": "lemma",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.1741560846567154,
            "y": 0.6791906952857971,
            "z": 0.576269805431366
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.Counterexamples.CE1.idxs_long",
        "kind": "lemma",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.3983617424964905,
            "y": 0.17504698038101196,
            "z": 0.29038456082344055
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.Counterexamples.CE1.gc_n_short",
        "kind": "lemma",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.6484836339950562,
            "y": 0.06741005927324295,
            "z": 0.1751103401184082
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.Counterexamples.CE1.gc_n_long",
        "kind": "lemma",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.9181690812110901,
            "y": 0.03562389686703682,
            "z": 0.3967093825340271
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.Counterexamples.CE1.gc_edge_false_short",
        "kind": "lemma",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.9182603359222412,
            "y": 0.02966284193098545,
            "z": 0.47340166568756104
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.Counterexamples.CE1.gc_edge_false_long",
        "kind": "lemma",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.8846094012260437,
            "y": 0.051593612879514694,
            "z": 0.4124162495136261
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.Counterexamples.CE1.causalGraphGC_iso_short_long",
        "kind": "theorem",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.7376828789710999,
            "y": 0.06413352489471436,
            "z": 0.39005783200263977
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.Counterexamples.CE2.s0_not_normalForm",
        "kind": "lemma",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.3864974081516266,
            "y": 0.24835775792598724,
            "z": 0.42071372270584106
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.Counterexamples.CE2.sigma_eq_e_id_or_swap",
        "kind": "lemma",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.8731191158294678,
            "y": 0.053714439272880554,
            "z": 0.40498247742652893
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.Counterexamples.CE2.apply_eq_of_sigma_eq",
        "kind": "lemma",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.7685226798057556,
            "y": 0.059223245829343796,
            "z": 0.3015088140964508
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.Counterexamples.CE2.normalForm_apply_s0_of_app",
        "kind": "lemma",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.7502885460853577,
            "y": 0.06284210085868835,
            "z": 0.3891112208366394
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.Counterexamples.CE2.length_eq_one_of_nf",
        "kind": "lemma",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.4381243586540222,
            "y": 0.18733510375022888,
            "z": 0.443041056394577
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.Counterexamples.CE2.e_observableB_of_evolves_singleton",
        "kind": "lemma",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.4984847903251648,
            "y": 0.20355775952339172,
            "z": 0.5630002021789551
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.Counterexamples.CE2.causalInvariantGC",
        "kind": "theorem",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.792765200138092,
            "y": 0.059668201953172684,
            "z": 0.26350709795951843
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.System.Step",
        "kind": "def",
        "family": "Wolfram",
        "pos": {
            "x": 0.4686495363712311,
            "y": 0.1128176897764206,
            "z": 0.07285942137241364
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.System.StepStar",
        "kind": "def",
        "family": "Wolfram",
        "pos": {
            "x": 0.327048659324646,
            "y": 0.32081660628318787,
            "z": 0.21349933743476868
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.System.NormalFormStep",
        "kind": "def",
        "family": "Wolfram",
        "pos": {
            "x": 0.23264217376708984,
            "y": 0.5250386595726013,
            "z": 0.37783804535865784
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.System.normalForm_iff_normalFormStep",
        "kind": "lemma",
        "family": "Wolfram",
        "pos": {
            "x": 0.30499786138534546,
            "y": 0.4486485719680786,
            "z": 0.5619184374809265
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.System.Evolves",
        "kind": "theorem",
        "family": "Wolfram",
        "pos": {
            "x": 0.3299514055252075,
            "y": 0.31765422224998474,
            "z": 0.20272745192050934
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.System.Evolves",
        "kind": "theorem",
        "family": "Wolfram",
        "pos": {
            "x": 0.3886137902736664,
            "y": 0.1841610223054886,
            "z": 0.17815802991390228
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.System.StepStar",
        "kind": "theorem",
        "family": "Wolfram",
        "pos": {
            "x": 0.2848919630050659,
            "y": 0.41249436140060425,
            "z": 0.27496835589408875
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.System.Joinable",
        "kind": "def",
        "family": "Wolfram",
        "pos": {
            "x": 0.5363339185714722,
            "y": 0.0892781987786293,
            "z": 0.03243490681052208
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.System.Confluent",
        "kind": "def",
        "family": "Wolfram",
        "pos": {
            "x": 0.6579141616821289,
            "y": 0.0644301027059555,
            "z": 0.09013447910547256
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.System.SemiConfluent",
        "kind": "def",
        "family": "Wolfram",
        "pos": {
            "x": 0.6504828929901123,
            "y": 0.06583970040082932,
            "z": 0.08908707648515701
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.System.semiConfluent_confluent",
        "kind": "theorem",
        "family": "Wolfram",
        "pos": {
            "x": 0.7367655038833618,
            "y": 0.05541994050145149,
            "z": 0.16548800468444824
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.System.BoundedFrom",
        "kind": "def",
        "family": "Wolfram",
        "pos": {
            "x": 0.5381942987442017,
            "y": 0.08197353035211563,
            "z": 0.04116571322083473
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.System.TerminatingFrom",
        "kind": "def",
        "family": "Wolfram",
        "pos": {
            "x": 0.01916702464222908,
            "y": 0.9684967994689941,
            "z": 0.9597944617271423
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.FreshSupply",
        "kind": "class",
        "family": "Wolfram",
        "pos": {
            "x": 0.08612916618585587,
            "y": 0.8298447728157043,
            "z": 0.5958207249641418
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.FreshSupply.fresh_not_mem",
        "kind": "lemma",
        "family": "Wolfram",
        "pos": {
            "x": 0.5260100960731506,
            "y": 0.06800944358110428,
            "z": 0.10672196000814438
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.FreshSupply.allocList",
        "kind": "def",
        "family": "Wolfram",
        "pos": {
            "x": 0.1950748860836029,
            "y": 0.6168161630630493,
            "z": 0.46925944089889526
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.FreshSupply.allocList_length",
        "kind": "lemma",
        "family": "Wolfram",
        "pos": {
            "x": 0.3920770287513733,
            "y": 0.18647262454032898,
            "z": 0.292804479598999
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.FreshSupply.allocList_mem_not_mem_forbidden",
        "kind": "lemma",
        "family": "Wolfram",
        "pos": {
            "x": 0.3610013723373413,
            "y": 0.3535926342010498,
            "z": 0.5550896525382996
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.FreshSupply.allocList_nodup",
        "kind": "lemma",
        "family": "Wolfram",
        "pos": {
            "x": 0.2241743505001068,
            "y": 0.5648728609085083,
            "z": 0.46927961707115173
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.FreshSupply.allocVec",
        "kind": "def",
        "family": "Wolfram",
        "pos": {
            "x": 0.8136522173881531,
            "y": 0.056463420391082764,
            "z": 0.18350771069526672
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.FreshSupply.alloc",
        "kind": "def",
        "family": "Wolfram",
        "pos": {
            "x": 0.3912574052810669,
            "y": 0.17221838235855103,
            "z": 0.1807692050933838
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.FreshSupply.alloc_injective",
        "kind": "lemma",
        "family": "Wolfram",
        "pos": {
            "x": 0.7702803611755371,
            "y": 0.05307754874229431,
            "z": 0.16482019424438477
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.FreshSupply.alloc_not_mem",
        "kind": "lemma",
        "family": "Wolfram",
        "pos": {
            "x": 0.9951655864715576,
            "y": 0.009911305271089077,
            "z": 0.8114669322967529
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.instFreshSupply_ofInfinite",
        "kind": "instance",
        "family": "Wolfram",
        "pos": {
            "x": 0.4812374413013458,
            "y": 0.0801476538181305,
            "z": 0.18503504991531372
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.Expr",
        "kind": "def",
        "family": "Wolfram",
        "pos": {
            "x": 0.18267393112182617,
            "y": 0.6068966388702393,
            "z": 0.365429550409317
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.HGraph",
        "kind": "def",
        "family": "Wolfram",
        "pos": {
            "x": 0.17407800257205963,
            "y": 0.628687858581543,
            "z": 0.3788222074508667
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.Expr.rename",
        "kind": "def",
        "family": "Wolfram",
        "pos": {
            "x": 0.186826691031456,
            "y": 0.6043341159820557,
            "z": 0.37352773547172546
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.Expr.rename_id",
        "kind": "lemma",
        "family": "Wolfram",
        "pos": {
            "x": 0.29871222376823425,
            "y": 0.3849456310272217,
            "z": 0.25404372811317444
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.Expr.rename_comp",
        "kind": "lemma",
        "family": "Wolfram",
        "pos": {
            "x": 0.2869587242603302,
            "y": 0.4081972539424896,
            "z": 0.26835504174232483
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.HGraph.rename",
        "kind": "def",
        "family": "Wolfram",
        "pos": {
            "x": 0.3244324028491974,
            "y": 0.3309558033943176,
            "z": 0.21178582310676575
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.HGraph.rename_id",
        "kind": "lemma",
        "family": "Wolfram",
        "pos": {
            "x": 0.31570857763290405,
            "y": 0.3519973158836365,
            "z": 0.2263612598180771
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.HGraph.rename_comp",
        "kind": "lemma",
        "family": "Wolfram",
        "pos": {
            "x": 0.792479395866394,
            "y": 0.05591496825218201,
            "z": 0.15332737565040588
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.HGraph.Iso",
        "kind": "def",
        "family": "Wolfram",
        "pos": {
            "x": 0.19374342262744904,
            "y": 0.5881189703941345,
            "z": 0.3536653518676758
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.HGraph.Iso",
        "kind": "lemma",
        "family": "Wolfram",
        "pos": {
            "x": 0.20595912635326385,
            "y": 0.5639297962188721,
            "z": 0.340714693069458
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.HGraph.Iso",
        "kind": "lemma",
        "family": "Wolfram",
        "pos": {
            "x": 0.44506213068962097,
            "y": 0.13253383338451385,
            "z": 0.09944380819797516
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.HGraph.Iso",
        "kind": "lemma",
        "family": "Wolfram",
        "pos": {
            "x": 0.49879953265190125,
            "y": 0.09727365523576736,
            "z": 0.042570702731609344
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.HGraph.vertsStep",
        "kind": "def",
        "family": "Wolfram",
        "pos": {
            "x": 0.3197636902332306,
            "y": 0.3405298590660095,
            "z": 0.21606311202049255
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.HGraph.instRightCommutative_vertsStep",
        "kind": "instance",
        "family": "Wolfram",
        "pos": {
            "x": 0.28355035185813904,
            "y": 0.49792906641960144,
            "z": 0.5909757614135742
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.HGraph.verts",
        "kind": "def",
        "family": "Wolfram",
        "pos": {
            "x": 0.5150861144065857,
            "y": 0.09610557556152344,
            "z": 0.028361491858959198
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.HGraph.mem_foldl_of_mem_acc",
        "kind": "lemma",
        "family": "Wolfram",
        "pos": {
            "x": 0.5321294069290161,
            "y": 0.06787516176700592,
            "z": 0.14102201163768768
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.HGraph.foldl_mono",
        "kind": "lemma",
        "family": "Wolfram",
        "pos": {
            "x": 0.6727396845817566,
            "y": 0.05967990681529045,
            "z": 0.09973078221082687
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.HGraph.mem_verts_of_mem",
        "kind": "lemma",
        "family": "Wolfram",
        "pos": {
            "x": 0.5188941359519958,
            "y": 0.07019011676311493,
            "z": 0.08902943134307861
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.System.EventData",
        "kind": "def",
        "family": "Wolfram/Multiway",
        "pos": {
            "x": 0.012065780349075794,
            "y": 0.9864028096199036,
            "z": 0.9679139852523804
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.System.EventData.Applicable",
        "kind": "def",
        "family": "Wolfram/Multiway",
        "pos": {
            "x": 0.3825027048587799,
            "y": 0.20537538826465607,
            "z": 0.2825187146663666
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.System.EventData.apply",
        "kind": "def",
        "family": "Wolfram/Multiway",
        "pos": {
            "x": 0.2609398066997528,
            "y": 0.4686630070209503,
            "z": 0.348143607378006
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.System.allSubsts",
        "kind": "def",
        "family": "Wolfram/Multiway",
        "pos": {
            "x": 0.5437838435173035,
            "y": 0.08458775281906128,
            "z": 0.03814532607793808
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.System.mem_allSubsts",
        "kind": "lemma",
        "family": "Wolfram/Multiway",
        "pos": {
            "x": 0.8793458342552185,
            "y": 0.047034867107868195,
            "z": 0.29176121950149536
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.System.allInjSubsts",
        "kind": "def",
        "family": "Wolfram/Multiway",
        "pos": {
            "x": 0.6626263856887817,
            "y": 0.0686807632446289,
            "z": 0.10304484516382217
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.System.mem_allInjSubsts_iff",
        "kind": "lemma",
        "family": "Wolfram/Multiway",
        "pos": {
            "x": 0.6343482136726379,
            "y": 0.06689028441905975,
            "z": 0.13981343805789948
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.System.allEventData",
        "kind": "def",
        "family": "Wolfram/Multiway",
        "pos": {
            "x": 0.5158833265304565,
            "y": 0.07476296275854111,
            "z": 0.059856098145246506
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.System.mem_allEventData_iff",
        "kind": "lemma",
        "family": "Wolfram/Multiway",
        "pos": {
            "x": 0.6909670829772949,
            "y": 0.06144103780388832,
            "z": 0.1555263102054596
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.System.stepEdges",
        "kind": "def",
        "family": "Wolfram/Multiway",
        "pos": {
            "x": 0.7637166976928711,
            "y": 0.04990403354167938,
            "z": 0.1259172111749649
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.System.mem_stepEdges_iff",
        "kind": "lemma",
        "family": "Wolfram/Multiway",
        "pos": {
            "x": 0.39514634013175964,
            "y": 0.16955016553401947,
            "z": 0.24187202751636505
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.System.stepStates",
        "kind": "def",
        "family": "Wolfram/Multiway",
        "pos": {
            "x": 0.20085950195789337,
            "y": 0.586452841758728,
            "z": 0.3967224359512329
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.System.mem_stepStates_iff",
        "kind": "lemma",
        "family": "Wolfram/Multiway",
        "pos": {
            "x": 0.33590930700302124,
            "y": 0.31113529205322266,
            "z": 0.31964975595474243
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.System.toWppRule",
        "kind": "def",
        "family": "Wolfram/Multiway",
        "pos": {
            "x": 0.3240053951740265,
            "y": 0.3329940438270569,
            "z": 0.21979039907455444
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.System.statesAtDepth",
        "kind": "def",
        "family": "Wolfram/Multiway",
        "pos": {
            "x": 0.05655788257718086,
            "y": 0.9134311676025391,
            "z": 0.7528554201126099
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.Ordering",
        "kind": "structure",
        "family": "Wolfram/Multiway",
        "pos": {
            "x": 0.08189858496189117,
            "y": 0.8422154188156128,
            "z": 0.6022315621376038
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.Ordering.EvolvesBy",
        "kind": "inductive",
        "family": "Wolfram/Multiway",
        "pos": {
            "x": 0.8096323609352112,
            "y": 0.04560733214020729,
            "z": 0.17292413115501404
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.Ordering.EvolvesBy",
        "kind": "theorem",
        "family": "Wolfram/Multiway",
        "pos": {
            "x": 0.4990098178386688,
            "y": 0.07823929190635681,
            "z": 0.07928598672151566
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.System.stepStates_iff_step",
        "kind": "theorem",
        "family": "Wolfram/Multiway",
        "pos": {
            "x": 0.42036035656929016,
            "y": 0.13487306237220764,
            "z": 0.22794108092784882
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.System.wpp_stepStar_iff_stepStar",
        "kind": "theorem",
        "family": "Wolfram/Multiway",
        "pos": {
            "x": 0.27521684765815735,
            "y": 0.5042511224746704,
            "z": 0.5672982931137085
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.System.toWppRel",
        "kind": "def",
        "family": "Wolfram/Multiway",
        "pos": {
            "x": 0.17330694198608398,
            "y": 0.6428578495979309,
            "z": 0.42431455850601196
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.System.toWppRel_stepRel",
        "kind": "theorem",
        "family": "Wolfram/Multiway",
        "pos": {
            "x": 0.4933101236820221,
            "y": 0.07021860778331757,
            "z": 0.11581443250179291
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.System.toWppRel_stepStar_iff",
        "kind": "theorem",
        "family": "Wolfram/Multiway",
        "pos": {
            "x": 0.11704729497432709,
            "y": 0.7975986003875732,
            "z": 0.6735712289810181
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.Rule",
        "kind": "structure",
        "family": "Wolfram",
        "pos": {
            "x": 0.006732848007231951,
            "y": 0.9642102718353271,
            "z": 0.9996039271354675
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.Rule.inst",
        "kind": "def",
        "family": "Wolfram",
        "pos": {
            "x": 0.18982261419296265,
            "y": 0.5961992144584656,
            "z": 0.35967957973480225
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.Rule.instLhs",
        "kind": "def",
        "family": "Wolfram",
        "pos": {
            "x": 0.19776959717273712,
            "y": 0.5810765027999878,
            "z": 0.3560711443424225
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.Rule.instRhs",
        "kind": "def",
        "family": "Wolfram",
        "pos": {
            "x": 0.16053952276706696,
            "y": 0.6557477712631226,
            "z": 0.41884946823120117
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.System",
        "kind": "structure",
        "family": "Wolfram",
        "pos": {
            "x": 0.005658248905092478,
            "y": 0.9948952794075012,
            "z": 0.9596368670463562
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.System.Event",
        "kind": "structure",
        "family": "Wolfram",
        "pos": {
            "x": 0.006956824101507664,
            "y": 0.9804037809371948,
            "z": 0.9830392003059387
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.System.Event.input",
        "kind": "def",
        "family": "Wolfram",
        "pos": {
            "x": 0.38836321234703064,
            "y": 0.18828333914279938,
            "z": 0.18270470201969147
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.System.Event.output",
        "kind": "def",
        "family": "Wolfram",
        "pos": {
            "x": 0.389056533575058,
            "y": 0.17889364063739777,
            "z": 0.19020427763462067
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.System.Event.Applicable",
        "kind": "def",
        "family": "Wolfram",
        "pos": {
            "x": 0.3251546323299408,
            "y": 0.3310413658618927,
            "z": 0.29263317584991455
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.System.Event.decidableApplicable",
        "kind": "instance",
        "family": "Wolfram",
        "pos": {
            "x": 0.2171877920627594,
            "y": 0.6044486165046692,
            "z": 0.5760789513587952
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.System.Event.apply",
        "kind": "def",
        "family": "Wolfram",
        "pos": {
            "x": 0.39174729585647583,
            "y": 0.17862410843372345,
            "z": 0.17826826870441437
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.System.Event.Causes",
        "kind": "def",
        "family": "Wolfram",
        "pos": {
            "x": 0.018105298280715942,
            "y": 0.9799310564994812,
            "z": 0.9333111047744751
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.System.Evolves",
        "kind": "inductive",
        "family": "Wolfram",
        "pos": {
            "x": 0.4937739968299866,
            "y": 0.09110647439956665,
            "z": 0.05335569381713867
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.System.Reachable",
        "kind": "def",
        "family": "Wolfram",
        "pos": {
            "x": 0.32936540246009827,
            "y": 0.317406564950943,
            "z": 0.2156061828136444
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.System.NormalForm",
        "kind": "def",
        "family": "Wolfram",
        "pos": {
            "x": 0.017760585993528366,
            "y": 0.9829148650169373,
            "z": 0.9260273575782776
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.RuleFresh",
        "kind": "structure",
        "family": "Wolfram",
        "pos": {
            "x": 0.021850651130080223,
            "y": 0.9895686507225037,
            "z": 0.8103424906730652
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.RuleFresh.instLhs",
        "kind": "def",
        "family": "Wolfram",
        "pos": {
            "x": 0.5187388062477112,
            "y": 0.08626879751682281,
            "z": 0.03582005202770233
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.RuleFresh.instRhs",
        "kind": "def",
        "family": "Wolfram",
        "pos": {
            "x": 0.7737589478492737,
            "y": 0.045767609030008316,
            "z": 0.12222270667552948
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.RuleFresh.WellFormed",
        "kind": "def",
        "family": "Wolfram",
        "pos": {
            "x": 0.28814196586608887,
            "y": 0.4076058566570282,
            "z": 0.2826090455055237
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.SystemFresh",
        "kind": "structure",
        "family": "Wolfram",
        "pos": {
            "x": 0.02236824482679367,
            "y": 0.9859920740127563,
            "z": 0.8373773097991943
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.SystemFresh.Event",
        "kind": "structure",
        "family": "Wolfram",
        "pos": {
            "x": 0.013084321282804012,
            "y": 0.9786223769187927,
            "z": 0.9649461507797241
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.SystemFresh.Event.rule",
        "kind": "def",
        "family": "Wolfram",
        "pos": {
            "x": 0.220857173204422,
            "y": 0.5558042526245117,
            "z": 0.4150969684123993
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.SystemFresh.Event.input",
        "kind": "def",
        "family": "Wolfram",
        "pos": {
            "x": 0.7372956275939941,
            "y": 0.05246914550662041,
            "z": 0.13044606149196625
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.SystemFresh.Event.FreshAssign",
        "kind": "def",
        "family": "Wolfram",
        "pos": {
            "x": 0.7241054177284241,
            "y": 0.05647704005241394,
            "z": 0.16297738254070282
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.SystemFresh.Event.Applicable",
        "kind": "def",
        "family": "Wolfram",
        "pos": {
            "x": 0.27378007769584656,
            "y": 0.45379146933555603,
            "z": 0.3848125636577606
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.SystemFresh.Event.decidableApplicable",
        "kind": "instance",
        "family": "Wolfram",
        "pos": {
            "x": 0.17977240681648254,
            "y": 0.6880244612693787,
            "z": 0.6502833962440491
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.SystemFresh.Event.applyWith",
        "kind": "def",
        "family": "Wolfram",
        "pos": {
            "x": 0.9741913676261902,
            "y": 0.01559046097099781,
            "z": 0.6307234764099121
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.SystemFresh.Event.apply",
        "kind": "def",
        "family": "Wolfram",
        "pos": {
            "x": 0.9726181030273438,
            "y": 0.01412887591868639,
            "z": 0.6038772463798523
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.SystemFresh.Event.freshAssign_alloc",
        "kind": "lemma",
        "family": "Wolfram",
        "pos": {
            "x": 0.6366121172904968,
            "y": 0.07214193791151047,
            "z": 0.2042405605316162
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.SystemFresh.Event.rangeFinset",
        "kind": "def",
        "family": "Wolfram",
        "pos": {
            "x": 0.40126195549964905,
            "y": 0.1672074794769287,
            "z": 0.2821817100048065
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.SystemFresh.Event.mem_rangeFinset",
        "kind": "lemma",
        "family": "Wolfram",
        "pos": {
            "x": 0.4651503264904022,
            "y": 0.1284985989332199,
            "z": 0.33574098348617554
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.SystemFresh.Event.CrossDisjoint",
        "kind": "def",
        "family": "Wolfram",
        "pos": {
            "x": 0.4509281516075134,
            "y": 0.12471658736467361,
            "z": 0.29015374183654785
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.SystemFresh.Event.crossDisjoint_of_not_mem_range",
        "kind": "lemma",
        "family": "Wolfram",
        "pos": {
            "x": 0.6508811116218567,
            "y": 0.09320830553770065,
            "z": 0.416713684797287
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.SystemFresh.Event.swapPerm",
        "kind": "def",
        "family": "Wolfram",
        "pos": {
            "x": 0.3746604919433594,
            "y": 0.21679508686065674,
            "z": 0.27099913358688354
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.SystemFresh.Event.swapPerm_apply_of_forall_ne",
        "kind": "lemma",
        "family": "Wolfram",
        "pos": {
            "x": 0.3593669533729553,
            "y": 0.3656894862651825,
            "z": 0.5749194025993347
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.SystemFresh.Event.swapPerm_apply_left",
        "kind": "lemma",
        "family": "Wolfram",
        "pos": {
            "x": 0.469713419675827,
            "y": 0.1582891047000885,
            "z": 0.42646583914756775
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.SystemFresh.Event.swapPerm_fix_of_mem_verts",
        "kind": "lemma",
        "family": "Wolfram",
        "pos": {
            "x": 0.8348114490509033,
            "y": 0.06546073406934738,
            "z": 0.3521691560745239
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.SystemFresh.Event.expr_rename_eq_self_of_forall_mem",
        "kind": "lemma",
        "family": "Wolfram",
        "pos": {
            "x": 0.3277577757835388,
            "y": 0.4411580264568329,
            "z": 0.6240827441215515
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.SystemFresh.Event.hgraph_rename_eq_self_of_forall_mem",
        "kind": "lemma",
        "family": "Wolfram",
        "pos": {
            "x": 0.4803338944911957,
            "y": 0.2230987548828125,
            "z": 0.5758832097053528
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.SystemFresh.Event.hgraph_rename_eq_self_of_fix_verts",
        "kind": "lemma",
        "family": "Wolfram",
        "pos": {
            "x": 0.7742301821708679,
            "y": 0.06224597617983818,
            "z": 0.45322301983833313
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.SystemFresh.Event.hgraph_rename_eq_self_of_le",
        "kind": "lemma",
        "family": "Wolfram",
        "pos": {
            "x": 0.9324187636375427,
            "y": 0.017646731808781624,
            "z": 0.5496136546134949
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.SystemFresh.Event.sigma_mem_verts_of_inLhs",
        "kind": "lemma",
        "family": "Wolfram",
        "pos": {
            "x": 0.9515489935874939,
            "y": 0.016832970082759857,
            "z": 0.5717647075653076
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.SystemFresh.Event.sigma_fixed_of_inRhs",
        "kind": "lemma",
        "family": "Wolfram",
        "pos": {
            "x": 0.888577938079834,
            "y": 0.04963115230202675,
            "z": 0.4239005744457245
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.SystemFresh.Event.applyWith_rename_of_crossDisjoint",
        "kind": "lemma",
        "family": "Wolfram",
        "pos": {
            "x": 0.848487138748169,
            "y": 0.05442431941628456,
            "z": 0.4686453640460968
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.SystemFresh.Event.applyWith_iso_of_crossDisjoint",
        "kind": "lemma",
        "family": "Wolfram",
        "pos": {
            "x": 0.7769408226013184,
            "y": 0.06188484653830528,
            "z": 0.4420190453529358
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.SystemFresh.Event.applyWith_iso",
        "kind": "lemma",
        "family": "Wolfram",
        "pos": {
            "x": 0.6806159615516663,
            "y": 0.06337568908929825,
            "z": 0.18544498085975647
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.HGraph.SimpleEdges",
        "kind": "def",
        "family": "Wolfram",
        "pos": {
            "x": 0.01364936400204897,
            "y": 0.9703179001808167,
            "z": 0.9752059578895569
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.System.Event.injectiveOn_of_applicable_of_mem_lhs",
        "kind": "lemma",
        "family": "Wolfram",
        "pos": {
            "x": 0.8450205326080322,
            "y": 0.05653305724263191,
            "z": 0.4567585587501526
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.System.Event.injective_of_applicable_of_finRange_mem_lhs",
        "kind": "theorem",
        "family": "Wolfram",
        "pos": {
            "x": 0.775054931640625,
            "y": 0.06293188035488129,
            "z": 0.47152456641197205
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.SystemFresh.Event.injectiveOn_of_applicable_of_mem_lhs",
        "kind": "lemma",
        "family": "Wolfram",
        "pos": {
            "x": 0.7554659247398376,
            "y": 0.06415530294179916,
            "z": 0.44296762347221375
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.SystemFresh.Event.injective_of_applicable_of_finRange_mem_lhs",
        "kind": "theorem",
        "family": "Wolfram",
        "pos": {
            "x": 0.7046923637390137,
            "y": 0.08107364177703857,
            "z": 0.48732608556747437
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.WM148.P",
        "kind": "def",
        "family": "Wolfram/WM148",
        "pos": {
            "x": 0.019820628687739372,
            "y": 0.9981718063354492,
            "z": 0.800868809223175
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.WM148.V",
        "kind": "def",
        "family": "Wolfram/WM148",
        "pos": {
            "x": 0.09843234717845917,
            "y": 0.8003247976303101,
            "z": 0.5593133568763733
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.WM148.rule",
        "kind": "def",
        "family": "Wolfram/WM148",
        "pos": {
            "x": 0.14835800230503082,
            "y": 0.6891838908195496,
            "z": 0.44694074988365173
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.WM148.init",
        "kind": "def",
        "family": "Wolfram/WM148",
        "pos": {
            "x": 0.01695977710187435,
            "y": 0.9876800179481506,
            "z": 0.9000702500343323
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.WM148.sys",
        "kind": "def",
        "family": "Wolfram/WM148",
        "pos": {
            "x": 0.026368537917733192,
            "y": 0.9816416501998901,
            "z": 0.7804656624794006
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.WM148.sys_rules_length",
        "kind": "lemma",
        "family": "Wolfram/WM148",
        "pos": {
            "x": 0.08702531456947327,
            "y": 0.8429999947547913,
            "z": 0.6553777456283569
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.WM148.rule_wellFormed",
        "kind": "lemma",
        "family": "Wolfram/WM148",
        "pos": {
            "x": 0.12432190030813217,
            "y": 0.7689425945281982,
            "z": 0.6032106876373291
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.WM148.freshNat",
        "kind": "def",
        "family": "Wolfram/WM148",
        "pos": {
            "x": 0.16213323175907135,
            "y": 0.6589341759681702,
            "z": 0.4257599711418152
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.WM148.freshNat_not_mem",
        "kind": "lemma",
        "family": "Wolfram/WM148",
        "pos": {
            "x": 0.7962737083435059,
            "y": 0.05312099680304527,
            "z": 0.15506583452224731
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.WM148.allocFreshNat",
        "kind": "def",
        "family": "Wolfram/WM148",
        "pos": {
            "x": 0.4606783092021942,
            "y": 0.1061793640255928,
            "z": 0.10177812725305557
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.WM148.allocFreshNat_injective",
        "kind": "lemma",
        "family": "Wolfram/WM148",
        "pos": {
            "x": 0.29256686568260193,
            "y": 0.41604310274124146,
            "z": 0.3729468286037445
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.WM148.allocFreshNat_not_mem",
        "kind": "lemma",
        "family": "Wolfram/WM148",
        "pos": {
            "x": 0.6231014132499695,
            "y": 0.06869237124919891,
            "z": 0.1412043571472168
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.WM148.idx0",
        "kind": "def",
        "family": "Wolfram/WM148",
        "pos": {
            "x": 0.1743660420179367,
            "y": 0.6327345967292786,
            "z": 0.39517366886138916
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.WM148.mkEvent",
        "kind": "def",
        "family": "Wolfram/WM148",
        "pos": {
            "x": 0.6858624219894409,
            "y": 0.05848698318004608,
            "z": 0.09424668550491333
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.WM148.applyDet",
        "kind": "def",
        "family": "Wolfram/WM148",
        "pos": {
            "x": 0.08284302055835724,
            "y": 0.8413000106811523,
            "z": 0.6109280586242676
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.WM148.expr_rename_eq_self_of_forall_mem",
        "kind": "lemma",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.3327687978744507,
            "y": 0.39601099491119385,
            "z": 0.5461872816085815
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.WM148.hgraph_rename_eq_self_of_forall_mem",
        "kind": "lemma",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.5061847567558289,
            "y": 0.15206044912338257,
            "z": 0.4593367576599121
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.WM148.hgraph_rename_eq_self_of_fix_verts",
        "kind": "lemma",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.8302919268608093,
            "y": 0.06764428317546844,
            "z": 0.32760724425315857
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.WM148.multiset_foldl_singleton",
        "kind": "lemma",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.9111892580986023,
            "y": 0.044685184955596924,
            "z": 0.37375178933143616
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.WM148.verts_add_singleton",
        "kind": "lemma",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.9611477255821228,
            "y": 0.01850586012005806,
            "z": 0.5385974049568176
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.WM148.wm148_rule_eq",
        "kind": "lemma",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.5480998158454895,
            "y": 0.0850597620010376,
            "z": 0.040745917707681656
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.WM148.wm148_nFresh",
        "kind": "lemma",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.5175741910934448,
            "y": 0.07457908987998962,
            "z": 0.05743883177638054
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.WM148.fresh0",
        "kind": "def",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.32778400182724,
            "y": 0.324361115694046,
            "z": 0.2001885324716568
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.WM148.input_eq_singleton",
        "kind": "lemma",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.9163089990615845,
            "y": 0.03241182491183281,
            "z": 0.3577554523944855
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.WM148.instRhs_eq_input_add_new",
        "kind": "lemma",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.7866304516792297,
            "y": 0.055806007236242294,
            "z": 0.20988307893276215
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.WM148.applyWith_eq_add_new",
        "kind": "lemma",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.9044250249862671,
            "y": 0.04199787601828575,
            "z": 0.3437868356704712
        }
    },
    {
        "name": "HeytingLean.WPP.Wolfram.WM148.causalInvariant",
        "kind": "theorem",
        "family": "Wolfram/Causal",
        "pos": {
            "x": 0.24066010117530823,
            "y": 0.510138750076294,
            "z": 0.37455132603645325
        }
    },
    {
        "name": "HeytingLean.CLI.Certified.die",
        "kind": "def",
        "family": "CLI",
        "pos": {
            "x": 0.02012438140809536,
            "y": 0.9990145564079285,
            "z": 0.7929171919822693
        }
    },
    {
        "name": "HeytingLean.CLI.Certified.okJson",
        "kind": "def",
        "family": "CLI",
        "pos": {
            "x": 0.16503417491912842,
            "y": 0.6506657004356384,
            "z": 0.40692517161369324
        }
    },
    {
        "name": "HeytingLean.CLI.Certified.readInputJson",
        "kind": "def",
        "family": "CLI",
        "pos": {
            "x": 0.20989249646663666,
            "y": 0.5571586489677429,
            "z": 0.3409690856933594
        }
    },
    {
        "name": "HeytingLean.CLI.Certified.getString",
        "kind": "def",
        "family": "CLI",
        "pos": {
            "x": 0.15659435093402863,
            "y": 0.6623050570487976,
            "z": 0.4209859371185303
        }
    },
    {
        "name": "HeytingLean.CLI.Certified.getNat",
        "kind": "def",
        "family": "CLI",
        "pos": {
            "x": 0.10268916189670563,
            "y": 0.7894189953804016,
            "z": 0.5513511896133423
        }
    },
    {
        "name": "HeytingLean.CLI.Certified.getInt",
        "kind": "def",
        "family": "CLI",
        "pos": {
            "x": 0.10191165655851364,
            "y": 0.7911065816879272,
            "z": 0.5491771697998047
        }
    },
    {
        "name": "HeytingLean.CLI.defaultBundlePath",
        "kind": "def",
        "family": "Seismic",
        "pos": {
            "x": 0.0743393823504448,
            "y": 0.8595165610313416,
            "z": 0.6125732064247131
        }
    },
    {
        "name": "HeytingLean.CLI.defaultBundlePathAlt",
        "kind": "def",
        "family": "Seismic",
        "pos": {
            "x": 0.15733039379119873,
            "y": 0.6729153990745544,
            "z": 0.4291239380836487
        }
    },
    {
        "name": "HeytingLean.CLI.fileExists",
        "kind": "def",
        "family": "Seismic",
        "pos": {
            "x": 0.17133884131908417,
            "y": 0.6348506808280945,
            "z": 0.3844260275363922
        }
    },
    {
        "name": "HeytingLean.CLI.findDefaultBundlePath",
        "kind": "def",
        "family": "Seismic",
        "pos": {
            "x": 0.32802635431289673,
            "y": 0.32588276267051697,
            "z": 0.1938043087720871
        }
    },
    {
        "name": "HeytingLean.CLI.readInputJson",
        "kind": "def",
        "family": "Seismic",
        "pos": {
            "x": 0.3344373106956482,
            "y": 0.3098379373550415,
            "z": 0.18533243238925934
        }
    },
    {
        "name": "HeytingLean.CLI.getFloat",
        "kind": "def",
        "family": "Seismic",
        "pos": {
            "x": 0.16057465970516205,
            "y": 0.6573047041893005,
            "z": 0.40187913179397583
        }
    },
    {
        "name": "HeytingLean.CLI.getFloatArray",
        "kind": "def",
        "family": "Seismic",
        "pos": {
            "x": 0.1816500574350357,
            "y": 0.6056259274482727,
            "z": 0.36265313625335693
        }
    },
    {
        "name": "HeytingLean.CLI.Bundle",
        "kind": "structure",
        "family": "Seismic",
        "pos": {
            "x": 0.016963375732302666,
            "y": 0.9997608065605164,
            "z": 0.8169835805892944
        }
    },
    {
        "name": "HeytingLean.CLI.ValidationOutput",
        "kind": "structure",
        "family": "Seismic",
        "pos": {
            "x": 0.7612351179122925,
            "y": 0.04923184961080551,
            "z": 0.11983464658260345
        }
    },
    {
        "name": "HeytingLean.CLI.parseBundle",
        "kind": "def",
        "family": "Seismic",
        "pos": {
            "x": 0.4864582419395447,
            "y": 0.11491117626428604,
            "z": 0.03917405754327774
        }
    },
    {
        "name": "HeytingLean.CLI.getBool",
        "kind": "def",
        "family": "Seismic",
        "pos": {
            "x": 0.16476552188396454,
            "y": 0.643040120601654,
            "z": 0.3958509862422943
        }
    },
    {
        "name": "HeytingLean.CLI.getString",
        "kind": "def",
        "family": "Seismic",
        "pos": {
            "x": 0.3324178457260132,
            "y": 0.31491366028785706,
            "z": 0.1909935474395752
        }
    },
    {
        "name": "HeytingLean.CLI.parseDetectionParams",
        "kind": "def",
        "family": "Seismic",
        "pos": {
            "x": 0.6640626192092896,
            "y": 0.0634264275431633,
            "z": 0.09048782289028168
        }
    },
    {
        "name": "HeytingLean.CLI.mkKey",
        "kind": "def",
        "family": "Seismic",
        "pos": {
            "x": 0.5253827571868896,
            "y": 0.10961636155843735,
            "z": 0.0058676633052527905
        }
    },
    {
        "name": "HeytingLean.CLI.validateBundle",
        "kind": "def",
        "family": "Seismic",
        "pos": {
            "x": 0.49899208545684814,
            "y": 0.11041880398988724,
            "z": 0.027604294940829277
        }
    },
    {
        "name": "HeytingLean.CLI.main",
        "kind": "def",
        "family": "Seismic",
        "pos": {
            "x": 0.5122209191322327,
            "y": 0.11483156681060791,
            "z": 0.00841367058455944
        }
    },
    {
        "name": "main",
        "kind": "def",
        "family": "Seismic",
        "pos": {
            "x": 0.002237094799056649,
            "y": 0.9787157773971558,
            "z": 0.9918767809867859
        }
    },
    {
        "name": "_WolframFreshAnchor",
        "kind": "def",
        "family": "Wolfram/Multiway",
        "pos": {
            "x": 0.3633594512939453,
            "y": 0.261416494846344,
            "z": 0.14292022585868835
        }
    },
    {
        "name": "_WolframSimpleEdgesAnchor",
        "kind": "def",
        "family": "Wolfram/Multiway",
        "pos": {
            "x": 0.1625530868768692,
            "y": 0.6524662971496582,
            "z": 0.3971015512943268
        }
    },
    {
        "name": "Args",
        "kind": "structure",
        "family": "Wolfram/Multiway",
        "pos": {
            "x": 0.10078588873147964,
            "y": 0.7926514148712158,
            "z": 0.5478360652923584
        }
    },
    {
        "name": "parseArg",
        "kind": "def",
        "family": "Wolfram/Multiway",
        "pos": {
            "x": 0.17095617949962616,
            "y": 0.634525716304779,
            "z": 0.3820091784000397
        }
    },
    {
        "name": "parseArgs",
        "kind": "def",
        "family": "Wolfram/Multiway",
        "pos": {
            "x": 0.3630807399749756,
            "y": 0.2653229832649231,
            "z": 0.14030835032463074
        }
    },
    {
        "name": "exprToJson",
        "kind": "def",
        "family": "Wolfram/Multiway",
        "pos": {
            "x": 0.35834452509880066,
            "y": 0.27559417486190796,
            "z": 0.14773505926132202
        }
    },
    {
        "name": "sigmaFin2ToJson",
        "kind": "def",
        "family": "Wolfram/Multiway",
        "pos": {
            "x": 0.5115804076194763,
            "y": 0.11540956050157547,
            "z": 0.00580940768122673
        }
    },
    {
        "name": "eventDataToJson",
        "kind": "def",
        "family": "Wolfram/Multiway",
        "pos": {
            "x": 0.515331506729126,
            "y": 0.11927156895399094,
            "z": 0.0013258543331176043
        }
    },
    {
        "name": "mkBasisLen1Len2",
        "kind": "def",
        "family": "Wolfram/Multiway",
        "pos": {
            "x": 0.3622179925441742,
            "y": 0.2643408179283142,
            "z": 0.14415667951107025
        }
    },
    {
        "name": "stateToCountsJson",
        "kind": "def",
        "family": "Wolfram/Multiway",
        "pos": {
            "x": 0.773684024810791,
            "y": 0.04669925197958946,
            "z": 0.11388775706291199
        }
    },
    {
        "name": "allSigmasFin2",
        "kind": "def",
        "family": "Wolfram/Multiway",
        "pos": {
            "x": 0.3494434654712677,
            "y": 0.2861103415489197,
            "z": 0.16027726233005524
        }
    },
    {
        "name": "findIdxFuel",
        "kind": "def",
        "family": "Wolfram/Multiway",
        "pos": {
            "x": 0.4909510016441345,
            "y": 0.1385827511548996,
            "z": 0.015354279428720474
        }
    },
    {
        "name": "findIdx",
        "kind": "def",
        "family": "Wolfram/Multiway",
        "pos": {
            "x": 0.5088452696800232,
            "y": 0.11968497186899185,
            "z": 0.006335126236081123
        }
    },
    {
        "name": "getIdx",
        "kind": "def",
        "family": "Wolfram/Multiway",
        "pos": {
            "x": 0.5021893978118896,
            "y": 0.1322343796491623,
            "z": 0.002501602517440915
        }
    },
    {
        "name": "dedupArray",
        "kind": "def",
        "family": "Wolfram/Multiway",
        "pos": {
            "x": 0.8090564608573914,
            "y": 0.05083107203245163,
            "z": 0.1602291762828827
        }
    },
    {
        "name": "pairEdges",
        "kind": "def",
        "family": "Wolfram/Multiway",
        "pos": {
            "x": 0.5168326497077942,
            "y": 0.11985723674297333,
            "z": 0.0
        }
    },
    {
        "name": "buildMultiway",
        "kind": "def",
        "family": "Wolfram/Multiway",
        "pos": {
            "x": 0.3476119041442871,
            "y": 0.29216328263282776,
            "z": 0.16026832163333893
        }
    },
    {
        "name": "runCE1",
        "kind": "def",
        "family": "Wolfram/Multiway",
        "pos": {
            "x": 0.3514375388622284,
            "y": 0.28065401315689087,
            "z": 0.15424591302871704
        }
    },
    {
        "name": "runCE2",
        "kind": "def",
        "family": "Wolfram/Multiway",
        "pos": {
            "x": 0.3486117720603943,
            "y": 0.28822606801986694,
            "z": 0.16515317559242249
        }
    },
    {
        "name": "main",
        "kind": "def",
        "family": "Wolfram/Multiway",
        "pos": {
            "x": 0.16704721748828888,
            "y": 0.6410498023033142,
            "z": 0.3818915784358978
        }
    },
    {
        "name": "HeytingLean.CLI.WolframRoundtrip.Args",
        "kind": "structure",
        "family": "Wolfram",
        "pos": {
            "x": 0.20216558873653412,
            "y": 0.5717951655387878,
            "z": 0.34399232268333435
        }
    },
    {
        "name": "HeytingLean.CLI.WolframRoundtrip.parseArg",
        "kind": "def",
        "family": "Wolfram",
        "pos": {
            "x": 0.2058883011341095,
            "y": 0.57731693983078,
            "z": 0.3953588306903839
        }
    },
    {
        "name": "HeytingLean.CLI.WolframRoundtrip.parseArgs",
        "kind": "def",
        "family": "Wolfram",
        "pos": {
            "x": 0.6649505496025085,
            "y": 0.062140945345163345,
            "z": 0.09694059938192368
        }
    },
    {
        "name": "HeytingLean.CLI.WolframRoundtrip.usage",
        "kind": "def",
        "family": "Wolfram",
        "pos": {
            "x": 0.16196785867214203,
            "y": 0.6678588390350342,
            "z": 0.43683934211730957
        }
    },
    {
        "name": "HeytingLean.CLI.WolframRoundtrip.expandTilde",
        "kind": "def",
        "family": "Wolfram",
        "pos": {
            "x": 0.3850559592247009,
            "y": 0.18798811733722687,
            "z": 0.21275576949119568
        }
    },
    {
        "name": "HeytingLean.CLI.WolframRoundtrip.findRepoRoot",
        "kind": "def",
        "family": "Wolfram",
        "pos": {
            "x": 0.759453296661377,
            "y": 0.050615549087524414,
            "z": 0.12874197959899902
        }
    },
    {
        "name": "HeytingLean.CLI.WolframRoundtrip.u64BytesLE",
        "kind": "def",
        "family": "Wolfram",
        "pos": {
            "x": 0.3135143220424652,
            "y": 0.3558453321456909,
            "z": 0.24910488724708557
        }
    },
    {
        "name": "HeytingLean.CLI.WolframRoundtrip.encodeU64LEList",
        "kind": "def",
        "family": "Wolfram",
        "pos": {
            "x": 0.2905370593070984,
            "y": 0.4088621735572815,
            "z": 0.32846641540527344
        }
    },
    {
        "name": "HeytingLean.CLI.WolframRoundtrip.decodeU64AtLE",
        "kind": "def",
        "family": "Wolfram",
        "pos": {
            "x": 0.45068272948265076,
            "y": 0.11110997945070267,
            "z": 0.11949916929006577
        }
    },
    {
        "name": "HeytingLean.CLI.WolframRoundtrip.decodeU64LEList",
        "kind": "def",
        "family": "Wolfram",
        "pos": {
            "x": 0.472210556268692,
            "y": 0.07966960221529007,
            "z": 0.14655564725399017
        }
    },
    {
        "name": "HeytingLean.CLI.WolframRoundtrip.splitByLengths",
        "kind": "def",
        "family": "Wolfram",
        "pos": {
            "x": 0.6534019708633423,
            "y": 0.06499063968658447,
            "z": 0.11007342487573624
        }
    },
    {
        "name": "HeytingLean.CLI.WolframRoundtrip.flattenEdges",
        "kind": "def",
        "family": "Wolfram",
        "pos": {
            "x": 0.21149316430091858,
            "y": 0.5797814726829529,
            "z": 0.4380318224430084
        }
    },
    {
        "name": "HeytingLean.CLI.WolframRoundtrip.edgeLengths",
        "kind": "def",
        "family": "Wolfram",
        "pos": {
            "x": 0.33244824409484863,
            "y": 0.31065860390663147,
            "z": 0.25348833203315735
        }
    },
    {
        "name": "HeytingLean.CLI.WolframRoundtrip.metricSumVertices",
        "kind": "def",
        "family": "Wolfram",
        "pos": {
            "x": 0.8401760458946228,
            "y": 0.05679327994585037,
            "z": 0.23691128194332123
        }
    },
    {
        "name": "HeytingLean.CLI.WolframRoundtrip.readHypergraph",
        "kind": "def",
        "family": "Wolfram",
        "pos": {
            "x": 0.9714384078979492,
            "y": 0.01615397445857525,
            "z": 0.5996092557907104
        }
    },
    {
        "name": "HeytingLean.CLI.WolframRoundtrip.writeHypergraph",
        "kind": "def",
        "family": "Wolfram",
        "pos": {
            "x": 0.787645161151886,
            "y": 0.0542406402528286,
            "z": 0.16069817543029785
        }
    },
    {
        "name": "HeytingLean.CLI.WolframRoundtrip.readVerifiedMetric",
        "kind": "def",
        "family": "Wolfram",
        "pos": {
            "x": 0.3363504409790039,
            "y": 0.3135015666484833,
            "z": 0.33638426661491394
        }
    },
    {
        "name": "HeytingLean.CLI.WolframRoundtrip.runWolframscript",
        "kind": "def",
        "family": "Wolfram",
        "pos": {
            "x": 0.746468186378479,
            "y": 0.05273953452706337,
            "z": 0.14139236509799957
        }
    },
    {
        "name": "HeytingLean.CLI.WolframRoundtrip.requireOk",
        "kind": "def",
        "family": "Wolfram",
        "pos": {
            "x": 0.27664363384246826,
            "y": 0.4312012493610382,
            "z": 0.29657942056655884
        }
    },
    {
        "name": "HeytingLean.CLI.WolframRoundtrip.echoDemo",
        "kind": "def",
        "family": "Wolfram",
        "pos": {
            "x": 0.9552246928215027,
            "y": 0.02055656909942627,
            "z": 0.49865013360977173
        }
    },
    {
        "name": "HeytingLean.CLI.WolframRoundtrip.notebookDemo",
        "kind": "def",
        "family": "Wolfram",
        "pos": {
            "x": 0.5193024277687073,
            "y": 0.07184171676635742,
            "z": 0.07487408071756363
        }
    },
    {
        "name": "HeytingLean.CLI.WolframRoundtrip.main",
        "kind": "def",
        "family": "Wolfram",
        "pos": {
            "x": 0.09841672331094742,
            "y": 0.8025044202804565,
            "z": 0.568227231502533
        }
    },
    {
        "name": "main",
        "kind": "def",
        "family": "Wolfram",
        "pos": {
            "x": 0.0,
            "y": 0.9873144030570984,
            "z": 0.9899474382400513
        }
    },
    {
        "name": "HeytingLean.CLI.WolframWM148.Args",
        "kind": "structure",
        "family": "Wolfram/WM148",
        "pos": {
            "x": 0.08696101605892181,
            "y": 0.8272984027862549,
            "z": 0.5864518880844116
        }
    },
    {
        "name": "HeytingLean.CLI.WolframWM148.parseArg",
        "kind": "def",
        "family": "Wolfram/WM148",
        "pos": {
            "x": 0.17726978659629822,
            "y": 0.6284400224685669,
            "z": 0.40304768085479736
        }
    },
    {
        "name": "HeytingLean.CLI.WolframWM148.parseArgs",
        "kind": "def",
        "family": "Wolfram/WM148",
        "pos": {
            "x": 0.09923301637172699,
            "y": 0.8020777702331543,
            "z": 0.571058452129364
        }
    },
    {
        "name": "HeytingLean.CLI.WolframWM148.exprToJsonNat",
        "kind": "def",
        "family": "Wolfram/WM148",
        "pos": {
            "x": 0.30788424611091614,
            "y": 0.3643213212490082,
            "z": 0.24184904992580414
        }
    },
    {
        "name": "HeytingLean.CLI.WolframWM148.sigmaFin2ToJsonNat",
        "kind": "def",
        "family": "Wolfram/WM148",
        "pos": {
            "x": 0.5071501731872559,
            "y": 0.07139425724744797,
            "z": 0.09965880215167999
        }
    },
    {
        "name": "HeytingLean.CLI.WolframWM148.mkBasisLen1Len2Nat",
        "kind": "def",
        "family": "Wolfram/WM148",
        "pos": {
            "x": 0.47513851523399353,
            "y": 0.08555162698030472,
            "z": 0.11899051815271378
        }
    },
    {
        "name": "HeytingLean.CLI.WolframWM148.stateToCountsJsonNat",
        "kind": "def",
        "family": "Wolfram/WM148",
        "pos": {
            "x": 0.7510219216346741,
            "y": 0.052664242684841156,
            "z": 0.14398397505283356
        }
    },
    {
        "name": "HeytingLean.CLI.WolframWM148.findIdxFuel",
        "kind": "def",
        "family": "Wolfram/WM148",
        "pos": {
            "x": 0.4737304151058197,
            "y": 0.10170242935419083,
            "z": 0.07839078456163406
        }
    },
    {
        "name": "HeytingLean.CLI.WolframWM148.findIdx",
        "kind": "def",
        "family": "Wolfram/WM148",
        "pos": {
            "x": 0.520221471786499,
            "y": 0.10097067803144455,
            "z": 0.016632026061415672
        }
    },
    {
        "name": "HeytingLean.CLI.WolframWM148.getIdx",
        "kind": "def",
        "family": "Wolfram/WM148",
        "pos": {
            "x": 0.5073018074035645,
            "y": 0.09432986378669739,
            "z": 0.028325894847512245
        }
    },
    {
        "name": "HeytingLean.CLI.WolframWM148.dedupArray",
        "kind": "def",
        "family": "Wolfram/WM148",
        "pos": {
            "x": 0.8251307010650635,
            "y": 0.05006997287273407,
            "z": 0.18785099685192108
        }
    },
    {
        "name": "HeytingLean.CLI.WolframWM148.buildWM148Multiway",
        "kind": "def",
        "family": "Wolfram/WM148",
        "pos": {
            "x": 0.419932097196579,
            "y": 0.13603806495666504,
            "z": 0.17877036333084106
        }
    },
    {
        "name": "HeytingLean.CLI.WolframWM148.run",
        "kind": "def",
        "family": "Wolfram/WM148",
        "pos": {
            "x": 0.10303147882223129,
            "y": 0.78755784034729,
            "z": 0.5469880104064941
        }
    },
    {
        "name": "main",
        "kind": "def",
        "family": "Wolfram/WM148",
        "pos": {
            "x": 0.0016781326849013567,
            "y": 0.9806703925132751,
            "z": 0.9879326224327087
        }
    }
],
  edges: [[0, 3], [0, 281], [0, 722], [0, 1037], [0, 1374], [1, 71], [1, 280], [1, 1221], [2, 877], [2, 1388], [2, 1429], [3, 1037], [3, 1374], [4, 5], [4, 143], [4, 714], [4, 771], [5, 143], [5, 714], [5, 771], [5, 1330], [6, 129], [6, 1066], [6, 1067], [7, 91], [7, 167], [7, 598], [7, 883], [7, 1034], [8, 113], [8, 262], [8, 1237], [8, 1407], [8, 1444], [9, 15], [9, 35], [9, 304], [9, 772], [9, 882], [10, 62], [10, 741], [10, 1108], [10, 1213], [11, 109], [11, 240], [11, 601], [11, 606], [11, 1009], [11, 1513], [12, 208], [12, 1084], [12, 1167], [12, 1230], [12, 1416], [13, 92], [13, 601], [13, 1014], [13, 1201], [13, 1341], [14, 897], [14, 1059], [14, 1516], [15, 772], [15, 882], [15, 1036], [16, 17], [16, 24], [16, 1215], [16, 1454], [17, 747], [17, 1065], [17, 1329], [18, 224], [18, 640], [18, 1159], [18, 1358], [19, 651], [19, 758], [19, 1019], [19, 1379], [20, 44], [20, 104], [20, 859], [20, 1296], [21, 350], [21, 514], [21, 840], [22, 266], [22, 275], [22, 283], [22, 957], [22, 1364], [23, 904], [23, 1073], [23, 1372], [24, 609], [24, 936], [24, 1275], [25, 76], [25, 884], [25, 1125], [26, 135], [26, 235], [26, 767], [26, 773], [26, 1064], [27, 74], [27, 849], [27, 948], [28, 60], [28, 229], [28, 751], [28, 1514], [29, 62], [29, 79], [29, 1112], [29, 1213], [30, 37], [30, 55], [30, 85], [30, 1357], [31, 197], [31, 643], [31, 963], [31, 1102], [32, 72], [32, 596], [32, 856], [32, 857], [32, 1115], [32, 1391], [33, 194], [33, 1002], [33, 1328], [33, 1521], [34, 49], [34, 132], [34, 602], [35, 1203], [35, 1233], [36, 105], [36, 122], [36, 688], [36, 932], [37, 55], [37, 85], [37, 149], [37, 821], [38, 150], [38, 151], [38, 798], [38, 1008], [38, 1270], [39, 218], [39, 407], [39, 665], [40, 559], [40, 611], [40, 709], [41, 311], [41, 762], [41, 941], [42, 252], [42, 619], [42, 808], [42, 954], [42, 1340], [43, 331], [43, 359], [43, 585], [44, 133], [44, 910], [44, 1296], [45, 200], [45, 666], [45, 1088], [46, 58], [46, 310], [46, 383], [46, 552], [47, 874], [47, 924], [47, 1097], [48, 253], [48, 393], [48, 693], [49, 132], [49, 983], [49, 1120], [50, 119], [50, 769], [50, 1119], [51, 961], [51, 1339], [51, 1533], [52, 615], [52, 670], [52, 674], [52, 733], [52, 870], [52, 938], [53, 479], [53, 676], [53, 780], [54, 117], [54, 180], [54, 341], [54, 1139], [55, 85], [55, 1116], [55, 1357], [56, 184], [56, 230], [56, 250], [56, 1259], [56, 1286], [57, 70], [57, 165], [57, 769], [58, 310], [58, 452], [58, 1146], [58, 1214], [59, 120], [59, 662], [59, 1031], [60, 751], [60, 1514], [61, 898], [61, 1060], [61, 1068], [61, 1508], [62, 79], [62, 207], [62, 741], [62, 1213], [63, 772], [63, 1036], [63, 1126], [63, 1136], [64, 73], [64, 597], [64, 966], [64, 1028], [65, 81], [65, 194], [65, 1339], [66, 193], [66, 194], [66, 254], [67, 267], [67, 1019], [67, 1336], [68, 110], [68, 111], [68, 118], [68, 124], [68, 166], [69, 753], [69, 1003], [69, 1101], [70, 165], [70, 1010], [70, 1232], [71, 930], [71, 1221], [72, 114], [72, 1115], [73, 1027], [73, 1185], [73, 1196], [74, 849], [74, 855], [74, 948], [74, 1053], [75, 592], [75, 892], [75, 1231], [75, 1262], [75, 1273], [75, 1297], [76, 729], [76, 860], [76, 1125], [76, 1304], [77, 284], [77, 604], [77, 845], [77, 1445], [78, 754], [78, 958], [78, 1016], [78, 1266], [78, 1308], [79, 1213], [80, 806], [80, 1043], [80, 1129], [80, 1212], [81, 793], [81, 794], [82, 95], [82, 209], [82, 1103], [83, 660], [83, 799], [83, 940], [84, 728], [84, 907], [84, 1061], [85, 149], [85, 821], [86, 460], [86, 468], [86, 707], [86, 1312], [87, 296], [87, 940], [87, 1315], [88, 125], [88, 298], [88, 1137], [89, 114], [89, 258], [89, 1511], [90, 166], [90, 1334], [90, 1361], [91, 1034], [91, 1170], [91, 1402], [92, 93], [92, 746], [92, 1512], [93, 607], [93, 1168], [93, 1512], [94, 123], [94, 1133], [94, 1226], [94, 1239], [95, 731], [95, 804], [95, 1266], [95, 1423], [96, 115], [96, 146], [96, 997], [96, 1002], [97, 116], [97, 1144], [97, 1458], [98, 112], [98, 890], [98, 1145], [98, 1199], [98, 1321], [99, 100], [99, 102], [99, 866], [99, 962], [99, 1141], [100, 938], [100, 1132], [100, 1141], [101, 257], [101, 1005], [101, 1275], [102, 866], [102, 998], [102, 1306], [103, 416], [103, 561], [103, 665], [104, 126], [104, 186], [104, 646], [104, 859], [104, 880], [104, 886], [104, 1092], [104, 1296], [105, 122], [105, 299], [105, 876], [106, 247], [106, 918], [106, 1142], [107, 130], [107, 306], [107, 817], [107, 865], [108, 150], [108, 151], [108, 865], [108, 1011], [109, 606], [109, 768], [110, 111], [110, 1054], [110, 1370], [111, 118], [111, 124], [111, 1054], [112, 212], [112, 650], [112, 890], [112, 1145], [113, 262], [113, 1237], [114, 258], [114, 1511], [115, 204], [115, 272], [115, 935], [115, 997], [115, 1368], [116, 734], [116, 791], [116, 792], [116, 1144], [117, 933], [117, 1104], [118, 124], [119, 606], [119, 1119], [120, 151], [120, 291], [120, 662], [120, 798], [120, 951], [121, 133], [121, 397], [121, 560], [122, 876], [123, 1133], [123, 1222], [123, 1239], [125, 289], [125, 298], [125, 934], [125, 1075], [126, 646], [126, 1092], [127, 787], [127, 977], [127, 1392], [128, 1202], [128, 1323], [128, 1338], [128, 1508], [129, 145], [129, 233], [129, 756], [129, 1067], [130, 215], [130, 306], [131, 274], [131, 661], [131, 826], [131, 939], [132, 602], [132, 1120], [133, 397], [134, 597], [134, 1185], [134, 1210], [134, 1382], [135, 773], [135, 1064], [135, 1407], [136, 256], [136, 1265], [136, 1532], [137, 171], [137, 900], [137, 946], [138, 1057], [138, 1117], [138, 1223], [139, 162], [139, 610], [139, 856], [139, 1115], [140, 207], [140, 854], [140, 878], [140, 1029], [140, 1113], [141, 729], [141, 1125], [141, 1304], [142, 144], [142, 598], [142, 724], [143, 715], [143, 771], [143, 1330], [144, 288], [144, 777], [144, 862], [144, 1017], [144, 1040], [145, 233], [145, 267], [145, 756], [146, 285], [146, 1100], [146, 1406], [147, 663], [147, 850], [147, 998], [147, 1062], [148, 815], [148, 959], [148, 1428], [149, 821], [149, 1116], [149, 1211], [150, 151], [150, 1011], [151, 276], [151, 662], [151, 865], [151, 1011], [152, 379], [152, 562], [152, 579], [152, 684], [152, 823], [153, 698], [153, 1309], [153, 1425], [154, 734], [154, 923], [154, 1020], [155, 762], [155, 1069], [155, 1128], [156, 664], [156, 1001], [156, 1013], [157, 312], [157, 550], [157, 676], [157, 1417], [158, 899], [158, 968], [158, 1377], [159, 599], [159, 677], [159, 1171], [160, 609], [160, 845], [160, 936], [161, 223], [161, 1381], [161, 1531], [162, 610], [162, 846], [162, 1444], [163, 282], [163, 847], [163, 889], [164, 240], [164, 256], [164, 1381], [165, 769], [165, 1198], [165, 1232], [166, 1412], [167, 1038], [167, 1209], [168, 649], [168, 1041], [168, 1303], [169, 770], [169, 787], [169, 878], [170, 752], [170, 982], [170, 1121], [170, 1123], [171, 900], [171, 946], [172, 173], [172, 318], [172, 706], [172, 1099], [173, 313], [173, 339], [173, 340], [173, 706], [174, 315], [174, 384], [174, 629], [174, 1105], [174, 1421], [175, 953], [175, 1087], [175, 1335], [176, 670], [176, 689], [176, 1096], [176, 1132], [176, 1227], [177, 395], [177, 1090], [177, 1309], [178, 476], [178, 558], [178, 965], [179, 278], [179, 926], [179, 1308], [180, 341], [180, 549], [180, 933], [180, 1004], [180, 1104], [180, 1314], [181, 456], [181, 570], [181, 735], [181, 1106], [182, 251], [182, 396], [182, 502], [182, 616], [182, 1050], [183, 191], [183, 702], [183, 1415], [184, 250], [184, 1012], [185, 187], [185, 647], [185, 798], [185, 963], [185, 1102], [186, 221], [186, 646], [187, 245], [187, 647], [188, 190], [188, 744], [188, 943], [188, 1517], [189, 268], [189, 270], [189, 1140], [189, 1452], [190, 1127], [190, 1147], [191, 655], [191, 702], [191, 1018], [191, 1228], [191, 1415], [192, 748], [192, 1058], [192, 1160], [193, 194], [193, 1299], [193, 1509], [193, 1521], [194, 254], [195, 269], [195, 270], [195, 1457], [196, 251], [196, 1106], [196, 1423], [196, 1424], [197, 245], [197, 1452], [198, 382], [198, 420], [198, 427], [198, 653], [199, 202], [199, 922], [199, 1079], [199, 1453], [200, 472], [200, 666], [200, 909], [200, 965], [200, 1088], [201, 242], [201, 259], [201, 908], [202, 239], [202, 922], [203, 1205], [203, 1272], [203, 1510], [203, 1530], [204, 205], [204, 264], [204, 640], [204, 935], [204, 1159], [204, 1368], [205, 272], [205, 935], [205, 959], [206, 601], [206, 720], [206, 1074], [206, 1111], [206, 1219], [207, 878], [207, 1333], [208, 1084], [208, 1160], [208, 1230], [209, 797], [209, 1103], [210, 314], [210, 778], [210, 942], [211, 663], [211, 820], [211, 837], [211, 861], [211, 866], [211, 1411], [212, 243], [212, 650], [212, 1145], [212, 1302], [213, 215], [213, 306], [213, 1127], [214, 809], [214, 810], [214, 811], [214, 926], [214, 1016], [214, 1308], [215, 306], [215, 1086], [216, 648], [216, 696], [216, 818], [217, 868], [217, 876], [217, 1449], [218, 927], [218, 1419], [218, 1451], [219, 349], [219, 376], [219, 522], [220, 232], [220, 249], [220, 608], [221, 646], [221, 1092], [222, 286], [222, 697], [222, 1085], [223, 1381], [223, 1531], [224, 640], [224, 1007], [224, 1159], [224, 1271], [225, 238], [225, 931], [225, 1362], [226, 231], [226, 719], [226, 1216], [226, 1349], [226, 1442], [226, 1519], [227, 1264], [227, 1453], [227, 1523], [228, 1027], [228, 1184], [228, 1195], [228, 1236], [229, 743], [229, 1293], [229, 1327], [229, 1365], [229, 1506], [229, 1514], [230, 1259], [230, 1286], [231, 901], [231, 1294], [232, 249], [232, 261], [232, 608], [232, 960], [232, 1519], [233, 265], [233, 756], [234, 244], [234, 1286], [234, 1298], [234, 1409], [234, 1410], [235, 651], [235, 981], [235, 988], [235, 1064], [236, 263], [236, 830], [236, 852], [237, 1328], [237, 1406], [237, 1533], [238, 258], [238, 262], [239, 1218], [239, 1410], [239, 1518], [240, 256], [240, 602], [240, 1009], [240, 1381], [241, 769], [241, 987], [241, 1414], [242, 259], [242, 1103], [242, 1264], [242, 1292], [243, 650], [243, 1089], [244, 952], [244, 1286], [244, 1409], [244, 1410], [245, 647], [245, 1090], [245, 1309], [245, 1425], [246, 514], [246, 540], [246, 566], [246, 577], [246, 657], [246, 1433], [247, 918], [247, 1063], [247, 1142], [248, 296], [248, 660], [248, 1075], [249, 261], [249, 608], [249, 969], [250, 1012], [251, 1106], [251, 1423], [252, 808], [252, 1340], [253, 363], [253, 364], [253, 390], [253, 459], [254, 901], [254, 969], [254, 1339], [255, 402], [255, 486], [255, 490], [256, 1235], [256, 1381], [257, 1005], [257, 1065], [257, 1267], [257, 1268], [257, 1275], [258, 1511], [259, 1264], [259, 1292], [259, 1523], [260, 745], [260, 1031], [260, 1517], [261, 608], [261, 969], [262, 1237], [262, 1407], [263, 830], [263, 852], [263, 1124], [264, 935], [264, 1159], [264, 1405], [265, 716], [265, 1217], [265, 1222], [266, 269], [266, 283], [266, 643], [266, 1288], [266, 1459], [267, 894], [267, 1019], [267, 1336], [267, 1404], [267, 1515], [268, 269], [268, 270], [268, 996], [268, 1140], [268, 1457], [269, 1457], [269, 1459], [270, 1140], [270, 1457], [271, 600], [271, 1220], [271, 1295], [272, 935], [273, 646], [273, 880], [273, 886], [274, 661], [274, 826], [274, 939], [274, 1093], [275, 745], [275, 1364], [276, 291], [276, 865], [277, 458], [277, 731], [277, 804], [278, 926], [278, 1308], [279, 317], [279, 970], [279, 1200], [280, 1117], [280, 1223], [281, 722], [281, 1057], [282, 723], [282, 847], [282, 877], [283, 643], [283, 957], [284, 604], [284, 1445], [285, 1100], [285, 1328], [285, 1406], [286, 697], [286, 1085], [287, 785], [287, 889], [287, 985], [288, 1017], [288, 1040], [289, 290], [289, 911], [289, 934], [290, 451], [290, 911], [290, 976], [291, 648], [291, 925], [291, 951], [292, 320], [292, 464], [292, 692], [292, 694], [293, 549], [293, 737], [293, 1033], [293, 1422], [293, 1427], [293, 1431], [294, 329], [294, 338], [294, 528], [294, 667], [294, 1018], [295, 320], [295, 387], [295, 1045], [296, 940], [296, 1315], [297, 827], [297, 881], [297, 970], [298, 641], [298, 1137], [298, 1225], [298, 1315], [299, 688], [299, 1199], [300, 359], [300, 360], [300, 637], [301, 775], [301, 776], [301, 999], [301, 1043], [301, 1129], [302, 323], [302, 453], [302, 797], [302, 819], [302, 922], [302, 1000], [302, 1021], [303, 380], [303, 542], [303, 656], [303, 708], [303, 816], [303, 956], [304, 681], [304, 776], [304, 891], [305, 825], [305, 828], [305, 836], [305, 1311], [306, 817], [306, 1127], [307, 311], [307, 671], [307, 919], [307, 941], [308, 337], [308, 373], [308, 471], [308, 521], [308, 785], [308, 985], [309, 312], [309, 867], [309, 967], [310, 347], [310, 385], [310, 552], [311, 671], [311, 919], [311, 941], [311, 1450], [312, 682], [312, 967], [312, 1417], [313, 339], [313, 706], [314, 778], [314, 812], [314, 979], [315, 384], [315, 629], [315, 1421], [316, 339], [316, 340], [316, 706], [316, 993], [317, 345], [317, 349], [317, 377], [317, 1200], [318, 551], [318, 1099], [319, 481], [319, 550], [319, 978], [319, 1070], [319, 1135], [320, 541], [321, 553], [321, 687], [321, 705], [322, 323], [322, 453], [322, 637], [323, 1424], [324, 477], [324, 500], [324, 527], [324, 532], [325, 679], [325, 1039], [325, 1047], [326, 529], [326, 569], [326, 1107], [326, 1131], [327, 383], [327, 385], [327, 389], [327, 499], [328, 671], [328, 833], [328, 919], [329, 375], [329, 667], [330, 441], [330, 635], [330, 636], [330, 842], [331, 399], [331, 585], [332, 389], [332, 499], [332, 563], [332, 704], [333, 395], [333, 492], [333, 539], [333, 635], [334, 395], [334, 707], [334, 1426], [335, 350], [335, 386], [335, 414], [335, 611], [335, 840], [336, 470], [336, 501], [336, 580], [337, 353], [337, 373], [337, 507], [338, 528], [338, 560], [338, 912], [339, 340], [339, 706], [339, 993], [340, 706], [340, 993], [341, 795], [341, 796], [341, 1139], [341, 1314], [342, 352], [342, 355], [342, 621], [342, 625], [343, 366], [343, 400], [343, 536], [344, 476], [344, 504], [344, 567], [345, 349], [345, 523], [345, 578], [345, 583], [346, 473], [346, 531], [346, 551], [346, 832], [347, 376], [347, 385], [347, 474], [348, 518], [348, 546], [348, 573], [348, 632], [349, 376], [349, 474], [349, 669], [349, 678], [350, 689], [351, 366], [351, 536], [351, 586], [351, 589], [351, 694], [352, 401], [352, 444], [353, 373], [353, 507], [354, 378], [354, 504], [354, 672], [355, 538], [355, 621], [355, 625], [356, 375], [356, 557], [356, 613], [356, 695], [356, 703], [356, 914], [356, 915], [357, 469], [357, 554], [357, 1022], [358, 370], [358, 461], [358, 548], [358, 710], [359, 360], [359, 585], [359, 800], [359, 801], [360, 585], [360, 617], [361, 372], [361, 437], [361, 439], [361, 447], [361, 449], [362, 525], [362, 556], [362, 582], [363, 364], [363, 390], [364, 390], [365, 366], [365, 500], [365, 622], [366, 536], [367, 418], [367, 428], [367, 484], [367, 544], [368, 508], [368, 547], [368, 1049], [369, 505], [369, 512], [369, 788], [369, 916], [370, 461], [370, 710], [370, 995], [371, 427], [371, 586], [371, 620], [371, 653], [371, 711], [372, 400], [372, 439], [372, 445], [373, 471], [373, 507], [373, 521], [374, 407], [374, 416], [374, 561], [374, 665], [375, 613], [375, 667], [375, 914], [376, 474], [376, 522], [376, 678], [377, 475], [377, 523], [377, 553], [377, 761], [377, 838], [377, 841], [378, 476], [378, 504], [378, 672], [379, 491], [379, 537], [379, 572], [380, 485], [380, 515], [380, 816], [381, 475], [381, 553], [381, 1046], [382, 520], [382, 653], [382, 921], [383, 552], [383, 1420], [384, 1421], [386, 414], [386, 689], [386, 840], [387, 690], [387, 1426], [387, 1430], [388, 673], [388, 763], [388, 942], [389, 499], [389, 568], [390, 443], [391, 399], [391, 412], [391, 413], [391, 443], [392, 429], [392, 532], [392, 545], [392, 631], [393, 619], [393, 693], [394, 455], [394, 466], [394, 576], [394, 623], [394, 624], [395, 539], [395, 698], [396, 502], [396, 616], [396, 1051], [396, 1134], [397, 560], [397, 668], [397, 912], [398, 403], [398, 404], [398, 519], [398, 581], [398, 614], [399, 412], [399, 413], [399, 626], [400, 445], [401, 434], [401, 444], [402, 486], [402, 490], [403, 404], [403, 519], [403, 581], [404, 519], [404, 533], [404, 574], [404, 581], [404, 614], [405, 406], [405, 478], [405, 482], [405, 501], [406, 478], [406, 482], [406, 501], [407, 460], [407, 468], [408, 436], [408, 489], [408, 497], [408, 591], [409, 431], [409, 432], [409, 435], [409, 633], [410, 411], [410, 412], [410, 430], [411, 412], [411, 413], [411, 430], [412, 413], [414, 611], [414, 689], [415, 543], [415, 691], [415, 700], [416, 561], [416, 665], [416, 732], [417, 627], [417, 657], [417, 1433], [418, 419], [418, 428], [419, 421], [419, 502], [419, 736], [420, 620], [420, 653], [420, 711], [420, 736], [421, 428], [421, 456], [421, 570], [422, 465], [422, 543], [422, 700], [423, 425], [423, 462], [423, 638], [423, 954], [424, 465], [424, 700], [424, 735], [425, 462], [425, 463], [425, 638], [425, 954], [426, 457], [426, 576], [426, 955], [426, 1157], [427, 586], [428, 544], [428, 570], [429, 477], [429, 527], [429, 545], [429, 631], [430, 587], [431, 432], [431, 633], [431, 712], [432, 435], [432, 633], [433, 434], [433, 446], [433, 516], [433, 634], [434, 440], [434, 634], [435, 710], [436, 497], [436, 591], [436, 913], [437, 447], [437, 488], [438, 440], [438, 446], [438, 487], [439, 445], [439, 449], [440, 446], [440, 448], [440, 493], [441, 442], [441, 492], [441, 506], [442, 492], [442, 506], [442, 612], [443, 626], [444, 450], [445, 449], [446, 487], [447, 488], [448, 450], [448, 493], [448, 494], [448, 535], [449, 488], [450, 493], [450, 494], [451, 976], [451, 1042], [452, 1146], [452, 1214], [453, 1000], [453, 1021], [454, 459], [454, 571], [454, 585], [454, 617], [454, 618], [454, 843], [455, 466], [455, 624], [456, 570], [456, 1106], [457, 517], [457, 576], [457, 623], [457, 955], [458, 652], [458, 731], [458, 804], [458, 1300], [459, 618], [459, 843], [460, 468], [460, 690], [460, 707], [461, 548], [461, 655], [462, 463], [462, 638], [463, 619], [463, 639], [463, 693], [464, 692], [464, 694], [465, 590], [465, 700], [466, 624], [467, 495], [467, 530], [467, 675], [467, 1316], [468, 707], [468, 1430], [469, 554], [469, 1022], [470, 580], [470, 672], [470, 913], [471, 521], [472, 558], [472, 730], [472, 965], [473, 531], [473, 551], [473, 832], [474, 669], [475, 841], [475, 1046], [476, 672], [477, 527], [477, 538], [477, 631], [478, 482], [478, 489], [479, 780], [479, 873], [480, 509], [480, 563], [480, 683], [480, 704], [480, 1049], [481, 568], [481, 1135], [482, 498], [483, 575], [483, 712], [483, 913], [484, 544], [484, 691], [485, 538], [485, 625], [486, 490], [487, 535], [489, 633], [490, 587], [490, 691], [491, 505], [491, 537], [491, 572], [491, 916], [492, 506], [492, 539], [493, 535], [494, 535], [495, 530], [495, 629], [495, 675], [495, 1316], [496, 534], [496, 632], [496, 656], [497, 591], [498, 503], [498, 588], [498, 614], [500, 532], [500, 622], [502, 616], [503, 572], [503, 588], [504, 526], [504, 567], [504, 1022], [505, 547], [505, 788], [505, 916], [506, 539], [508, 509], [508, 555], [508, 564], [508, 565], [509, 1049], [510, 530], [510, 562], [510, 684], [511, 568], [511, 1135], [511, 1420], [512, 564], [512, 916], [513, 584], [513, 738], [513, 920], [514, 627], [514, 657], [514, 1433], [515, 534], [515, 816], [516, 577], [516, 634], [517, 576], [517, 623], [517, 624], [518, 534], [518, 625], [519, 574], [519, 588], [519, 614], [520, 612], [520, 921], [522, 678], [523, 578], [523, 583], [523, 841], [524, 525], [524, 556], [524, 1044], [524, 1047], [525, 556], [525, 582], [525, 1047], [526, 567], [526, 1022], [527, 631], [528, 560], [529, 569], [529, 630], [529, 1107], [529, 1131], [530, 1138], [531, 551], [531, 684], [532, 622], [532, 631], [533, 574], [533, 581], [536, 586], [537, 572], [538, 625], [540, 566], [540, 657], [541, 542], [541, 699], [541, 708], [542, 699], [542, 708], [542, 956], [543, 587], [543, 590], [543, 700], [544, 691], [545, 631], [546, 573], [546, 632], [547, 1049], [548, 569], [548, 655], [549, 1033], [549, 1427], [550, 676], [551, 1099], [553, 705], [553, 761], [553, 838], [554, 701], [554, 994], [555, 564], [555, 565], [556, 582], [556, 1047], [557, 695], [557, 703], [558, 668], [558, 730], [558, 965], [559, 709], [559, 1310], [560, 668], [560, 912], [561, 665], [561, 699], [562, 684], [563, 683], [563, 704], [564, 565], [566, 657], [567, 1022], [568, 1135], [568, 1420], [569, 659], [570, 735], [571, 585], [571, 626], [571, 843], [572, 588], [573, 632], [575, 712], [575, 995], [576, 623], [576, 955], [577, 1433], [578, 583], [579, 823], [579, 832], [580, 913], [580, 915], [584, 738], [584, 920], [586, 589], [588, 614], [589, 694], [590, 691], [592, 1231], [592, 1297], [593, 739], [593, 844], [593, 1440], [594, 595], [594, 945], [594, 1219], [595, 720], [595, 765], [595, 1219], [596, 856], [596, 857], [597, 1185], [597, 1196], [598, 724], [598, 883], [598, 1209], [598, 1223], [599, 677], [599, 723], [599, 1171], [600, 1220], [600, 1295], [600, 1357], [601, 606], [601, 1014], [601, 1201], [601, 1513], [602, 851], [603, 604], [603, 850], [603, 1032], [603, 1078], [604, 1032], [604, 1445], [605, 1510], [605, 1516], [605, 1530], [606, 768], [606, 1014], [606, 1119], [606, 1341], [607, 1052], [607, 1168], [608, 960], [608, 1519], [609, 936], [609, 1275], [610, 846], [610, 1444], [611, 697], [611, 709], [612, 842], [612, 921], [613, 914], [615, 685], [615, 733], [616, 1050], [616, 1051], [617, 618], [619, 639], [619, 693], [620, 711], [621, 625], [623, 624], [626, 843], [627, 630], [628, 690], [628, 692], [628, 1045], [629, 1105], [630, 710], [635, 636], [635, 698], [636, 842], [637, 1048], [639, 693], [641, 812], [641, 1137], [641, 1225], [642, 1110], [642, 1232], [642, 1269], [642, 1378], [642, 1538], [643, 957], [643, 1102], [644, 781], [644, 782], [644, 1136], [644, 1143], [645, 830], [645, 1145], [645, 1321], [646, 880], [646, 886], [646, 1092], [647, 1309], [647, 1312], [648, 696], [648, 887], [648, 925], [649, 774], [649, 831], [649, 1041], [649, 1098], [650, 651], [650, 981], [650, 1089], [651, 767], [651, 981], [651, 1379], [652, 1134], [652, 1300], [653, 921], [654, 1033], [654, 1431], [654, 1432], [655, 1228], [656, 816], [656, 1431], [657, 1433], [658, 888], [658, 986], [658, 1198], [659, 1227], [659, 1415], [660, 1075], [661, 826], [661, 939], [661, 1093], [662, 1031], [663, 861], [663, 1411], [664, 952], [664, 1001], [664, 1013], [666, 909], [666, 1088], [667, 1228], [669, 678], [670, 1227], [671, 763], [671, 833], [671, 919], [673, 942], [673, 984], [673, 1095], [674, 685], [674, 870], [675, 994], [675, 1138], [675, 1316], [677, 723], [679, 1039], [679, 1040], [680, 681], [680, 686], [680, 687], [681, 686], [681, 687], [681, 786], [681, 1044], [682, 905], [682, 906], [682, 1148], [683, 704], [684, 823], [685, 733], [685, 870], [685, 924], [685, 1097], [686, 687], [687, 705], [687, 891], [688, 932], [688, 1214], [689, 779], [690, 1430], [692, 1045], [695, 703], [696, 818], [697, 709], [698, 972], [698, 1312], [701, 994], [701, 1138], [702, 1018], [702, 1415], [703, 915], [708, 956], [709, 1310], [711, 736], [712, 995], [713, 714], [713, 1394], [713, 1397], [714, 1330], [715, 877], [715, 1429], [716, 1217], [716, 1320], [717, 945], [717, 1263], [717, 1538], [718, 1008], [718, 1270], [718, 1364], [719, 753], [719, 1442], [720, 765], [720, 1074], [720, 1111], [720, 1219], [721, 764], [721, 854], [721, 894], [721, 1055], [722, 1374], [723, 1171], [724, 862], [724, 1209], [724, 1223], [725, 904], [725, 1091], [725, 1520], [726, 824], [726, 831], [726, 858], [726, 1030], [727, 813], [727, 848], [727, 853], [727, 1212], [728, 975], [728, 1061], [728, 1142], [729, 1112], [729, 1125], [729, 1304], [730, 965], [731, 804], [731, 908], [732, 927], [732, 1427], [733, 1097], [734, 791], [734, 792], [734, 923], [734, 1020], [737, 956], [737, 1422], [737, 1431], [738, 920], [739, 844], [739, 1024], [739, 1208], [739, 1440], [740, 746], [740, 1163], [740, 1443], [741, 1164], [741, 1175], [741, 1257], [742, 1337], [742, 1376], [742, 1537], [743, 1358], [743, 1479], [743, 1506], [744, 943], [744, 1101], [744, 1337], [745, 1031], [746, 1163], [746, 1443], [747, 750], [747, 1329], [748, 897], [748, 1058], [748, 1160], [749, 1252], [749, 1356], [749, 1399], [750, 1005], [750, 1295], [750, 1399], [750, 1524], [751, 937], [752, 944], [752, 1063], [752, 1121], [752, 1123], [753, 1101], [753, 1216], [753, 1458], [754, 958], [754, 1307], [754, 1452], [755, 990], [755, 1094], [755, 1124], [756, 1226], [756, 1239], [757, 853], [757, 884], [757, 902], [758, 1019], [758, 1379], [759, 992], [759, 1095], [759, 1450], [760, 775], [760, 806], [760, 848], [760, 947], [760, 1129], [761, 838], [762, 1080], [763, 833], [763, 1105], [764, 878], [764, 1055], [765, 766], [766, 1074], [766, 1111], [767, 1064], [768, 834], [768, 973], [768, 989], [769, 987], [770, 787], [770, 1113], [772, 1036], [773, 988], [773, 1064], [774, 831], [774, 875], [774, 1098], [775, 806], [776, 999], [777, 949], [777, 1017], [778, 839], [778, 979], [779, 840], [779, 1096], [780, 873], [781, 782], [781, 949], [781, 974], [781, 1143], [782, 949], [782, 974], [782, 1143], [783, 786], [783, 882], [783, 1126], [783, 1136], [784, 805], [784, 828], [784, 835], [785, 985], [786, 882], [788, 916], [789, 790], [789, 869], [789, 992], [789, 1122], [790, 869], [790, 992], [790, 1095], [790, 1122], [790, 1413], [791, 792], [791, 1313], [791, 1317], [792, 1313], [792, 1317], [793, 794], [793, 822], [793, 1085], [794, 822], [794, 1085], [795, 796], [795, 1432], [796, 1432], [797, 922], [797, 1000], [798, 972], [799, 869], [799, 1122], [799, 1418], [800, 801], [800, 1048], [801, 1048], [802, 803], [802, 867], [802, 1094], [802, 1449], [803, 867], [803, 1094], [803, 1449], [805, 828], [805, 835], [805, 872], [806, 1129], [807, 1069], [807, 1080], [807, 1128], [808, 954], [808, 1012], [809, 810], [809, 811], [810, 811], [810, 1266], [810, 1300], [812, 979], [813, 827], [813, 884], [814, 863], [814, 917], [814, 1089], [814, 1301], [814, 1355], [815, 937], [815, 1141], [817, 1127], [818, 951], [819, 922], [819, 1079], [819, 1424], [820, 866], [820, 1411], [821, 1069], [821, 1211], [822, 961], [822, 1144], [823, 832], [824, 829], [824, 858], [824, 1408], [825, 907], [825, 976], [826, 1100], [827, 829], [827, 858], [827, 881], [828, 1311], [829, 858], [829, 1408], [831, 875], [831, 1030], [831, 1098], [834, 1120], [834, 1235], [835, 864], [836, 1042], [836, 1311], [837, 866], [837, 950], [838, 841], [839, 942], [839, 979], [841, 1046], [844, 1024], [844, 1028], [844, 1208], [844, 1440], [845, 936], [845, 1015], [846, 1444], [847, 889], [848, 853], [848, 947], [848, 1056], [848, 1212], [849, 948], [849, 1053], [850, 1078], [851, 1080], [851, 1116], [852, 1444], [853, 902], [853, 947], [853, 1212], [854, 971], [854, 1029], [854, 1055], [854, 1076], [854, 1113], [855, 975], [855, 1053], [855, 1334], [856, 857], [857, 1115], [857, 1391], [858, 1408], [859, 880], [860, 1030], [860, 1304], [861, 950], [862, 1017], [863, 1301], [863, 1302], [864, 871], [864, 872], [864, 991], [865, 925], [866, 962], [867, 967], [867, 1094], [868, 876], [868, 1199], [869, 1095], [869, 1418], [871, 872], [871, 879], [871, 885], [872, 879], [872, 885], [873, 905], [873, 906], [873, 953], [873, 1335], [873, 1417], [874, 924], [874, 1097], [875, 1098], [876, 1070], [877, 1429], [878, 1077], [879, 885], [879, 990], [880, 886], [881, 970], [883, 1034], [883, 1038], [883, 1209], [884, 902], [887, 927], [887, 1086], [888, 980], [888, 986], [890, 1145], [891, 999], [892, 1023], [892, 1262], [892, 1448], [893, 929], [893, 1071], [893, 1371], [894, 1006], [894, 1515], [895, 1248], [895, 1249], [895, 1260], [895, 1284], [895, 1349], [896, 900], [896, 1483], [896, 1526], [896, 1540], [897, 1073], [897, 1109], [898, 1060], [898, 1370], [899, 968], [899, 1377], [899, 1395], [900, 946], [900, 1526], [901, 1294], [901, 1400], [901, 1509], [903, 1234], [903, 1236], [903, 1262], [903, 1439], [904, 1372], [904, 1520], [905, 906], [905, 1148], [907, 976], [908, 964], [909, 965], [910, 1069], [910, 1128], [911, 934], [917, 1081], [917, 1355], [918, 1063], [919, 1450], [922, 1079], [923, 1020], [924, 1097], [926, 1308], [927, 1086], [928, 931], [928, 1320], [928, 1460], [929, 1006], [929, 1071], [929, 1371], [929, 1505], [930, 1037], [930, 1221], [930, 1255], [930, 1256], [931, 1460], [932, 1214], [933, 1004], [933, 1104], [935, 959], [935, 997], [935, 1368], [937, 959], [937, 1428], [938, 1141], [939, 1093], [943, 1517], [944, 1063], [944, 1109], [945, 1269], [945, 1378], [945, 1538], [949, 974], [950, 962], [952, 1001], [953, 1335], [954, 1340], [955, 1157], [956, 1431], [958, 1308], [959, 1368], [959, 1428], [960, 1458], [960, 1519], [961, 1339], [962, 1141], [963, 1102], [964, 996], [964, 1140], [966, 1056], [966, 1382], [968, 1377], [968, 1395], [968, 1534], [969, 1339], [970, 1200], [971, 1029], [971, 1076], [971, 1333], [972, 1312], [973, 989], [973, 1120], [975, 1061], [975, 1361], [977, 1081], [977, 1303], [977, 1392], [978, 1070], [978, 1135], [980, 986], [980, 1412], [981, 988], [982, 1121], [982, 1123], [983, 1080], [983, 1120], [984, 1095], [984, 1418], [987, 1413], [987, 1414], [989, 1120], [990, 1124], [991, 1087], [991, 1148], [992, 1095], [996, 1140], [996, 1307], [997, 1002], [998, 1062], [998, 1306], [998, 1366], [999, 1043], [1000, 1021], [1001, 1013], [1003, 1101], [1003, 1147], [1004, 1314], [1005, 1275], [1006, 1505], [1007, 1159], [1007, 1271], [1008, 1011], [1008, 1270], [1009, 1381], [1010, 1054], [1010, 1378], [1014, 1235], [1014, 1341], [1015, 1267], [1015, 1268], [1016, 1308], [1017, 1040], [1019, 1336], [1023, 1331], [1023, 1448], [1024, 1108], [1024, 1208], [1025, 1114], [1025, 1185], [1025, 1196], [1026, 1035], [1026, 1203], [1026, 1233], [1027, 1196], [1028, 1208], [1029, 1055], [1029, 1076], [1029, 1113], [1032, 1078], [1033, 1422], [1034, 1038], [1034, 1082], [1035, 1234], [1035, 1262], [1035, 1439], [1039, 1047], [1041, 1303], [1042, 1225], [1044, 1047], [1050, 1051], [1050, 1134], [1052, 1072], [1052, 1261], [1053, 1305], [1054, 1305], [1056, 1382], [1057, 1117], [1057, 1207], [1058, 1059], [1059, 1373], [1059, 1396], [1059, 1516], [1060, 1370], [1062, 1366], [1065, 1267], [1066, 1067], [1066, 1336], [1068, 1389], [1068, 1508], [1069, 1128], [1069, 1211], [1071, 1371], [1071, 1505], [1072, 1158], [1072, 1224], [1072, 1261], [1072, 1393], [1073, 1372], [1073, 1391], [1073, 1516], [1074, 1111], [1077, 1112], [1077, 1304], [1079, 1103], [1079, 1453], [1080, 1116], [1081, 1118], [1081, 1355], [1082, 1170], [1082, 1394], [1082, 1397], [1082, 1437], [1083, 1244], [1083, 1360], [1083, 1403], [1084, 1230], [1086, 1419], [1086, 1451], [1087, 1148], [1087, 1335], [1089, 1118], [1089, 1379], [1090, 1309], [1090, 1425], [1091, 1123], [1091, 1520], [1094, 1124], [1094, 1449], [1096, 1132], [1096, 1227], [1107, 1131], [1108, 1440], [1109, 1372], [1110, 1130], [1110, 1538], [1112, 1213], [1114, 1210], [1114, 1382], [1117, 1207], [1118, 1379], [1118, 1392], [1121, 1123], [1122, 1413], [1126, 1136], [1127, 1147], [1130, 1158], [1130, 1538], [1133, 1407], [1137, 1225], [1139, 1310], [1139, 1432], [1140, 1307], [1143, 1207], [1144, 1458], [1146, 1214], [1149, 1150], [1149, 1161], [1149, 1383], [1150, 1161], [1150, 1204], [1150, 1383], [1151, 1323], [1151, 1471], [1151, 1478], [1152, 1249], [1152, 1287], [1152, 1498], [1152, 1537], [1153, 1248], [1153, 1369], [1153, 1475], [1153, 1493], [1154, 1278], [1154, 1446], [1154, 1462], [1155, 1156], [1155, 1253], [1155, 1285], [1156, 1253], [1156, 1254], [1156, 1285], [1157, 1340], [1158, 1261], [1158, 1263], [1158, 1338], [1158, 1390], [1160, 1167], [1161, 1171], [1161, 1204], [1161, 1383], [1162, 1436], [1162, 1464], [1162, 1539], [1163, 1183], [1163, 1194], [1163, 1443], [1164, 1257], [1164, 1290], [1164, 1333], [1165, 1258], [1165, 1291], [1165, 1504], [1165, 1505], [1166, 1252], [1166, 1283], [1166, 1356], [1166, 1536], [1167, 1230], [1167, 1416], [1168, 1443], [1168, 1512], [1169, 1195], [1169, 1525], [1169, 1529], [1170, 1402], [1170, 1437], [1172, 1186], [1172, 1277], [1172, 1461], [1173, 1187], [1173, 1342], [1173, 1343], [1173, 1384], [1173, 1473], [1174, 1179], [1174, 1190], [1174, 1435], [1175, 1257], [1175, 1441], [1176, 1250], [1176, 1251], [1176, 1480], [1176, 1482], [1177, 1456], [1177, 1471], [1177, 1478], [1178, 1331], [1178, 1375], [1178, 1467], [1178, 1527], [1179, 1190], [1179, 1276], [1179, 1282], [1179, 1435], [1179, 1465], [1179, 1466], [1179, 1539], [1180, 1290], [1180, 1380], [1180, 1528], [1181, 1187], [1181, 1192], [1181, 1473], [1182, 1193], [1182, 1241], [1182, 1527], [1183, 1194], [1183, 1318], [1183, 1352], [1183, 1534], [1184, 1195], [1184, 1236], [1185, 1196], [1185, 1382], [1186, 1277], [1186, 1461], [1187, 1192], [1187, 1342], [1187, 1343], [1187, 1344], [1187, 1469], [1187, 1473], [1188, 1224], [1188, 1352], [1188, 1484], [1189, 1244], [1189, 1280], [1189, 1387], [1190, 1276], [1190, 1435], [1191, 1258], [1191, 1291], [1191, 1504], [1192, 1473], [1193, 1241], [1193, 1527], [1194, 1318], [1194, 1352], [1194, 1534], [1195, 1529], [1197, 1229], [1197, 1272], [1197, 1401], [1197, 1522], [1198, 1232], [1199, 1321], [1201, 1532], [1202, 1338], [1202, 1389], [1202, 1390], [1202, 1393], [1202, 1508], [1203, 1233], [1204, 1383], [1204, 1388], [1205, 1324], [1205, 1345], [1205, 1346], [1206, 1319], [1206, 1322], [1206, 1373], [1206, 1396], [1206, 1470], [1210, 1382], [1211, 1296], [1215, 1363], [1215, 1454], [1216, 1442], [1216, 1519], [1217, 1222], [1217, 1320], [1217, 1404], [1217, 1460], [1218, 1298], [1218, 1410], [1218, 1518], [1220, 1332], [1220, 1357], [1222, 1320], [1222, 1362], [1222, 1460], [1224, 1261], [1224, 1338], [1225, 1315], [1226, 1239], [1229, 1272], [1229, 1401], [1231, 1273], [1231, 1297], [1232, 1378], [1234, 1439], [1236, 1439], [1238, 1334], [1238, 1361], [1238, 1416], [1240, 1247], [1240, 1464], [1240, 1472], [1240, 1477], [1241, 1486], [1241, 1527], [1242, 1350], [1242, 1351], [1242, 1384], [1242, 1385], [1243, 1277], [1243, 1279], [1243, 1281], [1243, 1438], [1243, 1461], [1244, 1280], [1244, 1387], [1245, 1246], [1245, 1281], [1245, 1398], [1245, 1434], [1246, 1281], [1246, 1434], [1247, 1464], [1247, 1468], [1248, 1284], [1249, 1284], [1249, 1498], [1250, 1251], [1250, 1482], [1250, 1535], [1251, 1325], [1251, 1363], [1252, 1356], [1252, 1455], [1252, 1536], [1253, 1254], [1253, 1285], [1254, 1287], [1254, 1288], [1255, 1256], [1255, 1289], [1256, 1289], [1257, 1290], [1258, 1291], [1258, 1504], [1259, 1286], [1260, 1349], [1260, 1376], [1260, 1442], [1261, 1338], [1263, 1370], [1264, 1292], [1265, 1513], [1265, 1532], [1267, 1268], [1269, 1538], [1271, 1306], [1272, 1346], [1272, 1401], [1273, 1297], [1274, 1358], [1274, 1365], [1274, 1447], [1274, 1506], [1276, 1435], [1276, 1486], [1277, 1279], [1277, 1438], [1277, 1461], [1278, 1343], [1278, 1446], [1278, 1462], [1279, 1438], [1279, 1461], [1280, 1387], [1282, 1435], [1282, 1525], [1283, 1356], [1283, 1481], [1283, 1536], [1284, 1498], [1286, 1409], [1287, 1288], [1287, 1364], [1289, 1438], [1290, 1380], [1291, 1463], [1291, 1504], [1293, 1326], [1293, 1327], [1293, 1506], [1294, 1369], [1294, 1400], [1295, 1332], [1295, 1359], [1295, 1524], [1298, 1410], [1299, 1369], [1299, 1509], [1301, 1302], [1305, 1334], [1305, 1412], [1307, 1452], [1309, 1425], [1313, 1317], [1318, 1352], [1318, 1476], [1319, 1322], [1319, 1347], [1319, 1373], [1319, 1396], [1319, 1456], [1320, 1460], [1322, 1396], [1322, 1470], [1323, 1338], [1323, 1389], [1324, 1345], [1324, 1346], [1325, 1363], [1325, 1454], [1325, 1535], [1326, 1327], [1326, 1506], [1327, 1365], [1328, 1406], [1329, 1399], [1331, 1448], [1331, 1527], [1332, 1357], [1332, 1359], [1334, 1361], [1337, 1376], [1337, 1537], [1338, 1390], [1338, 1393], [1342, 1473], [1343, 1469], [1344, 1350], [1344, 1384], [1345, 1346], [1346, 1522], [1347, 1373], [1347, 1456], [1347, 1470], [1348, 1354], [1348, 1510], [1348, 1530], [1349, 1442], [1350, 1384], [1350, 1385], [1351, 1463], [1351, 1504], [1352, 1476], [1353, 1395], [1353, 1481], [1353, 1536], [1354, 1456], [1354, 1510], [1354, 1530], [1356, 1535], [1356, 1536], [1358, 1447], [1358, 1479], [1358, 1506], [1359, 1367], [1359, 1524], [1359, 1531], [1360, 1403], [1360, 1429], [1361, 1416], [1362, 1460], [1363, 1454], [1365, 1506], [1366, 1445], [1367, 1455], [1367, 1524], [1369, 1400], [1369, 1475], [1369, 1509], [1372, 1391], [1373, 1396], [1375, 1467], [1375, 1527], [1376, 1537], [1380, 1528], [1384, 1385], [1386, 1441], [1386, 1464], [1386, 1468], [1386, 1507], [1388, 1403], [1388, 1429], [1389, 1390], [1389, 1508], [1390, 1393], [1394, 1397], [1398, 1402], [1398, 1434], [1398, 1474], [1399, 1535], [1402, 1437], [1403, 1429], [1404, 1515], [1405, 1521], [1405, 1533], [1410, 1518], [1413, 1414], [1419, 1451], [1426, 1430], [1434, 1474], [1436, 1464], [1436, 1539], [1441, 1468], [1441, 1507], [1446, 1462], [1446, 1528], [1447, 1475], [1447, 1479], [1452, 1459], [1453, 1523], [1455, 1524], [1461, 1474], [1463, 1504], [1463, 1522], [1464, 1468], [1465, 1466], [1465, 1539], [1466, 1539], [1467, 1527], [1468, 1507], [1469, 1485], [1470, 1471], [1471, 1478], [1472, 1477], [1472, 1485], [1472, 1503], [1475, 1493], [1476, 1481], [1477, 1485], [1477, 1487], [1477, 1503], [1479, 1480], [1479, 1506], [1480, 1493], [1482, 1490], [1482, 1491], [1483, 1526], [1483, 1540], [1484, 1489], [1484, 1492], [1485, 1487], [1486, 1503], [1487, 1503], [1488, 1489], [1488, 1492], [1488, 1495], [1489, 1492], [1490, 1491], [1490, 1496], [1490, 1497], [1490, 1499], [1491, 1496], [1491, 1499], [1492, 1495], [1494, 1500], [1494, 1501], [1494, 1502], [1495, 1497], [1496, 1497], [1496, 1499], [1500, 1501], [1500, 1502], [1501, 1502], [1509, 1521], [1510, 1530], [1521, 1533], [1525, 1529], [1526, 1540]]
};

// Export for use in viewers
if (typeof module !== 'undefined') {
  module.exports = mirandaProofsData;
}
