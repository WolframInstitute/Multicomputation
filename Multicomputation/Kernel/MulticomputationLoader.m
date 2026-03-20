BeginPackage["Wolfram`MulticomputationInit`"]

PacletDependency

Begin["`Private`"]

PacletDependency[paclet_, version : _String | None : None] := With[{paclets = Through[PacletFind[paclet]["Version"]]},
    If[ ! If[version === None, Length[paclets] > 0, AnyTrue[paclets, ResourceFunction["VersionOrder"][#, version] >= 0 &]],
        PacletDirectoryLoad[PacletInstall[If[version === None, paclet, paclet -> version], "InstallLocation" -> "Cached"]["Location"]]
    ]
]

End[]

Get[FileNameJoin[{DirectoryName[$InputFileName], "WFR.m"}]]

PacletDependency["SetReplace"]
PacletDependency["WolframInstitute/Hypergraph"]

EndPackage[]

PacletManager`Package`loadWolframLanguageCode[
    "Wolfram`Multicomputation",
    "Wolfram`Multicomputation`",
    ParentDirectory[DirectoryName[$InputFileName]],
    "Kernel/Multicomputation.m",
    "AutoUpdate" -> False,
    "AutoloadSymbols" -> {
        "Wolfram`Multicomputation`Multi",
        "Wolfram`Multicomputation`MultiwaySystem"
    },
    "HiddenImports" -> {}
];

(* Dark-mode-compatible style overrides: use LightDarkSwitched for colors that are invisible on dark backgrounds *)
SetOptions[MultiEvaluate,
    "EventColumnOptions" -> {
        Alignment -> Center,
        Background -> {Opacity[0.8, LightDarkSwitched[Hue[0.14, 0.34, 1], RGBColor[0.25098, 0.239216, 0.188235]]], LightDarkSwitched[RGBColor[0.9998, 0.8347, 0.2631], RGBColor[0.564706, 0.447059, 0.129412]]},
        BaseStyle -> Directive[Opacity[1], GrayLevel[0], Bold, FontColor -> Black, FontFamily -> "Source Code Pro"]
    },
    "EventStyleOptions" -> {FontColor -> Directive[Opacity[1], LightDarkSwitched[GrayLevel[0], GrayLevel[1]]], FontFamily -> "Source Code Pro"},
    "StateStyleOptions" -> {FontWeight -> Bold, FontColor -> Directive[Opacity[1], LightDarkSwitched[GrayLevel[0], GrayLevel[1]]], FontFamily -> "Source Code Pro"}
];
