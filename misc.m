(* ::Package:: *)

BeginPackage["misc`"]


CurrentMax::usage="CurrentMax[list] produces a list of the maximum of all
 subsequences starting at the beginning."


Context["`Private`"]


CurrentMax=Function[{seq},
If[Length[seq]==0,
seq,
Module[{m},
m=seq[[1]];
Function[{x},
If[x>m,
m=x];
m]/@seq]]]


End[]


EndPackage[]
