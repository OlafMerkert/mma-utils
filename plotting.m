(* ::Package:: *)

(* ::Text:: *)
(*For comparing the growth rates with polynomial growth of order 1 to n, we produce a standard loglog plot in the range from 1 to bound.*)


GrowthRates=Function[{n,bound},
	Module[{colours,functions},
		colours=Table[Hue[i/n],{i,0,n-1}];
		functions=Table[x^i,{i,1,n}];
		LogLogPlot[functions,{x,1,bound},PlotStyle->colours]]];
