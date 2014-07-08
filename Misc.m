(* ::Package:: *)

BeginPackage["Misc`"]

CumulativeMax::usage="produce a list of the ongoing maximums of a list."
SquareMultiply::usage="Efficient algorithm for raising expressions to powers, 
	given a squaring and a multiplication function."

Begin["`Private`"]

(* ::Text:: *)
(*Compute the maximums of all seen elements as we iterate over a list.*)

CumulativeMax=Function[{seq},
	If[Length[seq]==0,
	seq,
	Module[{m},
		m=seq[[1]];
		Function[{x},
			If[x>m,m=x];
			m]/@seq]]]

(* ::Text:: *)
(*The classic square-multiply algorithm*)

SquareMultiply[expr_,n_Integer/;n>=0,square_,multiply_]:=Module[{digits,result},
	digits=IntegerDigits[n,2];
	result=1;
	Map[Function[{digit},
		result=multiply[expr,square[result]]],
		digits];
	result]

End[]
EndPackage[]
