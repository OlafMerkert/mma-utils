(* ::Package:: *)

(* ::Section:: *)
(*Valuations*)


(* ::Subsection:: *)
(*Archimedean*)


A[a_+b_]:=A[a]+A[b]
A[a_ b_]:=A[a]A[b]
A[a_^n_Integer]:=A[a]^n
A[n_Rational]:=Abs[n]
A[n_Integer]:=Abs[n]
A[0]:=0



(* ::Subsection:: *)
(*Non-archimedean*)


U[a_+b_]:=Max[U[a],U[b]]
U[a_ b_]:=U[a]U[b]
U[a_^n_Integer]:=U[a]^n
U[0]:=0
U[1]:=1
U[-1]:=1
U[a_Rational/;a<0]:=U[-a]
(*U[a_Rational]:=U[Numerator[a]]/U[Denominator[a]]*)


(* ::Section:: *)
(*Heights*)


(* ::Subsection:: *)
(*Projective heights*)


ProjectiveHeightRationals=Function[{list},
	Module[{maindenlist,dens},
		dens=Map[Composition[Abs,Denominator],list];
		maindenlist=Apply[LCM,dens]list;
		Log[Apply[Max,Map[Abs,maindenlist]]]]];


PolynomialHeightRationals=Function[{poly,var},
	ProjectiveHeightRationals[CoefficientList[poly,var]]];


(* ::Subsection:: *)
(*Visualisation*)


(* ::Input:: *)
(*HeightPlot=Function[{list},*)
(*Module[{values,points},*)
(*values=Map[h,list];*)
(*points=Table[{i,Part[values,i]},{i,Length[values]}];*)
(*ListLogLogPlot[points]]];*)
