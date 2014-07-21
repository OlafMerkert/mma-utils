(* ::Package:: *)

BeginPackage["SeriesContinuedFractionsNamed`"]

CF::square="Cannot produce CF expansion for square polynomial";

Begin["`Private`"]


(* ::Section:: *)
(*Helper functions*)

(* ::Subsection:: *)
(*Basic*)

Second[list_]:=Part[list,2]

(* ::Subsection:: *)
(*Simplification Wrapper*)

(* ::Text:: *)
(*In order to easily try out different simplification mechanisms, we define a wrapper.*)

Smpl[x_]:=Simplify[x]

(* ::Text:: *)
(*TODO We also need a mechanism to remove calculated information.*)

(* ::Subsection:: *)
(*Characteristic*)

(* ::Text:: *)
(*We want to able to at least compute (mod p), however it is not clear how to integrate with the main formulas.*)

$Char=0;
CMod[poly_]:=poly
CMod[n_Integer]:=n
WithChar[p_,body__]:=Block[{$Char=p},body]

(* ::Subsection:: *)
(*Algebraic numbers*)

OmegaPoly[coeff_]:=(\[Omega]^Range[0,Length[coeff]-1]).coeff
OmegaAlg={AlgebraicNumber[_,coeff_]:>OmegaPoly[coeff],Root[__]->\[Omega]};

(* ::Subsection:: *)
(*Polynomials*)

(* ::Text:: *)
(*TODO use one of my packages?*)

degree=Function[polynomial,Exponent[polynomial,X]];
LeadingCoefficient=Function[polynomial,
	Coefficient[polynomial,X,degree[polynomial]]];

(* ::Text:: *)
(*TODO need to automatically detect the variable of the polynomial.*)

FirstZero=Function[polynomial,
	Module[{z=Root[polynomial,t,1]},
		If[SameQ[Head[z],Root],
			ToNumberField[z],z]]];

(* ::Subsection:: *)
(*Rational functions*)

(* ::Text:: *)
(*Given some rational function, we are interested in the irreducible factors (without multiplicity) appearing in the denominator. Note that FactorList usually also includes a leading coefficient in the factorisation.*)

Poles=Function[expr,
	Cases[FactorList[expr,Modulus->$Char],
		{b_,g_}/;And[g<0,Not[NumberQ[b]]]->b]];

(* ::Subsection:: *)
(*List and Table generation*)

(* ::Text:: *)
(*We also have a general function to produce tables, if we have accessors like above:*)

list[accessor_,name_,nmax_]:=
	Table[accessor[name,n],
	{n,0,nmax}]
flatlist[accessor_,name_,nmax_]:=Flatten[list[accessor,name,nmax]]
union[accessor_,name_,nmax_]:=Union[list[accessor,name,nmax]]
column[accessor_,name_,nmax_]:=Column[list[accessor,name,nmax],Frame->All]
grid[accessor_,name_,nmax_]:=Grid[list[accessor,name,nmax],Frame->All]

(* ::Text:: *)
(*The above we call presenters. Often we want to combine a presentor with an accessor (a function which takes two arguments, name and n), so the following definition helps us with that.*)

DefCompoundAccessor[abbrev_,presenter_,accessor_]:=
	(abbrev[name_,nmax_]:=presenter[accessor,name,nmax])

(* ::Section:: *)
(*Continued fractions expansion*)

(* ::Subsection::Closed:: *)
(*Representing complete quotients and CF*)

(* ::Text:: *)
(*If a0 is the truncation of Sqrt[d], we use the representation (a0+t+Sqrt[d])/s for the complete quotients, where deg t<deg s<deg a0.*)
(*We first provide the formulas for generating the sequences, so we know how to advance:*)

ComputePartialQuotient[s_,a0_]:=Smpl[
	PolynomialQuotient[2 a0,s,X,Modulus->$Char]]
ComputeTranslator[t_,s_,a_,a0_]:=Smpl[CMod[a s-t-2a0]]
ComputeDenominator[t_,s_,d2_,a0_]:=Smpl[
	PolynomialQuotient[d2-2 a0 t-t^2,s,X,Modulus->$Char]]

(* ::Text:: *)
(*Then we put everything together. In this package, instead of storing object in a variable, we use names to identify a particular Continued Fraction expansion, and all the data attached to it (this is sort of pseudo-OOP).*)

(* ::Text:: *)
(*TODO check for even degree*)

SqrtContinuedFraction=Function[{name,radicand},
	Module[{n,a0,d2},
		poly[name]=radicand;
		n=Exponent[poly[name],X]/2;
		polyroot[name]=Series[Sqrt[poly[name]],{X,\[Infinity],0}];
		a0=polyrootpoly[name]=CMod[Normal[polyroot[name]]];
		d2=Simplify[CMod[poly[name]-a0^2]];
		If[SameQ[d2,0],Message[CF::square],
			partialquotient[name,n_Integer]:=partialquotient[name,n]=
				ComputePartialQuotient[denominator[name,n],a0];
			denominator[name,0]=1;
			translator[name,0]=0;
			denominator[name,n_Integer/;n>0]:=denominator[name,n]=
				ComputeDenominator[translator[name,n],
					denominator[name,n-1],d2,a0];
			translator[name,n_Integer/;n>0]:=
				translator[name,n]=ComputeTranslator[translator[name,n-1],
					denominator[name,n-1],partialquotient[name,n-1] ,a0];
			name]]];

(* ::Text:: *)
(*If the radicand contains a variable (different from X, which is our main polynomial variable), we can assign a special value to it. The following function does this (given a CF name), and goes on to compute the CF with the special value at once.*)

SpecialiseCF=Function[{name,param,value},
SqrtContinuedFraction[name[value],
poly[name]/.param->value]];

(* ::Subsection::Closed:: *)
(*TODO Clearing a name*)

ClearCF=Function[{name},
poly[name]=.;
polyroot[name]=.;
polyrootpoly[name]=.;
partialquotient[name,_]=.;
denominator[name,_]=.;
translator[name,_]=.;]

(* ::Subsection:: *)
(*Abbreviations and list/table generators*)

(* ::Text:: *)
(*When we computed a specialisation, we sometimes want to know what we end up with*)

cfDesc[name_]:={name,poly[name],polyrootpoly[name]}

(* ::Text:: *)
(*Partial quotient, Translator (t), Denominator (s)*)

ptd[name_,n_]:={partialquotient[name,n],
	translator[name,n],
	denominator[name,n]}

(* ::Text:: *)
(*As the above, but r=a0+t*)

prd[name_,n_]:={partialquotient[name,n],
	polyrootpoly[name]+translator[name,n],
	denominator[name,n]}

(* ::Text:: *)
(*For better inspection, we define Table versions of these:*)

DefCompoundAccessor[ptdTable,column,ptd]
DefCompoundAccessor[prdTable,column,prd]
DefCompoundAccessor[pqList,list,partialquotient]

(* ::Subsection::Closed:: *)
(*Searching for poles in the partial quotients*)

(* ::Text:: *)
(*From the results we find in the theory, we know it suffices to look at the leading coefficient of the partial quotient to get the points of bad reduction.*)

poles[name_,n_]:=Poles[LeadingCoefficient[partialquotient[name,n]]]

DefCompoundAccessor[poleTable,grid,poles]
DefCompoundAccessor[poleList,union,poles]
DefCompoundAccessor[degList,list,Composition[degree,partialquotient]]

(* ::Subsection::Closed:: *)
(*Automatic specialisation*)

(* ::Text:: *)
(*Once we have found the poles, we are of course interested in the specialisation at these points. And naturally, we try to automate this a little bit.*)

(* ::Text:: *)
(*First, we have a helper function to tell us the names of the specialistations -- these are all of the form name[t] where t is the special value.*)

SpecList[name_,nmax_]:=Map[Composition[name,FirstZero],poleList[name,nmax]]

(* ::Text:: *)
(*The most readily available information, that it also makes sense to display in parallel, are the degrees of the partial quotients.*)

specialDegList[name_,nmax_]:=Map[
	degList[SpecialiseCF[name,t,FirstZero[#]],nmax+1]&,
	poleList[name,nmax]]

(* ::Text:: *)
(*TODO this looks slightly misplaced here:*)

DefCompoundAccessor[denList,list,Composition[Factor,denominator]]

(* ::Subsection::Closed:: *)
(*Computing the period length*)

(* ::Text:: *)
(*TODO perhaps memoize period computations*)

findperiodlimit=40;
FindPeriod[name_]:=For[i=1,i<findperiodlimit,i++,
	If[1==denominator[name,i],Return[i]]]
FindQuasiPeriod[name_]:=For[i=1,i<findperiodlimit,i++,
	If[0==degree[denominator[name,i]],Return[i]]]

denListAuto[name_]:=denList[name,FindPeriod[name]]

(* ::Section:: *)
(*Convergents & Pell equation*)

(* ::Subsection:: *)
(*Convergents come from Matrix products*)

approxMatrixFactor[a_]:=({
 {a, 1},
 {1, 0}
})

approxMatrix[name_,0]:=approxMatrixFactor[partialquotient[name,0]/2]
approxMatrix[name_,n_Integer/;n>0]:=approxMatrix[name,n]=
	Dot[approxMatrix[name,n-1],approxMatrixFactor[partialquotient[name,n]]]
approxFraction[name_,n_]:=Simplify[Map[First,approxMatrix[name,n]]]

DefCompoundAccessor[approxNumList,list,Composition[First,approxFraction]]
DefCompoundAccessor[approxDenList,list,Composition[Second,approxFraction]]

(* ::Subsection:: *)
(*Testing solutions of the Pell equation*)

pellTest[name_,{p_,q_}]:=Collect[p^2-poly[name] q^2,X]

(* ::Section:: *)
(*End*)

End[]
EndPackage[]
