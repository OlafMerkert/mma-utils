(* ::Package:: *)

BeginPackage["SeriesContinuedFractions`"]

$X::usage="The variable against which all the univariate 
	polynomial and series functions work with."
SqrtPolyPart::usage="The polynomial part of the square root of a polynomial."
SquareQ::usage="Test if a polynomial is a square."
ConstantQ::usage="Test if an expression is constant with respect to $X"
SquareRemainder::usage="The part of a polynomial which obstructs its squareness."
CQ::usage="Notation for complete quotients in a continued fraction expansion
	of some quadratic."
CQNormalise::usage="Eliminate unwanted common factors in a CQ representation."
CQPartialQuotient::usage="Compute the partial quotient from the complete quotient."
CQStep::usage="Advance in the continued fraction process."
CQList::usage="Produce a list of subsequent partial quotients."
CQMap::usage="Map over a list of subsequent partial quotients."

QuasiPeriodLength::usage="Count the number of steps towards a constant 
	denominator s. By default, only search through a limited number 
	of steps."
ApproximationMatrix::usage="Compute the convergent matrix for a complete quotient."
ApproximationFraction::usage="Compute the convergent for a complete quotient."
ApproximationNumerator::usage="Compute the convergent numerator for a complete quotient."
ApproximationDenominator::usage="Compute the convergent denominator for a complete quotient."

CQDegree::usage="Compute the degree of the partial and complete quotient."

Begin["`Private`"]

(* ::Section::Closed:: *)
(*Continued fraction algorithm*)

(* ::Subsection:: *)
(*Elementary definitions*)

$X=Global`X;
SqrtPolyPart[d_]:=SqrtPolyPart[d]=Normal[Series[Sqrt[d],{$X,\[Infinity],0}]]
SquareQ[d_]:=SameQ[d-SqrtPolyPart[d]^2,0]
ConstantQ[xpr_]:=SameQ[0,Exponent[xpr,$X]]
SquareRemainder[d_]:=SquareRemainder[d]=Simplify[d-SqrtPolyPart[d]^2]


(* ::Subsection:: *)
(*Representation of continued fraction*)

(* ::Text:: *)
(*We represent every quadratic element in the form (a+t+Sqrt[d])/s, where a is the polynomial part of Sqrt[d]. We abbreviate Complete Quotient to CQ. Because we will use them mostly in continued fraction expansions, we also keep track of the position.*)

CQ[n,d,t,s]


(* ::Text:: *)
(*For the nicest formulas, we want to normalise such that s| (d-(a+t)^2.*)

CQNormalise[CQ[n_,d_,t_,s_]]:=Module[{a,r,g},
	a=SqrtPolyPart[d];
	r=a+t;
	g=Cancel[s/PolynomialGCD[r^2,s,d]];
	CQ[n,g^2 d,g t,g s]]


(* ::Subsection:: *)
(*Stepping in the expansion*)

(* ::Text:: *)
(*The next step is being able to compute the partial quotient from the complete quotient.*)

CQPartialQuotient[CQ[n_,d_,t_,s_]]:=Module[{a},
	a=SqrtPolyPart[d];
	Simplify[If[Exponent[t,$X]<Exponent[s,$X],
		PolynomialQuotient[2 a,s,$X],
		PolynomialQuotient[2 a+t,s,$X]]]]

CQStep[CQ[n_,d_,tn_,sn_]]:=Module[{a,da2,an,tn1},
	a=SqrtPolyPart[d];
	da2=SquareRemainder[d];
	an=CQPartialQuotient[CQ[n,d,tn,sn]];
	tn1=Simplify[an sn-2 a-tn];
	CQ[n+1,d,
		tn1,
		Simplify[PolynomialQuotient[da2-2 a tn1-tn1^2,sn,$X]]]]


(* ::Text:: *)
(*Now we obviously have to think about how we can integrate the computations over quotients.*)

(* ::Subsection:: *)
(*Access helpers*)

CQs[CQ[n_,d_,t_,s_]]:=s
CQt[CQ[n_,d_,t_,s_]]:=t
CQd[CQ[n_,d_,t_,s_]]:=d
CQn[CQ[n_,d_,t_,s_]]:=n


(* ::Text:: *)
(*We also like to have a function that facilitates iteration on the CF expansion for a given limit.*)

CQList[cq_,n_Integer/;n>=0]:=NestList[CQStep,cq,n]
CQMap[fn_,cq_,n_Integer/;n>=0]:=Map[fn,CQList[cq,n]]


(* ::Section:: *)
(*Analysing the CF expansion*)

(* ::Subsection:: *)
(*Computing Period length and Quasiperiod*)

(* ::Text:: *)
(*We always need a search limit for the period length, by default we use 40, that is nice and small.*)

QuasiPeriodLength[cq_]:=QuasiPeriodLength[cq,40]


(* ::Text:: *)
(*As we are mostly interested in continued fractions starting from a simple Sqrt[d], we assume that essentially the quasiperiod begins at index 0 or 1, and we only need to go until s becomes constant.*)

QuasiPeriodLength[cq_,bound_Integer]:=Module[cq1,
	cq1=CQStep[cq];
	If[ConstantQ[CQs[cq1]],
		CQn[cq1],
		QuasiPeriodLength[cq1,bound-1]]]


(* ::Subsection:: *)
(*Determining bounds for the period length*)

(* ::Subsection:: *)
(*Approximation fractions*)

ApproximationMatrix[cq_,-1]:={{1,0},{0,1}}
ApproximationMatrix[cq_,n_Integer/;n>=0]:=
	{{CQPartialQuotient[cq],1},{1,0}}.ApproximationMatrix[CQStep[cq],n-1]

ApproximationFraction[cq_,n_Integer/;n>=-1]:=Part[ApproximationMatrix[cq,n],All,1]
ApproximationNumerator[cq,n_Integer/;n>=-1]:=Part[ApproximationMatrix[cq,n],1,1]
ApproximationDenominator[cq,n_Integer/;n>=-1]:=Part[ApproximationMatrix[cq,n],2,1]


(* ::Subsection:: *)
(*Degrees of complete quotients*)

CQDegree[CQ[n_,d_,t_,s_]]:=Max[Exponent[d,$X]/2,Exponent[t,$X]]-Exponent[s,$X]


(* ::Section:: *)
(*Reduction*)

(* ::Subsection:: *)
(*Denominators of complete quotients*)

(* ::Subsection:: *)
(*Specialisation of CF expansion*)

(* ::Section:: *)
(*End*)

End[]
EndPackage[]
