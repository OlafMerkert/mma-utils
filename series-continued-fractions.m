(* ::Package:: *)

(* ::Section:: *)
(*Continued fraction algorithm*)

(* ::Subsection:: *)
(*Elementary definitions*)

$X=X;
SqrtPolyPart[d_]:=Normal[Series[Sqrt[d],{$X,\[Infinity],0}]]
SquareQ[d_]:=SameQ[d-SqrtPolyPart[d]^2,0]
ConstantQ[xpr_]:=SameQ[0,Exponent[xpr,$X]]

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

CQPartialQuotient[CQ[n_,d_,t_,s_]]:=Module[a,
	a=SqrtPolyPart[d];
	If[deg[t,$X]<deg[s,$X],
		PolynomialQuotient[2 a,s,$X],
		PolynomialQuotient[2 a+t,s,$X]]]

CQStep[CQ[n_,d_,tn_,sn_]]:=Module[{a,an,rn1},
	a=SqrtPolyPart[d];
	an=CQPartialQuotient[CQ[n,d,tn,sn]];
	rn1=an sn- a-tn;
	CQ[n+1,d,rn1-a,Cancel[(d-rn1^2)/sn]]]

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

CQList[cq_,n_Integer/;n>=0]:=Nest[CQStep,cq,n]
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
