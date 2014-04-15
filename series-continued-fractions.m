(* ::Package:: *)

$X=X;

SqrtPolyPart[d_]:=Normal[Series[Sqrt[d],{$X,\[Infinity],0}]]

SquareQ[d_]:=SameQ[d-SqrtPolyPart[d]^2,0]

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
