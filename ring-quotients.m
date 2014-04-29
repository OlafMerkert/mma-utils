(* ::Package:: *)

(* ::Section:: *)
(*Quotients of free algebras over \[DoubleStruckCapitalQ] and Subscript[\[DoubleStruckCapitalF], p]*)

(* ::Text:: *)
(*We need to be able to compute with sufficient efficiency in Z or Q algebras of finite type, i.e. polynomials modulo a finite number of polynomials, and possibly a prime number. We represent ideals simply by lists.*)

(* ::Text:: *)
(*First of all, we need to distinguish between the main cases, whether the ideal contains a prime.*)

QModPrimeQ[ideal_]:=MemberQ[ideal,_?PrimeQ]

(* ::Text:: *)
(*The next step is to extract said prime, and make sure there not any conflicting ones.*)

QMod::InvalidIdealSpec="too many primes in ideal specification";

QModPrime[ideal_]:=Module[{ps},
	ps=Select[ideal,PrimeQ];
	Which[
		Length[ps]==1,First[ps],
		Length[ps]==0,0,
		True,Message[QMod::InvalidIdealSpec]]]

(* ::Text:: *)
(*We also want to extract all other elements conveniently.*)

QModGenerators[ideal_]:=Select[ideal,Composition[Not,PrimeQ]]

(* ::Text:: *)
(*As we are working with multivariate polynomials, we also need to choose a monomial ordering and figure out which variables are available*)

QModVariables[ideal_]:=Cases[ideal,_Symbol,\[Infinity]]

QModVariables[{2,X+1,Y^4+X Z^3}]

(* ::Text:: *)
(*We might have to come back to this, if things like a[3] should also be recognized as a variable.*)

QModCanonical[el_,ideal_]:=PolynomialMod[
	el,QModGenerators[ideal],
	(*QModVariables[Append[ideal,el]],*)Modulus->QModPrime[ideal]]

(* ::Text:: *)
(*For efficiency reasons, we should perhaps use a Groebner Basis for our ideal.*)

QModGroebner[ideal_]:=Module[{basis},
	basis=GroebnerBasis[QModGenerators[ideal],QModVariables[ideal],Modulus->QModPrime[ideal]];
	If[QModPrimeQ[ideal],
		Prepend[basis,QModPrime[ideal]],
		basis]]

(* ::Section:: *)
(*Fractions fields of such algebras*)

(* ::Text:: *)
(*For the standard operations like addition and multiplication, we just need the above function to go to canonical form. However, for fractions and division, we need more complicated normalisation procedures.*)
(*As a first step, we always normalise numerator and denominator, afterwards we pull out the GCD.*)

QModFracCanonical[num_,denom_,ideal_]:=Module[{numc,denomc,g},
	numc=QModCanonical[num,ideal];
	denomc=QModCanonical[denom,ideal];
	g=PolynomialGCD[numc,denomc,Modulus->QModPrime[ideal]];
	Cancel[{numc,denomc}/g]]

QModCanonicalAny[expr_,ideal_]:=If[NumberQ[Denominator[expr]],
	QModCanonical[expr,ideal],
	Divide@@QModFracCanonical[Numerator[expr],Denominator[expr],ideal]]

(* ::Text:: *)
(*Use square multiply for raising elements in the quotient to powers:*)

SquareMultiply[expr_,n_Integer/;n>=0,square_,multiply_]:=Module[{digits,result},
	digits=IntegerDigits[n,2];
	result=1;
	Map[Function[{digit},
		result=multiply[expr,square[result]]],
		digits];
	result]		

(* ::Text:: *)
(*Here we assume that expr is not a fractional expression, and n should be be non-negative. The more general case will be treated below.*)

QModPower[expr_,n_Integer/;n>=0,ideal_]:=Module[{prime,generators},
	prime=QModPrime[ideal];
	generators=QModGenerators[ideal];
	SquareMultiply[expr,n,
		Function[{el},PolynomialMod[el^2,generators,Modulus->prime]],
		Function[{el1,el2},PolynomialMod[el1 el2,generators,Modulus->prime]]]];

(* ::Section:: *)
(*Representation of elements*)

(* ::Text:: *)
(*Elements can be represented as follows.*)

QMod[el,ideal]

(* ::Text:: *)
(*Next, we implement the standard operations on them:*)

Unprotect[Plus,Times];
QMod[el1_,ideal_]+QMod[el2_,ideal_]:=QMod[QModCanonicalAny[el1+el2,ideal],ideal]
QMod[el1_,ideal_] QMod[el2_,ideal_]:=QMod[QModCanonicalAny[el1 el2,ideal],ideal]
el1_+QMod[el2_,ideal_]:=QMod[QModCanonicalAny[el1+el2,ideal],ideal]
el1_ QMod[el2_,ideal_]:=QMod[QModCanonicalAny[el1 el2,ideal],ideal]
Protect[Plus,Times];

(* ::Text:: *)
(*If we start off, we also want to be able to normalise a single element.*)

QModCanonical[QMod[el_,ideal_]]:=QMod[QModCanonicalAny[el,ideal],ideal]

(* ::Text:: *)
(*Finally, for powers, we want to use square multiply mod things, so we use a very special algorithm*)

Unprotect[Power];
QMod[el_,ideal_]^0:=1;
QMod[el_,ideal_]^n_Integer:=Module[{result},
	result=If[NumberQ[Denominator[el]],
		QModPower[el,Abs[n],ideal],
		Divide[QModPower[Numerator[el],Abs[n],ideal],
			QModPower[Denominator[el],Abs[n],ideal]]];
	QMod[If[n<0,
		1/result,
		result],ideal]]
Protect[Power];

(* ::Section:: *)
(*Univariate Polynomials over such fraction fields*)

(* ::Section:: *)
(*Some tests*)

QMod[t^2+t+1,{t^2+7}]+QMod[t^4+1,{t^2+7}]

QMod[t^2+t+1,{t^2+7}] QMod[t^4+1,{t^2+7}]

QModCanonical[QMod[t^2+t+1,{t^2+7}]]

QMod[t^2+t+1,{3,t^2+7}]^20
