(* ::Package:: *)

BeginPackage["RingQuotients`"]

QModPrimeQ::usage="Test if an ideal contains a prime number among
	its generators."
QMod::usage="Used to represent quotient elements."
QModPrime::usage="Determine the characteristic of the quotient,
	i.e. extract a prime from an ideal specification. If no prime
	is present, return 0."
QModGenerators::usage="Extract the polynomials generating the ideal, 
	removing any primes from the specification."
QModVariables::usage="Produce a list of all the variables occuring 
	in the ideal specification."
QModCanonical::usage="Simplify a quotient element into canonical form 
	wrt the given ideal presentation."
QModGroebner::usage="Compute a Groebner basis for a given ideal representation."
QModFracCanonical::usage="Put a fraction of quotient elements into canonical form."
QModCanonicalAny::usage="Put any expression of quotient elements into canonical form."
QModPower::usage="Raise quotient elements to powers"
QModCanonical::"Put a QMod expression into canonical form."
QModC::"Abbreviation for QModCanonical."

Begin["`Private`"]

(* ::Section::Closed:: *)
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


(* ::Section::Closed:: *)
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
(*Also add a shorter version for duality with QMod*)

QModC[el_,ideal_]:=QModCanonical[QMod[el,ideal]]


(* ::Text:: *)
(*Also, it would seem useful to simplify to a Groebner Base.*)

QModGroebnerCanonical[QMod[el_,ideal_]]:=QModCanonical[QMod[el,QModGroebner[ideal]]]


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

(* ::Text:: *)
(*First we need to analyse which operations for polynomials we actually need. The main customer for now is the Laurent series CF process for square roots, where we use:*)
(*	Exponent*)
(*	SqrtPolyPart, relying on Series*)
(*	PolynomialGCD*)
(*	Cancel (we can use our normalisation functions there)*)
(*	PolynomialQuotient*)
(*	*)
(*Another consideration would be, that the CF code should work transparently with normal polynomials, so we only have to use QMod when really necessary.*)

Unprotect[Exponent];
Exponent[QMod[el_,ideal_],form_]:=Exponent[el,form]
Protect[Exponent];

QModCoefficientList[QMod[el_,ideal_],var_]:=QModC[#,ideal]&/@CoefficientList[el,var]

QModCoefficientList[poly1,X]

QModCoefficientList[poly1,X].(X^Table[i,{i,0,4}])


(* ::Text:: *)
(*Unfortunately, we made QMod absorbing, so the smartest thing to do would be to do operations on elements, and normalise later (perhaps coefficientwise for less complexity).*)

(* ::Section:: *)
(*End*)

End[]
EndPackage[]
