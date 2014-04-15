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

QMod::InvalidIdealSpec="oo many primes in ideal specification";

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

QModCanonical[el_,ideal_]:=PolynomialReduce[
	el,QModGenerators[ideal],
	QModVariables[Append[ideal,el]],Modulus->QModPrime[ideal]]

(* ::Section:: *)
(*Fractions fields of such algebras*)
