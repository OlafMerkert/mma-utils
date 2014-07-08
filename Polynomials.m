(* ::Package:: *)

Poly[coeffvar_,degree_,varvar_]:=Sum[coeffvar[i]varvar^i,{i,0,degree}]
Poly[coeffvar_,degree_]:=Poly[coeffvar,degree,X]

MonicPoly[coeffvar_,degree_,varvar_]:=Poly[coeffvar,degree,varvar]/.coeffvar[degree]->1
MonicPoly[coeffvar_,degree_]:=MonicPoly[coeffvar,degree,X]
