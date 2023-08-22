A<x,y,z> := AffineSpace(Rationals(),3);

f1 := -x;
f2 := x^2+1;
f3 := x^2 - 2*x - 1;
f := f1*f2*f3;

C12 := Curve(A,[y^2-f1*f3, z^2-f2*f3]);

phi := CanonicalMap(C12);
C12c := Image(phi);
R1<u1,v1,w1,u,v,w,l> := PolynomialRing(Rationals(),7);
g := DefiningEquation(C12c);
g := Evaluate(g,[u,v,w]);
I := ideal< R1 | [g, u*u1+v*v1+w*w1] cat [uvw[1] - l * Derivative(g,uvw[2]) : uvw in [[u1,u],[v1,v],[w1,w]]]>;
gdual := GroebnerBasis(EliminationIdeal(I,{u1,v1,w1}))[1];
P<x1,y1,z1> := ProjectiveSpace(Rationals(),2);
C12dual := Curve(P, Evaluate(gdual,[x1,y1,z1,0,0,0,0]));
tangents := IrreducibleComponents(SingularSubscheme(C12dual));
[<Degree(T),IsReduced(T)> : T in tangents];
tangents := [ReducedSubscheme(T) : T in tangents];
T := tangents[#tangents];
S1 :=
//x1=0, z1 = +/-sqrt(2)y1
P<x2,y2,z2,u2> := ProjectiveSpace(Rationals(),3);
B1:= Curve(P, [y2^2-2*z2^2-u2^2,Evaluate(g,[0,0,0,x2,y2,z2,0])]);
B2:= Curve(P, [y2^2+2*z2^2-u2^2,Evaluate(g,[0,0,0,x2,y2,z2,0])]);
P<x2,y2,z2,u2,v2> := ProjectiveSpace(Rationals(),4);
//B3:= Curve(P, [y2^2+2*z2^2-u2^2,y2^2-2*z2^2-v2^2,Evaluate(g,[0,0,0,x2,y2,z2,0])]);
B3:= Curve(P, [y2^2+2*z2^2-u2^2,(y2^2-2*z2^2)*v2^2-(2*y2^4-x2^4),Evaluate(g,[0,0,0,x2,y2,z2,0])]);
B1,B2 := Explode([Curve(B): B in IrreducibleComponents(B3)]);
B1can := Image(CanonicalMap(B1));
B2can := Image(CanonicalMap(B2));
DefiningIdeal(B1can);
DefiningIdeal(B2can);
P<x2,y2,u2,v2> := AffineSpace(Rationals(),4);
//B3:= Curve(P, [y2^2+2*z2^2-u2^2,y2^2-2*z2^2-v2^2,Evaluate(g,[0,0,0,x2,y2,z2,0])]);
B3:= Curve(P, [y2^2+2*1^2-u2^2,v2^2-(2*y2^4-x2^4),Evaluate(g,[0,0,0,x2,y2,1,0])]);


S1 := ReducedSubscheme(Scheme(C12c, y^2+2*z^2));
S2 := ReducedSubscheme(Scheme(C12c, y^2-2*z^2));
S3 := ReducedSubscheme(Scheme(C12c, 2*y^4-x^4));
D1 := Divisor(C12c, S1);
D2 := Divisor(C12c, S2);
D3 := Divisor(C12c, S3);
IsLinearlyEquivalent(D1,D2);
IsLinearlyEquivalent(D1+D2, D3);
IsLinearlyEquivalent(2*D1,D3);


/*
    $.3^3 - 112*$.2*$.4^2 - 136*$.3*$.4^2 + 560*$.2*$.5^2 - 104*$.3*$.5^2,
    $.1^2 - 1/56*$.3^2 + 10/7*$.4^2 - 8/7*$.5^2,
    $.2^2 - 1/28*$.3^2 - 8/7*$.4^2 - 16/7*$.5^2,
    $.2*$.3 - 3/14*$.3^2 + 8/7*$.4^2 - 40/7*$.5^2

    $.3^3 + 112*$.2*$.4^2 - 136*$.3*$.4^2 + 560*$.2*$.5^2 + 104*$.3*$.5^2,
    $.1^2 + 1/56*$.3^2 - 10/7*$.4^2 - 8/7*$.5^2,
    $.2^2 - 1/28*$.3^2 - 8/7*$.4^2 + 16/7*$.5^2,
    $.2*$.3 + 3/14*$.3^2 - 8/7*$.4^2 - 40/7*$.5^2

*/
/*

x2^2 - 1/2*u2^2 - u2*v2 + 1/2*v2^2
x2^2 - 1/2*u2^2 + u2*v2 + 1/2*v2^2,





G := AutomorphismGroup(B1);