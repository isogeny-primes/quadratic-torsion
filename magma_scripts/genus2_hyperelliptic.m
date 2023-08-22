A<x,y,z> := AffineSpace(Rationals(),3);
R<x1> := PolynomialRing(Rationals());

f1 := -x;
f2 := x^2+1;
f3 := x^2 - 2*x - 1;
f := f1*f2*f3;
d := 79;
C := Curve(A,[y^2-d*f,z]);
_, CH := IsHyperelliptic(C);