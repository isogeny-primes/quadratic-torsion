A<x,y,z> := AffineSpace(Rationals(),3);
R<x1> := PolynomialRing(Rationals());

p := 79;

f1 := -79*x;
f2 := x^2+1;
f3 := x^2 - 2*x - 1;
f := f1*f2*f3;

C12 := Curve(A,[y^2-f1*f3, z^2-f2*f3]);
E12 := Curve(A,[y^2-f1, z^2-f2]);

C := Curve(A,[y^2-f,z]);
C1 := Curve(A,[y^2-f, z^2-f1]);
C2 := Curve(A,[y^2-f, z^2-f2]);
C3 := Curve(A,[y^2-f, z^2-f3]);
_, CH, phi := IsHyperelliptic(C);
_, CH1, phi1 := IsHyperelliptic(C1);
_, CH2, phi2 := IsHyperelliptic(C2);
_, CH3, phi3 := IsHyperelliptic(C3);

[#Factorization(HyperellipticPolynomials(Ci)) : Ci in [CH1,CH2,CH3]];


auts := Automorphisms(CH1);
for i in [1..#auts] do
  g1 := auts[i];
  Gi := AutomorphismGroup(CH1, [g1]);
  Ci,phi_i := CurveQuotient(Gi);
  if Genus(Ci) in [0,3] then continue; end if;
  print Genus(Ci),Ci;
  print phi_i;
end for;