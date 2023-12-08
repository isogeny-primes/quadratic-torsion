QQ := Rationals();
Qx<x> := PolynomialRing(QQ);

f1 := x;
f2 := x^2+1;
f3 := x^2 - 2*x - 1;
f := -f1*f2*f3;

d := 10;

x1_16 := HyperellipticCurve(f);

C := HyperellipticCurve(d*f);

K<a> := QuadraticField(d);

CK := BaseExtend(x1_16,K);

ptsC := Points(C : Bound:=10000);

J := Jacobian(C);

MW, MWtoSet, flag1, flag2, bound := MordellWeilGroupGenus2(
                                    J : 
                                    // RankOnly := true,
                                    SearchBounds := [1000,2000,5000,10000],
                                    SearchBounds2 := [1000,2000,5000,10000],
                                    SearchBounds3 := [200,500,1000,2000]
);

assert flag1;
assert flag2;

bas := [J!(MWtoSet(i)) : i in  Generators(MW)];

prec:=100;
QQ := RationalsExtra(prec);
Qx<x> := PolynomialRing(QQ);

f1 := x;
f2 := x^2+1;
f3 := x^2 - 2*x - 1;
f := -f1*f2*f3;

-8259, -7973, -7615, -7161, -7006, -6711, -6503, -6095,\\
        &-6031, -6005, -4911, -4847, -4773, -4674, -4371, -4191,\\
        &-4074, -3503, -3199, -1810, -1749, -815, 969, 1186,\\
        &3215, 3374, 3946, 4633, 5257, 5385, 7006, 7210,\\
        &7733, 8459, 8479, 8569, 9709, 9961\\

valsToCheck := [-6031, -6005, -4911, -4847, -4773, -4674, -4371, -4191,-4074, -3503, -3199, -1810, -1749, -815, 969, 1186, 3215, 3374, 3946, 4633, 5257, 5385, 7006, 7210, 7733, 8459, 8479, 8569, 9709, 9961];
AttachSpec("CHIMP/endomorphisms/endomorphisms/magma/spec");
for d in valsToCheck do

    C := HyperellipticCurve(d*f);
    desc := HeuristicEndomorphismAlgebra(C);
    print d, desc, "\n";
end for;