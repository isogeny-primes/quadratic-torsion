R<x> := PolynomialRing(Rationals());
X := HyperellipticCurve(x^6 - 2*x^5 + x^4 - 2*x^3 + 6*x^2 - 4*x + 1);
rationalCusps := Points(X : Bound := 100);
pt0 := rationalCusps[1];
genSet := [ptC - pt0 : ptC in rationalCusps];
[Order(P) : P in genSet];
T := [i * genSet[2] : i in [1..19]];
[P in T : P in genSet];
TorsionSubgroup(J);
TorsionBound(J, 100);


runningGCD := 0;
R<x> := PolynomialRing(Rationals());
X := HyperellipticCurve(x^6 - 2*x^5 + x^4 - 2*x^3 + 6*x^2 - 4*x + 1);
J := Jacobian(X);
for p in PrimesInInterval(5,30) do
    Jred := BaseChange(J,GF(p^2));
    runningGCD := GCD(runningGCD, #Jred);
end for;
print runningGCD;

for p in PrimesInInterval(5,30) do
   print p , Invariants(ClassGroup(ChangeRing(C, GF(p^2))));
end for;

positive_rank := [-9791, -9489, -9434, -9431, -9206, -9201, -9031, -8999, -8979, -8966, -8858, -8639, -8627, -8449, -8327, -8243, -8123, -7909, -7847, -7671, -7487, -7447, -7323, -7319, -7199, -7071, -7010, -6911, -6749, -6645, -6623, -6611, -6479, -6323, -6263, -6191, -6187, -6159, -6047, -5963, -5885, -5883, -5543, -5295, -5255, -5207, -5165, -5095, -4895, -4751, -4694, -4679, -4535, -4521, -4515, -4103, -4031, -3881, -3815, -3743, -3371, -3299, -3239, -3149, -3135, -3095, -3041, -2915, -2861, -2834, -2759, -2579, -2495, -2406, -2378, -2279, -2183, -2087, -2055, -2037, -1991, -1943, -1941, -1931, -1871, -1853, -1851, -1658, -1623, -1517, -1511, -1509, -1455, -1407, -1358, -1335, -1223, -1221, -1191, -1151, -1118, -1046, -1011, -935, -863, -817, -807, -794, -654, -647, -627, -623, -591, -542, -533, -503, -497, -431, -426, -407, -402, -287, -267, -215, -143, -139, -129, -110, -71, -59, 1, 33, 43, 109, 123, 137, 253, 267, 337, 353, 417, 457, 469, 497, 654, 681, 697, 858, 871, 985, 1009, 1122, 1142, 1261, 1293, 1294, 1329, 1342, 1345, 1353, 1509, 1649, 1699, 1726, 1727, 1761, 1793, 1993, 2155, 2310, 2314, 2329, 2557, 2589, 2759, 2833, 2841, 2913, 2962, 3082, 3281, 3282, 3442, 3485, 3489, 3493, 3637, 3741, 3769, 3806, 3927, 4081, 4145, 4529, 4615, 4642, 4729, 5137, 5149, 5161, 5281, 5369, 5379, 5659, 5878, 6001, 6082, 6217, 6490, 6601, 6729, 6819, 7057, 7234, 7242, 7321, 7359, 7369, 7469, 7521, 7655, 7705, 7926, 8205, 8241, 8274, 8339, 8382, 8409, 8421, 8633, 8729, 8965, 8989, 9042, 9049, 9097, 9137, 9183, 9431, 9483, 9586, 9705, 9726, 9790, 9869, 9890, 9913, 9969];
positive_rank2 := [d : d in positive_rank | (d gt 0) and (d mod 8 eq 1) and (d mod 3 ne 2)];
R<x> := PolynomialRing(Rationals());
//y^2=f is isomorphic to  X_1(18)
f := R![1, 2, 5, 10, 10, 4, 1];
output := [];
for d in positive_rank2 do
    if IsSquarefree(d) then
        if HasPointsEverywhereLocally(d*f,2) then
            C := HyperellipticCurve(d*f);
            if #TwoCoverDescent(C) gt 0 then
                Append(~output, d);
            end if;
        end if;
    end if;
end for;

print output;

for d in [-100..100] do
    if (d ne 0) and (d ne 1) then
        if IsSquarefree(d) then
            K<a> := NumberField(x^2 - d);
            JK := BaseExtend(J,K);
            B := TorsionBound(JK,100);
            if B ne 20 then
                print d, B;
            end if;
        end if;
    end if;
end for;