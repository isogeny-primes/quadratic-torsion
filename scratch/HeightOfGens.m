/*TorsionPrimes.m

  Use this script to generate torsion prime data:

myArray=(-6431 17)

myArray=(-9879 -9815 -9727 -9719 -9670 -9663 -9638 -9615 -9565 -9461 -9307 -9095 -8819 -8641 -8419 -8399 -7863 -7727 -7694 -7663 -7630 -7199 -6641 -6431 -6423 -6362 -6257 -6009 -5989 -5855 -5757 -5597 -5394 -5293 -5237 -5095 -4839 -4670 -4605 -4603 -4454 -4442 -4439 -4289 -4233 -4139 -4087 -4055 -3782 -3597 -3463 -3407 -3390 -3385 -3226 -3223 -3071 -3047 -2866 -2683 -2631 -2507 -2441 -2437 -2426 -2339 -2335 -2255 -2135 -2031 -1865 -1695 -1671 -1637 -1559 -1535 -1199 -1090 -935 -901 -779 -703 -671 -527 -510 -411 -377 -366 -359 -311 -303 -302 -287 -174 -29 1 17 79 113 145 193 313 409 442 481 493 646 673 718 745 957 1153 1173 1185 1271 1385 1417 1457 1465 1510 1537 1609 1659 1713 1870 1921 1943 1955 2038 2089 2161 2257 2265 2427 2433 2553 2629 3005 3057 3131 3193 3241 3273 3361 3473 3478 3535 3585 3649 3769 3878 3961 4033 4315 4354 4449 4549 4641 5026 5095 5241 5242 5289 5394 5449 5593 5777 5781 6139 6162 6217 6351 6393 6409 6582 6641 6769 6806 7017 7143 7234 7382 7521 7549 7671 7694 7802 8065 8081 8113 8122 8466 8473 8578 8579 8641 9141 9265 9418 9501 9689 9865 9877 9881)

parallel -j64 "magma -b d:={} HeightOfGens.m" ::: "${myArray[@]}"

*/

R<x> := PolynomialRing(Rationals());
//y^2=f is isomorphic to  X_1(13)
bound := 5;
f := R![1, 2, 1, 2, 6, 4, 1];

OutputFileName := "output.csv";

dInt := StringToInteger(d);
C:=HyperellipticCurve(dInt*f);
J := Jacobian(C);
MW, MWtoSet, flag1, flag2, bound := MordellWeilGroupGenus2(
J:
SearchBounds := [bound],
SearchBounds2 := [5,10,20,50, 100,200,500, 1000,2000,5000,10000,20000,50000,100000],
SearchBounds3 := [bound],
// We know the rank to be > 1 in these cases under bsd.  However we set the rank bound
// to 1 to stop searching after having found a point of infinite order.
Rankbound := 1,
// the next three are only for proving better upperbounds on heights so we set them very small
LogDiscBound := 1,
TwistSearchBound := 1,
TwistBound := 1
);
//inv := Invariants(MW);
pts := [MWtoSet(i) : i in  Generators(MW)];

aPt := pts[1];
height := NaiveHeight(aPt);

xStr := Sprint(aPt[1]);
yStr := Sprint(aPt[2]);
zStr := Sprint(aPt[3]);

toPrint := d cat "," cat RealToString(height) cat "," cat Sprint(flag1) cat "," cat Sprint(flag2) cat "," cat xStr cat "," cat yStr cat "," cat zStr;
Write(OutputFileName, toPrint);
quit;