_<x>:=PolynomialRing(Rationals());
f := x^6-2*x^5+x^4-2*x^3+6*x^2-4*x+1;
C:=HyperellipticCurve(f);
J:=Jacobian(C);

d := 673;

C1:=QuadraticTwist(C,d);
J1:=Jacobian(C1); // this has rank 2

a,b,_:=AutomorphismGroup(C1);

for phi in a do
    if Order(phi) gt 1 then 
        Cquot, mymap := CurveQuotient(AutomorphismGroup(C1,[b(phi)]));
        conicModel,_ := Conic(Cquot);
        print "ans for quotient by", phi, " is", IsLocallySoluble(conicModel);
    end if;
end for;

allOrder3Auts := [];

for x in a do
    if Order(x) eq 3 then
        Append(~allOrder3Auts,x);
    end if;
end for;

anOrder3Aut := allOrder3Auts[1];
assert Order(anOrder3Aut) eq 3;

Cquot, mymap := CurveQuotient(AutomorphismGroup(C1,[b(anOrder3Aut)]));

somePts := Points(Cquot : Bound := 100);

aRatPt := somePts[1];

deg3Divisor:=Pullback(mymap,Place(aRatPt));
assert Degree(deg3Divisor) eq 3;

a,b,_,_,_ := MordellWeilGroupGenus2(J1);

bas := [J1!(b(a.1)), J1!(b(a.2))];

f1,_ := HyperellipticPolynomials(C1);
deg3 := 1/6*(-673*x^2 + 673*x);
Attach("MWSieve-new.m");
SetVerbose("MWSieve", 1); SetVerbose("GroupInfo", 1); // see what happens...

HasPointMWSieve(J1, bas, deg3);

/*

a,b,_,_,_ := MordellWeilGroupGenus2(J1);

bas := [J1!(b(a.1)), J1!(b(a.2))];

f1,_ := HyperellipticPolynomials(C1);

deg3 := 1/6*(-673*x^2 + 673*x);  // this is wrong, this doesn't work

Attach("MWSieve-new.m");
SetVerbose("MWSieve", 1); SetVerbose("GroupInfo", 1); // see what happens...

// payload

HasPointMWSieve(J1, bas, deg3);  // this fails because deg3 is wrong above

*/

/* 
//bad box search

for a1 in [-30..30] do
    for a2 in [-10..10] do
        for a3 in [-10..10] do
            for a4 in [-5..5] do
                deg3 := (a1/3)*x^3 + (a2/7)*x^2 + a3*x + a4;
                fd3 := Factorization(f1 - deg3^2);
                degs := [Degree(a[1]) : a in fd3];
                bools := [IsOdd(x) : x in degs];
                if true in bools then
                    print deg3;
                end if;
            end for;
        end for;
    end for;
end for;

for a1 in [-100..100] do
    for a2 in [-100..100] do
        for a3 in [-100..100] do

            deg3 := (a1/4)*x^2 + (a2/2)*x + (a3/1);
            fd3 := Factorization(f1 - deg3^2);
            degs := [Degree(a[1]) : a in fd3];
            bools := [IsOdd(x) : x in degs];
            if true in bools then
                print deg3;
            end if;

        end for;
    end for;
end for;

*/