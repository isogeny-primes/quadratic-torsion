_<x>:=PolynomialRing(Rationals());
f := x^6-2*x^5+x^4-2*x^3+6*x^2-4*x+1;
C:=HyperellipticCurve(f);
J:=Jacobian(C);

d := 79;

C1:=QuadraticTwist(C,d);
J1:=Jacobian(C1); // this has rank 2

a,b,_,_,_ := MordellWeilGroupGenus2(J1);

bas := [J1!(b(a.1)), J1!(b(a.2))];

f1,_ := HyperellipticPolynomials(C1);

deg3 := x^3;  // this is wrong, this doesn't work

Attach("MWSieve-new.m");
SetVerbose("MWSieve", 1); SetVerbose("GroupInfo", 1); // see what happens...

// payload

HasPointMWSieve(J1, bas, deg3);  // this fails because deg3 is wrong above

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
*/