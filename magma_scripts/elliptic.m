// Z/11Z

B := 100;

function Has_1_11_Torsion(d)

    E := EllipticCurve([0,-1,-1,0,0]);
    Ed := QuadraticTwist(E,d);

    // first compute analytic rank zero or not via twisted winding element

    r, flag := Rank(Ed);

    if r gt 0 then
        ans := true;
    else
        ans := false;
    end if;

    return ans, flag;
end function;