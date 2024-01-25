// This is the Magma implementation of the sage code in quadratic_torsion/positive_rank_twists.py
// Since it is about 8 times slower than the sage code, we do the computation there
// and come here for the rank verification.

function IsZeroRankofTwist(G,d)
  M := ModularSymbols(G);
  S := CuspidalSubspace(M);
  chi := BaseExtend(KroneckerCharacter(d),RationalField());
  tw := TwistedWindingElement(S,1, chi);
  // print tw;
  twmap := RationalMapping(S)(tw);
  // print twmap;
  return not twmap eq Parent(twmap)!0;
end function;


// Anyway, the following verifies the list of values in the genus_one_lists folder

procedure VerifyPositiveRank(Dlist)
    for d in Dlist do
        Ed := QuadraticTwist(E,d);
        assert Rank(Ed) gt 0;
    end for;
end procedure;
