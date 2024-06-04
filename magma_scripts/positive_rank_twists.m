// This is the Magma implementation of the sage code in quadratic_torsion/positive_rank_twists.py
// Since it is about 8 times slower than the sage code, we do the computation there.
// The code here can be used to verify the sage implementation. However, this code is
// not needed to reproduce the results of our paper.

function IsZeroRankofTwist(G,d)
// This is the Magma implementation of the sage function is_rank_of_twist_zero(G, d) in
//   quadratic_torsion/positive_rank_twists.py
// Since it is about 8 times slower than the sage code, we do this compution in sage.
// And this function is not actually used. However we still include it in case someone
// wants to verify out results using magma.
// it uses modular symbols to compute wether the analytic rank is 0 or not
// if the analytic rank is 0 then the algebraic rank is also guaranteed to be 0
  M := ModularSymbols(G);
  S := CuspidalSubspace(M);
  chi := BaseExtend(KroneckerCharacter(d),RationalField());
  tw := TwistedWindingElement(S,1, chi);
  // print tw;
  twmap := RationalMapping(S)(tw);
  // print twmap;
  return not twmap eq Parent(twmap)!0;
end function;


// For each of the elliptic curves that have positive analytic rank
// we verify that they also have positive algebraic rank.
// It returns true, 0 if all twists of E by the integers d in Dlist indeed have postive
// algberaic rank. And returns false, d whenever there is an integer d such that E
// twisted by d has rank 0.
procedure VerifyPositiveRank(E, Dlist)
    for d in Dlist do
        Ed := QuadraticTwist(E,d);
        if Rank(Ed) eq 0 then
          return false, d;
    end for;
    return true, 0;
end procedure;
