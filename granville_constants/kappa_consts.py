"""kappa_consts.py

    Quick scratch code to compute Granville's kappa' constant
    for X_1(13), X_1(16), and X_1(18).

    This just follows the definitions in Section 1.1 of Granville's paper.
    Since all three models have leading coefficient 1, we can simplify the
    definition of omega_prime.

"""

### Globals

R.<x> = QQ[]

# how many Good euler factors to take in the product
NUM_GOOD_PRIMES = 5000  

# for the bad primes, how many terms to take in the series. Making this 
# too large kills the speed massively.
SERIES_TERMS = 5

# the constants N and m are fixed by Granville as follows
N = 6
m = 2

# This is Granville's omega constant
def omega(f,r):
    if is_prime(r):
        f = f.change_ring(GF(r))
        return len(f.roots())
    output = 0
    for i in range(r):
        if f(i)%r == 0:
            output += 1
    return output

# This is Granville's omega' (omega prime) constant
def omega_prime(f, p, k):
    assert f.leading_coefficient() == 1
    return p^(k-1) * (p - 1) * omega(f,p^k)


def kappa_f_prime(f, V_f_prime, A_f_Q):
    """
        Computes the kappa_f_prime constant in Section 1.1

        f - the polynomial
        V_f_prime - the area of the unit ball for F, computed in euclidean_contribution.ipynb
        A_f_Q - the constant of the same name, which is just #Aut_Q(C)/2
        
        returns: kappa_f_prime

    """

    disc_f = f.discriminant()

    bad_primes = ZZ(disc_f).prime_divisors()
    good_primes = [p for p in primes_first_n(NUM_GOOD_PRIMES) if p not in bad_primes]

    good_prime_contribution = 1
    for p0 in good_primes:
        p = RR(p0)
        term = 1 + omega(f,p0)*(p-1)*(p^(2*m/N) - 1) / (p* (p^m - p^(2*m/N)))
        good_prime_contribution *= term

    bad_prime_contribution = 1
    for p in bad_primes:

        terms_to_sum = [ (omega_prime(f,p,i*m)/RR(p)^(2*i*m*(1 - 1/N))) for i in range(1,SERIES_TERMS + 1) ]
        term = sum(terms_to_sum)
        term = 1 + (1 - (1/RR(p)^(2*m/N)))*term
        bad_prime_contribution *= term

    finalans = (V_f_prime/A_f_Q) * good_prime_contribution * bad_prime_contribution 
    return finalans

# Main calling function
def main():
    f = x*(x^2+1)*(x^2+2*x-1)
    V_f_prime = 6.132666484981952
    A_f_Q = 2
    kappa = kappa_f_prime(f, V_f_prime, A_f_Q)
    print(f"Kappa for X1(16) is {kappa}")

    f = x^6 - 2*x^5 + x^4 - 2*x^3 + 6*x^2 - 4*x + 1
    V_f_prime = 3.9325551449299807
    A_f_Q = 3
    kappa = kappa_f_prime(f, V_f_prime, A_f_Q)
    print(f"Kappa for X1(13) is {kappa}")

    f = x^6 + 2*x^5 + 5*x^4 + 10*x^3 + 10*x^2 + 4*x + 1
    V_f_prime = 3.517982630376745
    A_f_Q = 3
    kappa = kappa_f_prime(f, V_f_prime, A_f_Q)
    print(f"Kappa for X1(18) is {kappa}")

main()