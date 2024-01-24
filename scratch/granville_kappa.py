# Quick scratch code to compute Granville's kappa' constant
# for X1(16)

R.<x> = QQ[]
f = x*(x^2+1)*(x^2+2*x-1)
f0 = f.leading_coefficient()
disc_f = f.discriminant()
n = f.degree()
N = 6
m = 2
def omega(f,r):
    if is_prime(r):
        f = f.change_ring(GF(r))
        return len(f.roots())
    output = 0
    for i in range(r):
        if f(i)%r == 0:
            output += 1
    return output

def omega_prime(f, p, k):
    assert f.leading_coefficient() == 1
    return p^(k-1) * (p - 1) * omega(f,p^k)

bad_primes = ZZ(disc_f * f0).prime_divisors()

NUM_GOOD_PRIMES = 20000

good_primes = [p for p in primes_first_n(NUM_GOOD_PRIMES) if p not in bad_primes]

good_prime_contribution = 1
for p0 in good_primes:
    p = RR(p0)
    term = 1 + omega(f,p0)*(p-1)*(p^(2*m/N) - 1) / (p* (p^m - p^(2*m/N)))
    good_prime_contribution *= term

euclidean_contribution = 6.132666484981952  # see granville_euclidean.ipynb

SERIES_TERMS = 9  # making this too large kills the next computation

bad_prime_contribution = 1
for p in bad_primes:

    terms_to_sum = [ (omega_prime(f,p,i*m)/RR(p)^(2*i*m*(1 - 1/N))) for i in range(1,SERIES_TERMS + 1) ]
    print(RR(terms_to_sum[-1]))
    term = sum(terms_to_sum)
    term = 1 + (1 - (1/RR(p)^(2*m/N)))*term
    bad_prime_contribution *= term


fudged_denominator = 2  # this should be #Aut_Q(C)/2
finalans = (euclidean_contribution/fudged_denominator) * good_prime_contribution * bad_prime_contribution 
print(finalans)
