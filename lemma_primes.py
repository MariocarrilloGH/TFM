from sympy import primerange
from math import log2

for N in range(2,50):
    prod = 1
    for p in primerange(16*log2(N)):
        prod *= p
    """print(f"N: {N}")
    print(f"Primes product: {prod}")
    print()"""
    assert(N<prod)