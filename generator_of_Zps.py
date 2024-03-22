import sympy
import random
import math


def generator_of_Zp(p):
    if (p==2):
        g = 1
    elif (p==3):
        g = 2
    else:
        q = (p-1)//2
        found = False
        while not found:
            g = random.randint(2,p-2)
            if (pow(g,2,p)!=1 and pow(g,q,p)!=1):
                found = True
    return g


def generate_rust_struct(p):
    str_p = str(p)
    str_generator = str(generator_of_Zp(p))
    code = "#[derive(MontConfig)]\n#[modulus = \""+str_p+"\"]\n#[generator = \""+str_generator+"\"]\npub struct FqConfig"+str_p+";\npub type Z_"+str_p+" = Fp64<MontBackend<FqConfig"+str_p+",1>>;\n\n"
    return code


d = 3 #Polynomial degree
m = 3 #Number of variables
q = 7 #Z_q
M = pow(d,m)*pow(q,m*(d-1)+1)
new_bound = 16*math.log2(M)
highest_bound_so_far = 0
primes = sympy.sieve.primerange(highest_bound_so_far,new_bound)