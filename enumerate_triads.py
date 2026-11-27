"""Enumerate exact nonzonal Rossby triads on the square integer lattice."""
from argparse import ArgumentParser
from array import array
from math import gcd, isqrt


def multiply(z, w):
    a, b = z
    x, y = w
    return a*x-b*y, a*y+b*x


def powers(z, exponent):
    values = [(1, 0)]
    for _ in range(exponent):
        values.append(multiply(values[-1], z))
    return values


class NormTable:
    """Smallest prime factors and Gaussian generators for split primes."""
    def __init__(self, limit):
        self.factor = array("L", [0]) * (limit+1)
        for p in range(2, limit+1):
            if self.factor[p]:
                continue
            self.factor[p] = p
            if p*p <= limit:
                for m in range(p*p, limit+1, p):
                    if not self.factor[m]:
                        self.factor[m] = p
        self.split = {}
        for u in range(1, isqrt(limit)+1):
            for v in range(1, min(u, isqrt(limit-u*u))+1):
                p = u*u+v*v
                if p % 4 == 1 and self.factor[p] == p:
                    self.split[p] = (u, v)

    def circle(self, m):
        """All signed, ordered representations of m cubed by two squares."""
        base = (1, 0)
        choices = []
        while m > 1:
            p = self.factor[m]
            e = 0
            while m % p == 0:
                m //= p
                e += 3
            if p == 2:
                base = multiply(base, powers((1, 1), e)[-1])
            elif p % 4 == 3:
                if e % 2:
                    return
                base = multiply(base, (p**(e//2), 0))
            else:
                u, v = self.split[p]
                left, right = powers((u, v), e), powers((u, -v), e)
                choices.append([multiply(left[j], right[e-j]) for j in range(e+1)])
        partial = [base]
        for local in choices:
            partial = [multiply(z, w) for z in partial for w in local]
        for x, y in partial:
            yield from ((x,y), (-y,x), (-x,-y), (y,-x))


def square_roots(u, v):
    """Integer roots of (r+is)^2 = u+iv."""
    rho = isqrt(u*u+v*v)
    if rho*rho != u*u+v*v or (rho+u) % 2:
        return
    r, s = isqrt((rho+u)//2), isqrt((rho-u)//2)
    for x in {r, -r}:
        for y in {s, -s}:
            if x*x-y*y == u and 2*x*y == v:
                yield x, y


def partners(a, b, table):
    """All ordered first inputs, including zonal partners, excluding zero modes."""
    if a == 0:
        raise ValueError("the output must have nonzero zonal wavenumber")
    m = a*a+b*b
    for c, d in table.circle(m):
        u, ru = divmod(c+a*m, 2*a)
        v, rv = divmod(d+b*m, 2*a)
        if ru or rv:
            continue
        for h, j in square_roots(a*a-b*b-4*u, 2*a*b-4*v):
            if (a+h) % 2 or (b+j) % 2:
                continue
            x, y = (a+h)//2, (b+j)//2
            if (x,y) != (0,0) and (x,y) != (a,b):
                yield x, y


def normalized_input(limit, a, b, x, y, primitive):
    other = (a-x, b-y)
    if not 0 < x < a or max(abs(y), abs(b-y)) > limit or (x,y) > other:
        return False
    if b == 0 and (x,y) > min((x,-y), (a-x,y)):
        return False
    return not primitive or gcd(gcd(a, abs(b)), gcd(x, abs(y))) == 1


def box(limit, primitive=True):
    """One representative under summand exchange, signed reorientation and reflection."""
    table = NormTable(2*limit*limit)
    for a in range(1, limit+1):
        for b in range(limit+1):
            for x, y in partners(a,b,table):
                if normalized_input(limit,a,b,x,y,primitive):
                    yield a, b, x, y


def direct_box(limit, primitive):
    for a in range(1,limit+1):
        for b in range(limit+1):
            for x in range(1,a):
                for y in range(-limit,limit+1):
                    if not normalized_input(limit,a,b,x,y,primitive):
                        continue
                    n, t = x*x+y*y, (a-x)**2+(b-y)**2
                    if a*n*t == (a*a+b*b)*(x*t+(a-x)*n):
                        yield a, b, x, y


def check():
    table = NormTable(2000)
    for m in range(1, 101):
        actual = list(table.circle(m))
        expected = {(u,v) for u in range(-isqrt(m**3),isqrt(m**3)+1)
                    for t in [m**3-u*u] for v in {isqrt(t),-isqrt(t)} if v*v == t}
        assert len(actual) == len(expected) and set(actual) == expected
    for primitive in (False, True):
        arr = list(box(32, primitive))
        assert len(arr) == len(set(arr)) and set(arr) == set(direct_box(32, primitive))
    assert (1,-8) in set(partners(16, 2, table))
    print("Circle checks for M = 1..100 and exhaustive box checks at N = 32 passed.")


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("N", type=int, nargs="?", default=50)
    parser.add_argument("--all", action="store_true", help="include imprimitive triads")
    parser.add_argument("--list", action="store_true", help="print each (a,b,x,y)")
    parser.add_argument("--check", action="store_true", help="run exact independent comparisons")
    args = parser.parse_args()
    if args.N < 1:
        parser.error("N must be positive")
    if args.check:
        check()
    else:
        count = 0
        for triad in box(args.N, not args.all):
            count += 1
            if args.list:
                print(*triad)
        print("Triads:", count)
