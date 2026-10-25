"""Exact integer-polynomial source check for Yan–Radulescu (2021) p. 998.

Original paper: Weiping Yan and Vicentiu D. Radulescu,
DOI 10.1007/s12215-020-00540-3, Corollary 1.1.
This checks sampled integer p,q,T instances of the source-written g formula.
It does not prove a universal theorem or reproduce a steady NS solution.
"""


def clean(poly):
    a = list(poly)
    while len(a) > 1 and a[-1] == 0:
        a.pop()
    return tuple(a)


def add(a, b):
    return clean(tuple(
        (a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0)
        for i in range(max(len(a), len(b)))
    ))


def neg(a):
    return tuple(-c for c in a)


def mul(a, b):
    out = [0] * (len(a) + len(b) - 1)
    for i, ai in enumerate(a):
        for j, bj in enumerate(b):
            out[i + j] += ai * bj
    return clean(out)


def power(a, n):
    out = (1,)
    for _ in range(n):
        out = mul(out, a)
    return out


def deriv(a):
    return clean(tuple(i * a[i] for i in range(1, len(a))) or (0,))


def polynomial_seed(p, q, T):
    y, z = (0, 1), (-T, 1)
    yz = mul(y, z)
    h = power(yz, q)
    rho = power(yz, 2 * (p + 1))
    # Source p. 998: g = (yz)^(q-1) (2y-T) [q - 2(p+1) rho].
    g = mul(
        mul(power(yz, q - 1), (-T, 2)),
        add((q,), neg(tuple(2 * (p + 1) * c for c in rho))),
    )
    return h, rho, g


def run():
    n = 0
    for p in range(2, 7):
        for q in range(3, 10):
            for T in (1, 2, 3):
                h, rho, g = polynomial_seed(p, q, T)
                expected = add(deriv(h), neg(mul(h, deriv(rho))))
                assert expected == g, (p, q, T, expected, g)
                assert h[0] == g[0] == 0, (p, q, T)
                assert sum(h[i] * T ** i for i in range(len(h))) == 0
                assert sum(g[i] * T ** i for i in range(len(g))) == 0
                n += 1
    print(
        f"PASS: {n} exact integer-polynomial parameter instances of "
        "g=h'-h*rho' and endpoint zeros"
    )
    return n


if __name__ == "__main__":
    run()
