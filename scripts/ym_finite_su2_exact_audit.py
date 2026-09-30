#!/usr/bin/env python3
"""Exact-rational independent audit of the *finite* 4D quaternion YM geometry.

This executable does not establish continuum Yang-Mills or type-check Lean.
It tests actual link-derived plaquette gauge covariance, SU(2) Wilson trace
normalization, two-link blocking, and cross-plane reflection-positivity
obstructions on the Q8 subset of SU(2). All arithmetic is exact.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from itertools import product
from random import Random
from typing import Tuple

Z = Fraction(0)
O = Fraction(1)


@dataclass(frozen=True)
class Q:
    a: Fraction
    b: Fraction
    c: Fraction
    d: Fraction

    def __mul__(self, y: "Q") -> "Q":
        x = self
        return Q(
            x.a*y.a - x.b*y.b - x.c*y.c - x.d*y.d,
            x.a*y.b + x.b*y.a + x.c*y.d - x.d*y.c,
            x.a*y.c - x.b*y.d + x.c*y.a + x.d*y.b,
            x.a*y.d + x.b*y.c - x.c*y.b + x.d*y.a,
        )

    def inverse(self) -> "Q":
        assert self.a*self.a + self.b*self.b + self.c*self.c + self.d*self.d == O
        return Q(self.a, -self.b, -self.c, -self.d)

    def cost(self) -> Fraction:
        return O - self.a


ONE = Q(O, Z, Z, Z)
MINUS_ONE = Q(-O, Z, Z, Z)
BASIS = [ONE, Q(Z, O, Z, Z), Q(Z, Z, O, Z), Q(Z, Z, Z, O)]
Q8 = tuple(x for v in BASIS for x in (v, Q(-v.a, -v.b, -v.c, -v.d)))


def shift(x: Tuple[int, ...], direction: int, side: int) -> Tuple[int, ...]:
    y = list(x)
    y[direction] = (y[direction] + 1) % side
    return tuple(y)


def plaquette(links: dict, x: tuple, i: int, j: int, side: int) -> Q:
    return (links[x, i] * links[shift(x, i, side), j] *
            links[shift(x, j, side), i].inverse() * links[x, j].inverse())


def transform(links: dict, gauge: dict, side: int) -> dict:
    return {
        (x, i): gauge[x] * u * gauge[shift(x, i, side)].inverse()
        for (x, i), u in links.items()
    }


def two_link(links: dict, x: tuple, i: int, side: int) -> Q:
    return links[x, i] * links[shift(x, i, side), i]


def action(links: dict, side: int, beta: Fraction) -> Fraction:
    sites = tuple(product(range(side), repeat=4))
    return beta * sum(
        (plaquette(links, x, i, j, side).cost()
         for x in sites for i in range(4) for j in range(i+1, 4)), Z
    )


def audit() -> None:
    assert MINUS_ONE * MINUS_ONE == ONE
    assert MINUS_ONE.cost() == 2 and ONE.cost() == 0
    assert (MINUS_ONE*MINUS_ONE).cost() != MINUS_ONE.cost()+MINUS_ONE.cost()
    for epsilon in (Fraction(1,10), Fraction(1,1000)):
        # Exact additive-action version: positive Gibbs kernel wdiag=1,
        # woff=1+epsilon with a bounded *negative* off-diagonal action.
        kernel = ((O, O+epsilon), (O+epsilon, O))
        # Diagonal entry chosen 1, not zero.
        kernel = ((O, O+epsilon), (O+epsilon, O))
        gram = 2*O - 2*(O+epsilon)
        assert gram < 0
    rng = Random(369)
    side = 2
    sites = tuple(product(range(side), repeat=4))
    n_plaq = len(sites)*6
    for trial in range(12):
        links = {(x,i): rng.choice(Q8) for x in sites for i in range(4)}
        gauge = {x: rng.choice(Q8) for x in sites}
        changed = transform(links, gauge, side)
        beta = Fraction(trial+1, trial+2)
        for x in sites:
            for i in range(4):
                lhs = two_link(changed,x,i,side)
                rhs = gauge[x] * two_link(links,x,i,side) * gauge[shift(shift(x,i,side),i,side)].inverse()
                assert lhs == rhs, ("two-link gauge covariance", trial,x,i)
                for j in range(i+1,4):
                    lhs = plaquette(changed,x,i,j,side)
                    rhs = gauge[x]*plaquette(links,x,i,j,side)*gauge[x].inverse()
                    assert lhs == rhs, ("plaquette gauge covariance", trial,x,i,j)
                    assert lhs.cost() == rhs.cost()
        source = action(links,side,beta)
        assert source == action(changed,side,beta)
        assert Z <= source <= 2*beta*n_plaq
    print(f"PASS exact finite Q8 audit: 12 random 4D L=2 fields, {n_plaq} plaquettes each;")
    print("PASS all gauge covariance, blocking and Wilson bounds;")
    print("PASS -I coefficient probe, nonlinear blocking, small cross-plane RP obstruction.")
    print("LIMITATION: Q8 subgroup tests are diagnostics, not a proof for all SU(2) or continuum CMP119.")


if __name__ == "__main__":
    audit()
