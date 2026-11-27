#!/usr/bin/env python3
"""Reproduce the integer Laguerre certificate using only Python's standard library."""
from functools import cache
from math import comb
from pathlib import Path


@cache
def factor(h):
    """258^h times (B_h(x), x B'_h(x), x^2 B''_h(x)) at x = -1/258."""
    value = first = second = 0
    n = h + 1
    for j in range(n):
        coefficient, remainder = divmod(comb(n, j) * comb(n, j + 1), n)
        assert remainder == 0
        term = (-1)**j * 258**(h - j) * coefficient
        value += term
        first += j * term
        second += j * (j - 1) * term
    return value, first, second


def add_product(accumulator, left, right):
    """Accumulate ordinary first and second derivatives by the product rule."""
    a, b, c = left
    u, v, w = right
    accumulator[0] += a * u
    accumulator[1] += b * u + a * v
    accumulator[2] += c * u + 2 * b * v + a * w


def scaled_derivatives():
    row = [(1, 0, 0)]
    for count, base, mass in [(10, 1, 23), (96, 30, 1)]:
        for _ in range(count):
            update = [[0, 0, 0] for _ in range(len(row) + mass)]
            for previous_mass, triple in enumerate(row):
                for s in range(mass + 1):
                    add_product(update[previous_mass + s], triple, factor(base - 1 + mass - s))
            row = update
    assert len(row) == 327
    result = [0, 0, 0]
    for s, triple in enumerate(row):
        add_product(result, triple, factor(s))
    return tuple(result)


def main():
    a, b, c = scaled_derivatives()
    stored = Path(__file__).with_name("certificate.txt").read_text().splitlines()
    assert stored == [f"{key} = {value:#x}" for key, value in zip("ABC", (a, b, c))]
    gap = a * c - b**2
    assert a != 0
    quotient, remainder = divmod(gap, a**2)
    assert quotient == 12223800 and 0 < remainder < a**2
    print("leaf counts = 10, 96; largest center allocation = 326")
    print("normalized degree = 3110; x = -1/258")
    print("A is nonzero; A*C - B^2 is positive")
    print("floor((A*C - B^2)/A^2) =", quotient)
    print("The quotient is strictly between 12223800 and 12223801.")
    print("All three signed integers match certificate.txt.")


if __name__ == "__main__":
    main()
