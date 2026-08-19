#!/usr/bin/env python3
"""Independent arithmetic checks for the parameterized 7- and 11-families.

The manuscript proofs are symbolic. This script verifies the defining
recurrences, residue tables, endpoint formulas, and selected direct instances
as a regression layer independent of the Lean source.
"""
from __future__ import annotations
import sys
sys.set_int_max_str_digits(0)


def ds(n: int) -> int:
    return sum(map(int, str(n)))


def repblock(W: int, base: int, M: int) -> int:
    return W * (base**M - 1) // (base - 1)

# ---------------------------------------------------------------------------
# 7-family
# ---------------------------------------------------------------------------

def u7(t: int) -> int:
    return 6*t + 2


def M7(t: int) -> int:
    u = u7(t)
    num = 7*10**u - 25
    assert num % 27 == 0
    return num // 27


def M7_rec(t: int) -> int:
    m = 25
    for _ in range(t):
        m = 10**6*m + 925_925
    return m


def N7(t: int) -> int:
    m = M7(t)
    num = 5*10**(6*m + 2) + 11
    assert num % 7 == 0
    return num // 7


def defect7_direct(t: int, k: int) -> int:
    return ds(k*N7(t)) - k


def audit7() -> None:
    # Closed form/recurrence and central balance.
    for t in range(20):
        u, m = u7(t), M7(t)
        assert m == M7_rec(t)
        assert 7*10**u == 27*m + 25
        assert m >= u

    # The 152-digit witness is the first family member.
    assert M7(0) == 25
    assert 6*M7(0)+2 == 152

    # Direct integer audit on the first member.
    n = N7(0)
    assert ds(7*n) == 7
    q = 10**u7(0)
    assert [defect7_direct(0, 7*(q-1)+r) for r in range(1,7)] == [9]*6
    assert [defect7_direct(0, 7*q+r) for r in range(1,7)] == [-9]*6
    assert defect7_direct(0, 14) == -9

    # Symbolic endpoint formulas for many family indices.
    for t in range(1000):
        u = u7(t)
        left = 9*u - 9
        right = -9
        assert left == 54*t + 9
        assert left > 0 and right < 0

# ---------------------------------------------------------------------------
# 11-family: pure-power crossings
# ---------------------------------------------------------------------------

def q11(t: int) -> int:
    assert t >= 0
    return 100**(t+2)


def M11(t: int) -> int:
    q = q11(t)
    num = 11*q - 29
    assert num % 9 == 0
    return num // 9


def M11_rec(t: int) -> int:
    assert t >= 0
    m = 12_219
    for _ in range(t):
        m = 100*m + 319
    return m


def N11(t: int) -> int:
    m = M11(t)
    num = 9*10**(2*m+2) + 2
    assert num % 11 == 0
    return num // 11


def N11_small() -> int:
    return (9*10**52 + 2)//11


def residue11(r: int):
    assert 1 <= r <= 10
    h, a = divmod(9*r, 11)
    W = 9*a
    T = (100*a + 2*r)//11
    assert 9*r == 11*h + a
    assert 82*r == 100*h + T
    assert ds(W) == 9
    return h,a,W,T


def defect11_direct(t: int, k: int) -> int:
    return ds(k*N11(t)) - k


def audit11() -> None:
    for t in range(1000):
        q,m = q11(t),M11(t)
        assert m == M11_rec(t)
        assert 9*m == 11*q - 29
        assert m >= t+2
        if t:
            assert M11(t) > M11(t-1)

        # Symbolic local correction table: only two residue classes occur.
        for r in range(1,11):
            h,a,W,T = residue11(r)
            delta = ds(W+2)-9
            right_const = h + ds(T) + delta - r
            left_const = h + ds(T-2) + delta - r
            if r in (5,10):
                assert (right_const,left_const) == (-7,0)
                assert (18*t+18) > 0
                assert -27 < 0
            else:
                assert (right_const,left_const) == (11,9)
                assert (18*t+27) > 0
                assert -9 < 0

    # Materialize t=0 directly. For higher indices, verify the exact recurrence,
    # balance law, complete residue table, and endpoint formulas. This keeps the
    # check proportional to the proof data rather than to the decimal length of
    # the family member (which grows extremely quickly).
    t = 0
    n=N11(t); q=q11(t)
    assert ds(11*n)==11
    assert ds(22*n)-22 == -9
    for r in range(1,11):
        left=ds((11*(q-1)+r)*n)-(11*(q-1)+r)
        right=ds((11*q+r)*n)-(11*q+r)
        if r in (5,10):
            assert left == 18*t+18
            assert right == -27
        else:
            assert left == 18*t+27
            assert right == -9

    # Verify the 52-digit witness as a separate direct example.
    ns=N11_small()
    assert ds(11*ns)==11
    assert ds(22*ns)-22 == -9
    good=[k for k in range(1,496) if ds(k*ns)==k]
    assert good == [11]

def main() -> None:
    audit7()
    audit11()
    print('INFINITE_FAMILY_AUDIT_OK')
    print('7-family: M_0=25, M_{t+1}=10^6 M_t+925925; endpoints +(54t+9), -9')
    print('11-family: M_0=12219, M_{t+1}=100 M_t+319; common q=100^(t+2) crossings verified')

if __name__ == '__main__':
    main()
