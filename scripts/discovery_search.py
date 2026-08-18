#!/usr/bin/env python3
"""Reproduce the restricted sparse-template discovery of the compact witnesses.

This script is deliberately NOT a proof component.  It searches candidates

    N = (A*10^L + B) / p

with one nonzero leading digit A, a two-digit-or-shorter tail B, and
s(A)+s(B)=p.  It then performs a heuristic finite Good-multiplier scan.
The output explains how the compact 52- and 152-digit candidates can be found
without claiming global minimality or exhausting all integers n.
"""
from __future__ import annotations
import sys
sys.set_int_max_str_digits(0)


def ds(n: int) -> int:
    return sum(map(int, str(n)))


def good_list(n: int, bound: int) -> list[int]:
    return [k for k in range(1, bound + 1) if ds(k*n) == k]


def first_sparse_hit(p: int, max_L: int, scan_bound: int):
    tails = [(A,B) for A in range(1,10) for B in range(1,100)
             if ds(A)+ds(B)==p]
    for L in range(1,max_L+1):
        tenL=10**L
        for A,B in tails:
            num=A*tenL+B
            if num % p:
                continue
            n=num//p
            goods=good_list(n,scan_bound)
            if goods and max(goods)==p:
                return dict(p=p,L=L,A=A,B=B,n=n,goods=goods,
                            scan_bound=scan_bound)
    return None


def main() -> None:
    configs=[(11,60,500),(7,160,1500)]
    for p,maxL,bound in configs:
        hit=first_sparse_hit(p,maxL,bound)
        if hit is None:
            raise SystemExit(f'no hit found for p={p}')
        print(f"p={p}: first hit in the restricted sparse template/search order")
        print(f"  L={hit['L']}, A={hit['A']}, B={hit['B']}, scan_bound={bound}")
        print(f"  Good multipliers found: {hit['goods']}")
        print(f"  N has {len(str(hit['n']))} decimal digits")
    print('DISCOVERY_SEARCH_OK')


if __name__ == '__main__':
    main()
