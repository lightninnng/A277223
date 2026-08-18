from itertools import combinations, permutations
from math import gcd

FORBIDDEN = {1,2,3,4,5,6,8,10}


def ds(n:int)->int:
    return sum(map(int,str(n)))


def good(n:int,k:int)->bool:
    return ds(n*k)==k


def rep(block:int,width:int,count:int)->int:
    return sum(block*10**(width*i) for i in range(count))


def n7()->int:
    return 73 + 10**2 * rep(714285,6,25)


def n11()->int:
    return 82 + 10**2 * rep(81,2,25)


def digit_partitions(total:int, max_digit:int=9):
    """Unordered nonzero decimal digit multisets of prescribed digit mass."""
    out=[]
    def rec(rem:int, cap:int, prefix:list[int]):
        if rem == 0:
            out.append(tuple(prefix))
            return
        for d in range(min(cap,max_digit,rem),0,-1):
            rec(rem-d,d,prefix+[d])
    rec(total,max_digit,[])
    return out


def digit_at(n:int,u:int)->int:
    return (n//10**u)%10


def profile_max(c:int, parts:list[int], width:int=3)->int:
    best=0
    for r in range(1,min(len(parts),width)+1):
        for inds in combinations(range(len(parts)),r):
            for offs in permutations(range(width),r):
                best=max(best,sum(digit_at(c*parts[i],u) for i,u in zip(inds,offs)))
    return best



def has_adjacent_motif(config:list[tuple[int,int]], motif:str)->bool:
    """Whether a high-to-low decimal motif occurs in a labeled digit configuration."""
    target=[int(ch) for ch in motif]
    L=len(target)
    for inds in permutations(range(len(config)),L):
        if any(config[inds[j]][0] != target[j] for j in range(L)):
            continue
        exps=[config[i][1] for i in inds]
        if all(exps[j] == exps[0]-j for j in range(L)):
            return True
    return False


def audit_primary_motifs(parts:list[int], c:int, target:int, motifs:list[str], radius:int=8)->int:
    """
    Independent finite-local audit of the first-carry motif classification.

    Translation is normalized by requiring the lowest occupied exponent to be 0.
    The radius exceeds every product-profile width used in the paper.  Locality
    proves that larger gaps cannot introduce a new first carry; this routine is
    therefore an audit of the explicit motif table, not a search over integers.
    """
    checked=0
    for exps in permutations(range(radius+1),len(parts)):
        if min(exps) != 0:
            continue
        config=list(zip(parts,exps))
        m=sum(d*10**e for d,e in config)
        failed=(ds(c*m) != target)
        expected=any(has_adjacent_motif(config,motif) for motif in motifs)
        assert failed == expected, (parts,c,target,motifs,config,c*m,ds(c*m),failed,expected)
        checked += 1
    return checked

def shifted_sum(A:int,B:int,d:int)->int:
    if d>=0:
        return A+B*10**d
    return A*10**(-d)+B


def periodic_data(p,Q,A,B,C,d,M,t,r,q):
    h=(r*A)//p
    a=r*A-p*h
    T=r*C-h*10**t
    W=a*Q
    H=A*q+h
    L=W*10**t+B*q+T
    value=ds(L)+(M-1)*ds(W)+ds(H)
    return dict(h=h,a=a,T=T,W=W,H=H,L=L,digitsum=value,delta=value-(p*q+r))


def audit():
    N7=n7(); N11=n11()
    assert 7*N7 == 5*10**152+11
    assert 11*N11 == 9*10**52+2
    assert ds(7*N7)==7
    assert ds(11*N11)==11

    # Exhaustive digit-partition coverage.  This guards against accidentally
    # omitting a decimal digit multiset from the human Carry-Obstruction proof.
    p5=set(digit_partitions(5)); p6=set(digit_partitions(6))
    assert {p for p in p5 if max(p) >= 5} == {(5,)}
    assert {p for p in p6 if max(p) >= 5} == {(6,), (5,1)}

    p8=set(digit_partitions(8))
    expected8={(8,), (7,1), (6,2), (6,1,1), (5,3), (5,2,1), (5,1,1,1)}
    assert {p for p in p8 if max(p) >= 5} == expected8

    p10=set(digit_partitions(10))
    multi_high10={p for p in p10 if sum(1 for d in p if d >= 5) >= 2}
    assert multi_high10 == {(5,5)}
    one_high10={p for p in p10 if sum(1 for d in p if d >= 5) == 1}

    # Profile-safe families for the k=10 carry obstruction.
    families = [
        (12,[9,1]),
        (13,[8,2]),(13,[8,1,1]),
        (15,[7,3]),(15,[7,2,1]),(15,[6,4]),(15,[6,2,2]),
        (21,[7,1,1,1]),(21,[6,1,1,1,1]),(21,[5,2,2,1]),
        (21,[5,2,1,1,1]),(21,[5,1,1,1,1,1]),
        (22,[6,3,1]),(22,[6,2,1,1]),(22,[5,3,1,1]),
    ]
    safe10={tuple(parts) for _,parts in families}
    exceptional10={(5,4,1),(5,3,2)}
    assert one_high10 == safe10 | exceptional10
    assert safe10.isdisjoint(exceptional10)

    profile_rows=[]
    for c,parts in families:
        score=sum(ds(c*x) for x in parts)
        pm=profile_max(c,parts)
        assert score==c and pm<=9
        profile_rows.append((c,parts,score,pm))

    # Exact primary first-carry motifs used in the paper.  These checks use a
    # translation-normalized local window wider than all relevant product
    # profiles.  By the first-carry locality theorem, more distant gaps are
    # separated and cannot create new motifs.
    primary_specs=[
        ([6,1,1],25,20,['16']),
        ([5,3],25,20,['53']),
        ([5,2,1],25,20,['52','12']),
        ([5,1,1,1],45,36,['115']),
        ([5,4,1],21,21,['54','145']),
        ([5,3,2],21,21,['53']),
    ]
    primary_counts=[]
    for parts,c,target,motifs in primary_specs:
        primary_counts.append((parts,c,target,motifs,audit_primary_motifs(parts,c,target,motifs)))

    # Exact two-block obstruction locations used in the paper.
    local = {}
    tests=[
        ('8:52 secondary',2125*52,2125,{2}),
        ('8:12 secondary',2250*12,2250*5,{2}),
        ('8:115 secondary',375*115,375,{-1,3}),
        ('10:54 secondary',24*54,24,set()),
        ('10:53 secondary',24*53,24*2,{2}),
    ]
    excluded={
        '8:52 secondary':{0,1},
        '8:12 secondary':{0,1},
        '8:115 secondary':{0,1,2},
        '10:54 secondary':{0,1},
        '10:53 secondary':{0,1},
    }
    expected_sum={
        '8:52 secondary':17,
        '8:12 secondary':18,
        '8:115 secondary':30,
        '10:54 secondary':24,
        '10:53 secondary':24,
    }
    for name,A,B,bad_expected in tests:
        bad=[]
        for dlt in range(-12,13):
            if dlt in excluded[name]:
                continue
            if ds(shifted_sum(A,B,dlt)) != expected_sum[name]:
                bad.append(dlt)
        assert set(bad)==bad_expected,(name,bad)
        local[name]=bad

    # Fallback leaf arithmetic.
    leaves={
        '8:152':(125,152,10),
        '8:512':(125,512,10),
        '8:1151':(1750,1151,14),
        '8:1115':(2750,1115,22),
        '8:53':(2125,53,17),
        '10:145':(12,145,12),
        '10:253':(12,253,12),
    }
    for name,(c,m,j) in leaves.items():
        assert ds(c*m)==j,(name,c*m,ds(c*m))

    # Broad exact checks of the periodic normal form throughout the ranges
    # needed before/at the crossings, not merely at the two displayed endpoints.
    periodic_exact_checks=0
    for r in range(1,7):
        for q in range(0,101):
            a=periodic_data(7,142857,5,11,73,6,25,2,r,q)
            assert a['L'] < 10**8
            assert a['digitsum'] == ds((7*q+r)*N7)
            periodic_exact_checks += 1
    for r in range(1,11):
        for q in range(0,24):
            a=periodic_data(11,9,9,2,82,2,25,2,r,q)
            assert a['L'] < 10**4
            assert a['digitsum'] == ds((11*q+r)*N11)
            periodic_exact_checks += 1

    # N7: one uniform crossing for all nonzero residues.
    cross7=[]
    for r in range(1,7):
        a=periodic_data(7,142857,5,11,73,6,25,2,r,99)
        b=periodic_data(7,142857,5,11,73,6,25,2,r,100)
        assert a['delta']==9 and b['delta']==-9
        assert a['digitsum']==ds((7*99+r)*N7)
        assert b['digitsum']==ds((7*100+r)*N7)
        cross7.append((r,a['delta'],b['delta'],a['W'],a['T']))
    assert ds(14*N7)-14==-9

    # N11: two crossing indices, exactly as in the proof.
    cross11=[]
    for r in range(1,11):
        q=22 if r in (1,2) else 21
        a=periodic_data(11,9,9,2,82,2,25,2,r,q)
        b=periodic_data(11,9,9,2,82,2,25,2,r,q+1)
        assert a['delta']>0 and b['delta']<0
        assert a['digitsum']==ds((11*q+r)*N11)
        assert b['digitsum']==ds((11*(q+1)+r)*N11)
        cross11.append((r,q,a['delta'],b['delta'],a['W'],a['T']))
    assert ds(22*N11)-22==-9

    # Independent sanity scan: every Good forbidden small multiplier observed
    # in a large finite range has a larger Good witness from the paper's pool.
    guards={
        1:[2], 2:[4], 3:[6], 4:[8], 5:[9,10], 6:[9,12,15],
        8:[9,10,12,14,16,17,18,20,22,30,36],
        10:[12,13,15,20,21,22,24],
    }
    checked=0
    for n in range(1,200_001):
        for k in FORBIDDEN:
            if good(n,k):
                checked+=1
                assert any(j>k and good(n,j) for j in guards[k]),(n,k)

    print('digit partition coverage:', {
        'mass5': len(p5), 'mass6': len(p6), 'mass8': len(p8), 'mass10': len(p10),
        'mass8-high': len(expected8), 'mass10-one-high': len(one_high10)})
    print('periodic normal-form exact checks:', periodic_exact_checks)
    print('N7 digits:',len(str(N7)))
    print('N11 digits:',len(str(N11)))
    print('profile rows:',profile_rows)
    print('primary motif audits:',primary_counts)
    print('local obstruction offsets:',local)
    print('N7 crossings:',cross7)
    print('N11 crossings:',cross11)
    print('finite sanity Good cases checked:',checked)
    print('AUDIT_OK')

if __name__=='__main__':
    audit()
