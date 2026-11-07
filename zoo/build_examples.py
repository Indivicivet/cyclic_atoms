"""Build reproducible exact 0A files, using CRT for coordinate-line constructions."""
from fractions import Fraction as F
from pathlib import Path
from math import prod
import json
D=Path(__file__).resolve().parent

def write(name, atoms):
    (D/name).write_text(json.dumps([[p,str(a)] for p,a in atoms],indent=2)+'\n')

def grid(primes, lines):
    L=prod(primes); result=[]
    for p, coords in lines:
        # Find the CRT position with the varying coordinate set to zero.
        x=sum(v*(L//m)*pow(L//m,-1,m) for m,v in zip(primes,coords)) % L
        result.append((p,F(x,L)))
    return result

def three(s,p,q):
    lines=[]
    for x in range(p):
        for y in range(q): lines.append((s,(0,x,y)))
    for u in range(s-1):
        for y in range(q): lines.append((p,(u,0,y)))
    for x in range(p): lines.append((q,(s-1,x,0)))
    return grid((s,p,q),lines)

def four(kind):
    s,p,q,r=3,5,7,11; lines=[]
    for x in range(p):
        for y in range(q):
            for z in range(r):lines.append((s,(0,x,y,z)))
    if kind=='product': modes=['p','q','r']
    elif kind=='mixed588': modes=['p','q','mix588']
    else: modes=['p','p','mix590']
    for u,mode in enumerate(modes):
        if mode=='p':
            for y in range(q):
                for z in range(r):lines.append((p,(u,0,y,z)))
        if mode=='q':
            for x in range(p):
                for z in range(r):lines.append((q,(u,x,0,z)))
        if mode=='r':
            for x in range(p):
                for y in range(q):lines.append((r,(u,x,y,0)))
        if mode=='mix588':
            for y in range(q-1):
                for z in range(r):lines.append((p,(u,0,y,z)))
            for x in range(p):lines.append((r,(u,x,q-1,0)))
        if mode=='mix590':
            for x in range(p-1):
                for z in range(r):lines.append((q,(u,x,0,z)))
            for y in range(q):lines.append((r,(u,p-1,y,0)))
    return grid((s,p,q,r),lines)

write('identical_twos.json',[(2,F(0)),(2,F(0))])
write('composite_224.json',[(2,F(0)),(2,F(1,4)),(4,F(0))])
write('two_and_five.json',[(5,F(0)),(5,F(1,10))]+[(2,F(i,10)) for i in range(5)])
write('23_max.json',three(2,3,5))
# Five copies of the four-atom 3-2-2-3 branch.
write('235_ten.json',[(5,F(0)),(5,F(1,2))]+[(p,a) for p,a in [(3,F(0)),(3,F(1,2)),(2,F(1,3)),(2,F(2,3))]]+[(2,F(k,5)) for k in range(1,5)])
write('235_branches.json',[(5,F(0)),(5,F(1,2))]+[(p,F(k,5)+a) for k in range(5) for p,a in [(3,F(0)),(3,F(1,2)),(2,F(1,3)),(2,F(2,3))]])
write('3711_max.json',three(3,7,11))
for kind in ('product','mixed588','max590'):write('35711_'+kind+'.json',four(kind))
