"""Exact auxiliary checks using only Python standard-library rational arithmetic."""
import json
from fractions import Fraction as F
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]

def row(a,b,strict=False):return (list(map(F,a)),F(b),strict)
BASE=[row([1,1,1,1],F(5,6)),row([-1,-1,-1,-1],F(-5,6))]
for i in range(3):
    a=[0]*4;a[i]=-1;a[i+1]=1;BASE.append(row(a,0))
BASE.append(row([0,0,0,-1],0,True))
for k in range(1,4):
    a=[0]*4;a[0]=-k;a[k]=-(4-k);BASE.append(row(a,-1,True))

def branch(axis,cap,closed,left):
    a=[0]*4;a[axis]=1 if left else -1
    return row(a,F(cap) if left else -F(cap),not closed if left else closed)

def valid_certificate(rows,cert):
    a=[F(0)]*4;b=F(0);strict=False
    for j,v in cert:
        q=F(v)
        if q<0:return False
        for i in range(4):a[i]+=q*rows[j][0][i]
        b+=q*rows[j][1];strict|=q>0 and rows[j][2]
    return all(x==0 for x in a) and (b<0 or (b==0 and strict))

def verify(data):
    nodes=data['nodes'];seen=set()
    def visit(k,rows):
        assert k not in seen;seen.add(k);n=nodes[k]
        if n['kind']=='empty':assert valid_certificate(rows,n['certificate'])
        elif n['kind']=='box':
            b=data['boxes'][n['box']]
            for axis,(cap,closed) in enumerate(zip(b['caps'],b['closed'])):
                assert valid_certificate(rows+[branch(axis,cap,closed,False)],n['certificates'][axis])
        else:
            for left in (True,False):
                visit(n['left' if left else 'right'],rows+[branch(n['axis'],n['cap'],n['closed'],left)])
    visit(data['root'],BASE);assert len(seen)==len(nodes)


def verify_words(boxes):
    for box in boxes:
        w=box['word']; P=len(w)
        assert P>0 and all(i in range(4) for i in w)
        for i,(cap,closed) in enumerate(zip(box['caps'],box['closed'])):
            b=F(cap);assert b>0 and P*b<=w.count(i)
            for m in range(P):
                for L in range(P):
                    count=sum(w[(m+j)%P]==i for j in range(L))
                    assert L*b<count+1 if closed else L*b<=count+1
if __name__=='__main__':
    data=json.loads((ROOT/'results/pinwheel-rational-certificate.json').read_text())
    verify(data);verify_words(data['boxes'])
    print('Exact rational cover and all 47 periodic word certificates passed.')
