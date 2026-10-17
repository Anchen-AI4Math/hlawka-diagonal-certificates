"""Generate rational dual witnesses for coarse localization; no float is trusted."""
from fractions import Fraction as F
import json
from pathlib import Path

DIM=16
def unit(i):
    v=[F(0)]*DIM; v[i]=F(1); return v
def add(*vs): return [sum(x) for x in zip(*vs)]
def scale(v,s): return [F(s)*x for x in v]
X=[[unit(3*j+i) for i in range(3)] for j in range(3)]
N=[unit(9+j) for j in range(3)]
P=[unit(12+i) for i in range(3)] # pair excluding i
T=unit(15)
def model(pmin=F('31.75'),c=F('.448'),q=F('.3854'),loss=F('.08')):
    A=[]; b=[]
    def le(v,r): A.append(v); b.append(F(r))
    for n in N:
        le(scale(n,-1),0); le(add(n,scale(T,-1)),0)
    le(scale(T,-1),-1); le(T,3*q)
    for j in range(3):
        for i in range(3):
            for s in [-1,1]: le(add(scale(X[j][i],s),scale(N[j],-1)),0)
    for i in range(3):
        total=add(*(X[j][i] for j in range(3)))
        for s in [-1,1]: le(add(scale(total,s),scale(T,-1)),0)
        js=[j for j in range(3) if j!=i]
        le(scale(P[i],-1),0)
        le(add(P[i],*(scale(N[j],-1) for j in js)),0)
        le(add(P[i],*(scale(X[j][i],-1) for j in js)),loss)
    k0=c*pmin
    le(add(T,*(scale(v,-k0) for v in P)),3-6*k0)
    return A,b,[add(*N)],[F(3)]

def dual(c,A,b,E,f):
    import numpy as np
    from scipy.optimize import linprog
    res=linprog(np.array(c,dtype=float),A_ub=np.array(A,dtype=float),b_ub=np.array(b,dtype=float),A_eq=np.array(E,dtype=float),b_eq=np.array(f,dtype=float),bounds=[(None,None)]*DIM,method='highs')
    if not res.success: raise RuntimeError(res.message)
    y=[F(float(x)).limit_denominator(10**9) for x in res.ineqlin.marginals]
    z=[F(float(x)).limit_denominator(10**9) for x in res.eqlin.marginals]
    assert all(v<=0 for v in y)
    assert all(sum(y[i]*A[i][j] for i in range(len(A)))+sum(z[i]*E[i][j] for i in range(len(E)))==c[j] for j in range(DIM))
    lower=sum(v*w for v,w in zip(y,b))+sum(v*w for v,w in zip(z,f))
    return dict(objective=list(map(str,c)),dual_ineq=list(map(str,y)),dual_eq=list(map(str,z)),lower=str(lower))

def generate(pmin=F('31.75'),c=F('.448'),q=F('.3854'),loss=F('.08'),box=None,half_tail=F('1e-5')):
    A,b,E,f=model(pmin,c,q,loss); stages=[]
    if box is None: box=dict(diag_min=F('.555'),diag_max=F('1.158'),off_min=F('.79'),off_max=F('1.158'))
    # Each pass-0 dominant coordinate is positive, <= 3, and its other coordinates <= half.
    tests=[]
    for i in range(3):
        js=[j for j in range(3) if j!=i]
        large=add(*(X[j][i] for j in js))
        tests += [(f'positive_{i}',large,F(0)),(f'upper3_{i}',scale(large,-1),F(-3))]
        for k in js:
            small=add(*(X[j][k] for j in js))
            for sign in [-1,1]: tests.append((f'half_{i}_{k}_{sign}',add(scale(large,F(1,2)),scale(small,sign)),F(0)))
    records=[]
    for name,objective,target in tests:
        cert=dual(objective,A,b,E,f); assert F(cert['lower'])>=target,(name,cert['lower'])
        records.append(dict(name=name,target=str(target),**cert))
    stages.append(records)
    # The certified half-tail estimate permits these new linear premises.
    for i in range(3):
        js=[j for j in range(3) if j!=i]
        A.append(add(P[i],*(scale(X[j][i],-1) for j in js))); b.append(half_tail)
    records=[]
    for j in range(3):
        for i in range(3):
            low,high=(-box['diag_max'],-box['diag_min']) if i==j else (box['off_min'],box['off_max'])
            for name,objective,target in [(f'lo_{j}_{i}',X[j][i],low),(f'hi_{j}_{i}',scale(X[j][i],-1),-high)]:
                cert=dual(objective,A,b,E,f)
                print(name,float(F(cert['lower'])),float(target))
                assert F(cert['lower'])>=target,(name,cert['lower'],target)
                records.append(dict(name=name,target=str(target),**cert))
    stages.append(records)
    return dict(p_min=str(pmin),c=str(c),q_cap=str(q),stages=stages)

if __name__=='__main__':
    Path('certificates').mkdir(exist_ok=True)
    Path('certificates/coarse.json').write_text(json.dumps(generate(),indent=2)+'\n')
