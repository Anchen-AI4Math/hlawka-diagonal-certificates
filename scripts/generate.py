"""Untrusted numerical search creates a rational schedule; verify.py checks it."""
from fractions import Fraction as F
from pathlib import Path
import json, math
from scipy.optimize import brentq
from scout import optimum
from intervals import Q,I,ratio,envelope

def rounded(v,up=False):
    return F((math.ceil if up else math.floor)(v*10**9),10**9)
def make_slab(a,b):
    af,bf=float(a),float(b); c=.448; q=.3854
    tlo=rounded(2**(-1/af)); thia=rounded(2**(-1/af),True); thib=rounded(2**(-1/bf),True)
    h=F(2)/(F('0.448')*a)+F(3,10**10)
    D=h-6*(1-thia); delta=rounded(float(D/(2*tlo)),True)
    def diag(N): return N*(-math.expm1(bf*math.log1p(-float(delta)/N)))**(1/bf)
    def ratios(n):
        s=rounded(float(2*tlo-D/n))
        r=brentq(lambda x:x**bf+(float(s)-x)**bf-1,float(s)-1,float(s)/2,xtol=1e-14)
        return s,rounded(r-1e-8),rounded(float(s)-r+1e-8,True)
    n=F('.79'); rounds=[]
    for _ in range(6):
        s,tau,sigma=ratios(n)
        root=brentq(lambda N:float(tau)*(3-N)-diag(N)-3*q,.79,1,xtol=1e-14)
        nn=rounded(root-1e-7)
        Ab=rounded(diag(float(nn))+1e-9,True)
        rounds.append(dict(n=str(n),s=str(s),tau=str(tau),sigma=str(sigma),next_n=str(nn),Ab=str(Ab)))
        n=nn
    s,tau,sigma=ratios(n)
    root=brentq(lambda U:6-float(h)-float(sigma)*(3-U)-diag(3-U)-2*float(thib)*3*q,1,1.3,xtol=1e-14)
    U=rounded(root+1e-7,True); B=rounded(diag(3-float(U))+1e-9,True); Af=rounded(diag(float(U))+1e-9,True)
    return {**{k:str(v) for k,v in dict(a=a,b=b,q=F('.3854'),tlo=tlo,thia=thia,thib=thib,h=h,D=D,delta=delta).items()},'rounds':rounds,'final':{k:str(v) for k,v in dict(n=n,s=s,tau=tau,sigma=sigma,U=U,B=B,Af=Af).items()}}

def scalar_tree(a,b):
    t=rounded(optimum(float((a+b)/2))[0])
    p=I(a,b); r=ratio(p,Q(t)); e=envelope(p,Q('.3854'))
    if r is not None and e is not None and r-e>0 and r-Q('.448')*p>0:
        return [dict(a=str(a),b=str(b),t=str(t))]
    if b-a<F(1,10**8): raise RuntimeError('scalar not certified')
    m=(a+b)/2
    return scalar_tree(a,m)+scalar_tree(m,b)

def upper_tree(a,b,l,r):
    p=I(a,b); v=ratio(p,I(l,r))
    if v is not None and p/2-v>0: return [[str(l),str(r)]]
    if r-l<F(1,10**7): raise RuntimeError('upper not certified')
    m=(l+r)/2
    return upper_tree(a,b,l,m)+upper_tree(a,b,m,r)

if __name__=='__main__':
    out=Path('certificates'); out.mkdir(exist_ok=True)
    slabs=[make_slab(F(127,4)+F(i,64),F(127,4)+F(i+1,64)) for i in range(16)]
    (out/'contractor.json').write_text(json.dumps(slabs,indent=2)+'\n')
    print('contractor slabs:',len(slabs),flush=True)
    scalars=scalar_tree(F(127,4),F(32))
    (out/'scalar.json').write_text(json.dumps(scalars,indent=2)+'\n')
    print('scalar cells:',len(scalars),flush=True)
    upper=[]
    for s in slabs:
        a,b=F(s['a']),F(s['b'])
        leaves=upper_tree(a,b,F(1,2),F(1))+upper_tree(a,b,F(1),F(2))
        upper.append(dict(a=str(a),b=str(b),t_cells=leaves))
    (out/'cyclic-upper.json').write_text(json.dumps(upper,indent=2)+'\n')
    print('upper boxes:',sum(len(x['t_cells']) for x in upper),flush=True)
