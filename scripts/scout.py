"""Floating point exploration only. Never a certificate."""
import json
from pathlib import Path
import numpy as np
from scipy.optimize import minimize_scalar, brentq

def ratio(p,t):
    a=np.exp(np.logaddexp(p*np.log(t),np.log(2))/p)
    b=2*np.exp(np.log1p(2*(abs(1-t)/2)**p)/p)
    return (3*a-3**(1/p)*(2-t))/(6*a-3*b)
def envelope(p,q):
    return (1-q)/(-2*np.expm1((np.log1p(q**p)-np.log(2))/p))
def optimum(p):
    r=minimize_scalar(lambda t:-ratio(p,t),bounds=(.5,1),method='bounded',options={'xatol':1e-14})
    return r.x, -r.fun
def contract(a,b,q,c=.448,rounds=8):
    tlo=2**(-1/a); thi=2**(-1/b)
    h=2/(c*a)+3e-10; D=h-6*(1-tlo); delta=D/(2*tlo)
    def diag(N): return N*(-np.expm1(b*np.log1p(-delta/N)))**(1/b)
    n=.79
    for _ in range(rounds):
        s=2*tlo-D/n
        tau=brentq(lambda x:x**b+(s-x)**b-1,s-1,s/2)
        sigma=s-tau
        n=brentq(lambda N:tau*(3-N)-diag(N)-3*q,.79,1)
    U=brentq(lambda U:6-h-sigma*(3-U)-diag(3-U)-2*thi*3*q,1,1.3)
    return dict(n=n,U=U,tau=tau,sigma=sigma,off_low=tau*n,off_high=sigma*U,diag_low=tau*(3-U)-3*q,diag_high=diag(U))
if __name__=='__main__':
    rows=[]
    for p in [16,20,24,26,28,29,30,31,32,33,40,50]:
        t,k=optimum(p)
        q=brentq(lambda q:envelope(p,q)-k,.30,.65)
        rows.append(dict(p=p,t=t,K_candidate=k,K_over_p=k/p,q_threshold=q))
    Path('results').mkdir(exist_ok=True)
    Path('results/scout.json').write_text(json.dumps(rows,indent=2)+'\n')
    for row in rows: print(row)
    for a in [31,31.5,31.75,31.9,32]:
        _,k=optimum(a); q=brentq(lambda q:envelope(a,q)-k,.3,.5)+.00002
        print('contract',a,q,contract(a,a+.01,q))
