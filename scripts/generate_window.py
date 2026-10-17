"""Untrusted parameterized search; every output must be replayed by verify.py."""
import argparse,json,math
from pathlib import Path
from fractions import Fraction as F
from scipy.optimize import brentq
from scout import optimum
from generate import rounded,upper_tree
from intervals import Q,I,ratio,envelope
from coarse_lp import generate as coarse_generate

def make_slab(a,b,c,q,coarse_tail,n0,round_count):
    af,bf=float(a),float(b)
    tlo=rounded(2**(-1/af)); thia=rounded(2**(-1/af),True); thib=rounded(2**(-1/bf),True)
    h=2/(c*a)+3*coarse_tail
    D=h-6*(1-thia); delta=rounded(float(D/(2*tlo)),True)
    def diag(N): return N*(-math.expm1(bf*math.log1p(-float(delta)/N)))**(1/bf)
    def ratios(n):
        s=rounded(float(2*tlo-D/n))
        r=brentq(lambda x:x**bf+(float(s)-x)**bf-1,float(s)-1,float(s)/2,xtol=1e-14)
        return s,rounded(r-1e-8),rounded(float(s)-r+1e-8,True)
    n=n0; rounds=[]
    for _ in range(round_count):
        s,tau,sigma=ratios(n)
        root=brentq(lambda N:float(tau)*(3-N)-diag(N)-3*float(q),float(n0),1.1,xtol=1e-14)
        nn=rounded(root-1e-7); Ab=rounded(diag(float(nn))+1e-9,True)
        rounds.append({k:str(v) for k,v in dict(n=n,s=s,tau=tau,sigma=sigma,next_n=nn,Ab=Ab).items()})
        n=nn
    s,tau,sigma=ratios(n)
    root=brentq(lambda U:6-float(h)-float(sigma)*(3-U)-diag(3-U)-2*float(thib)*3*float(q),1,1.4,xtol=1e-14)
    U=rounded(root+1e-7,True); B=rounded(diag(3-float(U))+1e-9,True); Af=rounded(diag(float(U))+1e-9,True)
    def box_round(x,up=False):
        numerator=x.numerator*10000; denominator=x.denominator
        return F(-((-numerator)//denominator) if up else numerator//denominator,10000)
    box=dict(diag_min=box_round(tau*(3-U)-3*q),diag_max=box_round(Af,True),
             off_min=box_round(tau*n),off_max=box_round(sigma*U,True))
    final={k:str(v) for k,v in dict(n=n,s=s,tau=tau,sigma=sigma,U=U,B=B,Af=Af).items()}
    final['box']={k:str(v) for k,v in box.items()}
    return {**{k:str(v) for k,v in dict(a=a,b=b,q=q,tlo=tlo,thia=thia,thib=thib,h=h,D=D,delta=delta).items()},'rounds':rounds,'final':final}

def scalar_tree(a,b,c,q):
    t=rounded(optimum(float((a+b)/2))[0])
    p=I(a,b); r=ratio(p,Q(t)); e=envelope(p,Q(q))
    if r is not None and e is not None and r-e>0 and r-Q(c)*p>0:
        return [dict(a=str(a),b=str(b),t=str(t))]
    if b-a<F(1,10**8): raise RuntimeError('scalar not certified')
    m=(a+b)/2
    return scalar_tree(a,m,c,q)+scalar_tree(m,b,c,q)

def generate(profile,out):
    lo,hi,c,q,step,loss,half_tail,coarse_tail=[F(profile[k]) for k in
        ['p_min','p_max','c','q','slab_width','orientation_loss','half_tail','coarse_tail']]
    box={k:F(v) for k,v in profile['coarse_box'].items()}
    out.mkdir(parents=True,exist_ok=True)
    def save(name,data): (out/name).write_text(json.dumps(data,indent=2)+'\n')
    coarse=coarse_generate(lo,c,q,loss,box,half_tail); save('coarse.json',coarse)
    slabs=[]; a=lo
    while a<hi:
        b=min(hi,a+step)
        slabs.append(make_slab(a,b,c,q,coarse_tail,box['off_min'],profile['rounds'])); a=b
    save('contractor.json',slabs); print('contractor slabs:',len(slabs),flush=True)
    scalars=scalar_tree(lo,hi,c,q); save('scalar.json',scalars); print('scalar cells:',len(scalars),flush=True)
    upper=[]
    for s in slabs:
        a,b=F(s['a']),F(s['b'])
        cells=upper_tree(a,b,F(1,2),F(1))+upper_tree(a,b,F(1),F(2))
        upper.append(dict(a=str(a),b=str(b),t_cells=cells))
    save('cyclic-upper.json',upper); print('upper boxes:',sum(len(s['t_cells']) for s in upper),flush=True)

if __name__=='__main__':
    parser=argparse.ArgumentParser(); parser.add_argument('--profile',type=Path,required=True); parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args(); generate(json.loads(args.profile.read_text()),args.output)
