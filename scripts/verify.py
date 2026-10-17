"""Replay certificates with Arb or dyadic intervals, plus rational LP duals.

No scipy, optimizer output or stored numeric margin is trusted.
This checks numerical obligations, not the entire mathematical reduction.
"""
import argparse, json, hashlib
from pathlib import Path
from fractions import Fraction as F
from coarse_lp import model,add,scale,X,P,DIM

def require(condition,message):
    if not condition: raise ValueError(message)

LO=F(127,4); HI=F(32); C=F('0.448'); QC=F('.3854')
def partition(cells,lo,hi):
    pos=lo
    for a,b in cells:
        require(a==pos and b>a,'gap, overlap or inverted interval')
        pos=b
    require(pos==hi,'coverage endpoint mismatch')
def positive(x,label): require(x>0,label)
def le(x,y,label): require(x<=y,label)
def power_cert(x,y,b,label):
    require(0<=x<=1 and 0<=y<=1,label+' base range')
    positive(Q(x)**Q(b)+Q(y)**Q(b)-1,label)
def ratios(r,n,tlo,D,b):
    s,tau,sigma=map(F,(r['s'],r['tau'],r['sigma']))
    require(F(r['n'])==n,'round does not use preceding n')
    require(n>0 and D>=0,'ratio prerequisites')
    le(s,2*tlo-D/n,'s bound'); le(2*tau,s,'tau branch'); le(s,2*sigma,'sigma branch')
    require(s>=1 and tau>=0 and sigma>=0,'ratio domain')
    power_cert(tau,s-tau,b,'ratio lower')
    power_cert(sigma,s-sigma,b,'ratio upper')
    return tau,sigma

def verify(root,precision=192,backend='arb'):
    global Q,I,ratio,envelope
    if backend=='arb':
        from intervals import Q,I,ratio,envelope,ctx
        ctx.prec=precision
    elif backend=='rational':
        from rational_intervals import Q,I,ratio,envelope,configure
        configure(precision)
    else: raise ValueError('unknown arithmetic backend')
    load=lambda name:json.loads((root/name).read_text())
    scalar=load('scalar.json'); upper=load('cyclic-upper.json'); slabs=load('contractor.json'); coarse=load('coarse.json')
    partition([(F(s['a']),F(s['b'])) for s in scalar],LO,HI)
    margins=[]
    for s in scalar:
        a,b,t=map(F,(s['a'],s['b'],s['t']))
        require(F(1,2)<=t<=2,'cyclic witness outside domain')
        p=I(a,b); r=ratio(p,Q(t)); e=envelope(p,Q(QC))
        require(r is not None and e is not None,'scalar denominator')
        positive(r-e,'scalar envelope'); positive(r-Q(C)*p,'linear lower')
        margins.append(float((r-e).lower()))
    partition([(F(s['a']),F(s['b'])) for s in upper],LO,HI)
    for s in upper:
        p=I(F(s['a']),F(s['b']))
        cells=[tuple(map(F,row)) for row in s['t_cells']]
        partition(cells,F(1,2),F(2))
        for l,r in cells:
            val=ratio(p,I(l,r)); require(val is not None,'upper denominator')
            positive(p/2-val,'K <= p/2')
    # Numerical prerequisites for the analytic orientation and tail arguments.
    k0=C*LO; Tcap=3*QC; Gcap=2/k0; Nmin=3-2*Tcap
    positive(Q('.08')-2*Q(Tcap)*(1-Q(3)**(-1/Q(LO))),'pass-0 loss')
    require(Nmin>Gcap+F('.08'),'opposite signs conflict')
    require(3-2*Gcap-F('.16')>Tcap,'equal signs conflict')
    positive(Q('0.00001')-6*Q(F(1,2))**Q(LO)/Q(LO),'half-tail')
    positive(Q('1e-10')-6*Q(F(603,1580))**Q(LO)/Q(LO),'coarse-tail')
    positive(Q(2/C)-6*Q(2).log(),'residual monotonicity')
    require((F(coarse['p_min']),F(coarse['c']),F(coarse['q_cap']))==(LO,C,QC),'LP metadata')
    A,b,E,f=model()
    # Reconstruct expected objectives: never trust a certificate to select an easier target.
    expected=[]
    for i in range(3):
        js=[j for j in range(3) if j!=i]; large=add(*(X[j][i] for j in js))
        expected += [(large,F(0)),(scale(large,-1),F(-3))]
        for k in js:
            small=add(*(X[j][k] for j in js))
            for sign in [-1,1]: expected.append((add(scale(large,F(1,2)),scale(small,sign)),F(0)))
    coarse_slack=[]
    for stage,records in enumerate(coarse['stages']):
        require(len(records)==len(expected),'LP count')
        for cert,(c,target) in zip(records,expected):
            require(list(map(F,cert['objective']))==c and F(cert['target'])==target,'LP objective mismatch')
            y=list(map(F,cert['dual_ineq'])); z=list(map(F,cert['dual_eq']))
            require(len(y)==len(A) and len(z)==len(E) and all(v<=0 for v in y),'dual sign/dimension')
            require(all(sum(y[i]*A[i][j] for i in range(len(A)))+sum(z[i]*E[i][j] for i in range(len(E)))==c[j] for j in range(DIM)),'dual identity')
            lower=sum(v*w for v,w in zip(y,b))+sum(v*w for v,w in zip(z,f))
            require(lower>=target,'LP bound'); coarse_slack.append(float(lower-target))
        if stage==0:
            for i in range(3):
                js=[j for j in range(3) if j!=i]
                A.append(add(P[i],*(scale(X[j][i],-1) for j in js))); b.append(F(1,100000))
            expected=[]
            for j in range(3):
                for i in range(3):
                    low,high=(F('-1.158'),F('-.555')) if i==j else (F('.79'),F('1.158'))
                    expected += [(X[j][i],low),(scale(X[j][i],-1),-high)]
    require(len(coarse['stages'])==2,'LP stages')
    # Sequential contractor; powers tested at beta control all p in [alpha,beta].
    partition([(F(s['a']),F(s['b'])) for s in slabs],LO,HI)
    final_slacks=[]
    for slab in slabs:
        a,b,q,tlo,thia,thib,h,D,delta=[F(slab[k]) for k in ['a','b','q','tlo','thia','thib','h','D','delta']]
        require(q==QC and a>0 and tlo>0,'slab constants')
        positive(Q(F(1,2))**(1/Q(a))-Q(tlo),'root lower')
        positive(Q(thia)-Q(F(1,2))**(1/Q(a)),'root upper a')
        positive(Q(thib)-Q(F(1,2))**(1/Q(b)),'root upper b')
        le(2/(C*a)+F(3,10**10),h,'offsum budget')
        le(2/(C*a)+F(3,10**10)-6*(1-thia),D,'residual budget')
        require(D>=0 and delta>=0,'budget sign'); le(D/(2*tlo),delta,'delta budget')
        n=F('.79')
        for r in slab['rounds']:
            le(delta,n,'lower-round domain')
            tau,sigma=ratios(r,n,tlo,D,b)
            nn,Ab=F(r['next_n']),F(r['Ab'])
            require(0<nn<3 and Ab>=0,'lower-round endpoint')
            power_cert(Ab/nn,1-delta/nn,b,'lower norm certificate')
            le(3*q,tau*(3-nn)-Ab,'lower norm check')
            n=nn
        r=slab['final']; tau,sigma=ratios(r,n,tlo,D,b)
        U,B,Af=map(F,(r['U'],r['B'],r['Af']))
        le(delta,n,'upper-round domain'); require(0<U<3 and B>=0 and Af>=0,'upper endpoints')
        power_cert(B/(3-U),1-delta/(3-U),b,'upper norm certificate')
        le(2*thib*3*q,6-h-sigma*(3-U)-B,'upper norm check')
        power_cert(Af/U,1-delta/U,b,'diagonal cap')
        slacks=[tau*n-F('.849'),F('1.121')-sigma*U,F('1.065')-Af,tau*(3-U)-3*q-F('.625')]
        require(all(x>=0 for x in slacks),'final box')
        final_slacks.append(list(map(float,slacks)))
    # Fixed final box, geometry constants 9 and 4200 from the source proof.
    m,M=F('0.625'),F('1.121')
    tmin,tmax=F('0.633'),F('1.617')
    require((tmin*tmin+tmax*tmax)/(tmin+tmax)**2<=F(8,5)*m*m,'total pair shape')
    require(4*F(101,100)*M*M*F(202,125)<=9,'geometry D coefficient')
    require(4*F(101,100)*M*M*F(2424,5)+101*16<=4200,'geometry U coefficient')
    require(F('.625')/F('1.121')>=F(1,2) and F('1.065')/F('.849')<=2,'orbit parameter range')
    p=I(LO,HI)
    rT=Q(F(14553,4528))*Q(F(133672,179139))**(p-2)
    rC=Q(F(10089,4528))*Q(F(278008,530625))**(p-2)
    curvatureT=1-9*(p/2)*rT
    curvatureC=2*Q(C)-1/p-2100*rC
    positive(curvatureT,'total curvature'); positive(curvatureC,'column curvature')
    return dict(status='PASS',backend=backend,precision_bits=precision,p_interval=[str(LO),str(HI)],scalar_cells=len(scalar),upper_boxes=sum(len(s['t_cells']) for s in upper),contractor_slabs=len(slabs),lp_dual_certificates=sum(map(len,coarse['stages'])),geometry_constants_checked=True,min_envelope_margin_lower=min(margins),min_final_box_slacks=[min(v[i] for v in final_slacks) for i in range(4)],total_curvature_margin=str(curvatureT),column_curvature_margin=str(curvatureC),scope='Numerical obligations only; analytic reduction and source dependencies are not machine checked here.',sha256={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(root.glob('*.json'))})

if __name__=='__main__':
    parser=argparse.ArgumentParser(); parser.add_argument('--precision',type=int,default=192); parser.add_argument('--backend',choices=['arb','rational'],default='arb'); parser.add_argument('--directory',type=Path,default=Path('certificates')); parser.add_argument('--output',type=Path,default=Path('results/verification.json')); args=parser.parse_args()
    result=verify(args.directory,args.precision,args.backend)
    args.output.parent.mkdir(exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
