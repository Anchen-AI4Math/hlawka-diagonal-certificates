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

def verify(root,precision=192,backend='arb',profile=None):
    global Q,I,ratio,envelope
    if backend=='arb':
        from intervals import Q,I,ratio,envelope,ctx
        ctx.prec=precision
    elif backend=='rational':
        from rational_intervals import Q,I,ratio,envelope,configure
        configure(precision)
    else: raise ValueError('unknown arithmetic backend')
    lo,hi,c,q=LO,HI,C,QC
    loss,half_tail,coarse_tail=F('.08'),F('1e-5'),F('1e-10')
    coarse_box=dict(diag_min=F('.555'),diag_max=F('1.158'),off_min=F('.79'),off_max=F('1.158'))
    if profile is not None:
        require(profile['geometry'] in ['norm_caps','pair_caps'],'unknown geometry')
        lo,hi,c,q=[F(profile[k]) for k in ['p_min','p_max','c','q']]
        loss,half_tail,coarse_tail=[F(profile[k]) for k in ['orientation_loss','half_tail','coarse_tail']]
        coarse_box={k:F(v) for k,v in profile['coarse_box'].items()}
    require(2<lo<hi and c>0 and F(1,3)<q<F(1,2),'profile domain')
    require(loss>0 and half_tail>0 and coarse_tail>0,'profile errors')
    al0,ah0,bl0,bh0=[coarse_box[k] for k in ['diag_min','diag_max','off_min','off_max']]
    require(0<al0<=ah0 and 0<bl0<=bh0,'coarse box domain')
    load=lambda name:json.loads((root/name).read_text())
    scalar=load('scalar.json'); upper=load('cyclic-upper.json'); slabs=load('contractor.json'); coarse=load('coarse.json')
    partition([(F(s['a']),F(s['b'])) for s in scalar],lo,hi)
    margins=[]
    for s in scalar:
        a,b,t=map(F,(s['a'],s['b'],s['t']))
        require(F(1,2)<=t<=2,'cyclic witness outside domain')
        p=I(a,b); r=ratio(p,Q(t)); e=envelope(p,Q(q))
        require(r is not None and e is not None,'scalar denominator')
        positive(r-e,'scalar envelope'); positive(r-Q(c)*p,'linear lower')
        margins.append(float((r-e).lower()))
    partition([(F(s['a']),F(s['b'])) for s in upper],lo,hi)
    for s in upper:
        p=I(F(s['a']),F(s['b']))
        cells=[tuple(map(F,row)) for row in s['t_cells']]
        partition(cells,F(1,2),F(2))
        for l,r in cells:
            val=ratio(p,I(l,r)); require(val is not None,'upper denominator')
            positive(p/2-val,'K <= p/2')
    # Numerical prerequisites for the analytic orientation and tail arguments.
    k0=c*lo; Tcap=3*q; Gcap=2/k0; Nmin=3-2*Tcap
    positive(Q(loss)-2*Q(Tcap)*(1-Q(3)**(-1/Q(lo))),'pass-0 loss')
    require(Nmin>Gcap+loss,'opposite signs conflict')
    require(3-2*Gcap-2*loss>Tcap,'equal signs conflict')
    positive(Q(half_tail)-6*Q(F(1,2))**Q(lo)/Q(lo),'half-tail')
    if profile is not None and profile['geometry']=='pair_caps':
        from geometry import capped_tail
        tail_ratio=capped_tail(coarse_box,Tcap)/(2*bl0)
    else:
        tail_ratio=max(abs(bl0-ah0),abs(bh0-al0))/(2*bl0)
    require(0<tail_ratio<1,'coarse tail ratio')
    positive(Q(coarse_tail)-6*Q(tail_ratio)**Q(lo)/Q(lo),'coarse-tail')
    positive(Q(2/c)-6*Q(2).log(),'residual monotonicity')
    require((F(coarse['p_min']),F(coarse['c']),F(coarse['q_cap']))==(lo,c,q),'LP metadata')
    A,b,E,f=model(lo,c,q,loss)
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
        for cert,(objective,target) in zip(records,expected):
            require(list(map(F,cert['objective']))==objective and F(cert['target'])==target,'LP objective mismatch')
            y=list(map(F,cert['dual_ineq'])); z=list(map(F,cert['dual_eq']))
            require(len(y)==len(A) and len(z)==len(E) and all(v<=0 for v in y),'dual sign/dimension')
            require(all(sum(y[i]*A[i][j] for i in range(len(A)))+sum(z[i]*E[i][j] for i in range(len(E)))==objective[j] for j in range(DIM)),'dual identity')
            lower=sum(v*w for v,w in zip(y,b))+sum(v*w for v,w in zip(z,f))
            require(lower>=target,'LP bound'); coarse_slack.append(float(lower-target))
        if stage==0:
            for i in range(3):
                js=[j for j in range(3) if j!=i]
                A.append(add(P[i],*(scale(X[j][i],-1) for j in js))); b.append(half_tail)
            expected=[]
            for j in range(3):
                for i in range(3):
                    low,high=(-ah0,-al0) if i==j else (bl0,bh0)
                    expected += [(X[j][i],low),(scale(X[j][i],-1),-high)]
    require(len(coarse['stages'])==2,'LP stages')
    # Sequential contractor; powers tested at beta control all p in [alpha,beta].
    partition([(F(s['a']),F(s['b'])) for s in slabs],lo,hi)
    final_slacks=[]; curvature_rows=[]
    for slab in slabs:
        a,b,slab_q,tlo,thia,thib,h,D,delta=[F(slab[k]) for k in ['a','b','q','tlo','thia','thib','h','D','delta']]
        require(slab_q==q and a>0 and tlo>0,'slab constants')
        positive(Q(F(1,2))**(1/Q(a))-Q(tlo),'root lower')
        positive(Q(thia)-Q(F(1,2))**(1/Q(a)),'root upper a')
        positive(Q(thib)-Q(F(1,2))**(1/Q(b)),'root upper b')
        le(2/(c*a)+3*coarse_tail,h,'offsum budget')
        le(2/(c*a)+3*coarse_tail-6*(1-thia),D,'residual budget')
        require(D>=0 and delta>=0,'budget sign'); le(D/(2*tlo),delta,'delta budget')
        n=bl0
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
        box=r['box'] if profile is not None else dict(diag_min='.625',diag_max='1.065',off_min='.849',off_max='1.121')
        al,ah,bl,bh=[F(box[k]) for k in ['diag_min','diag_max','off_min','off_max']]
        slacks=[tau*n-bl,bh-sigma*U,ah-Af,tau*(3-U)-3*q-al]
        require(all(x>=0 for x in slacks),'final box')
        final_slacks.append(list(map(float,slacks)))
        if profile is not None:
            from geometry import constants,pair_cap_constants
            if profile['geometry']=='pair_caps':
                # These are consequences of S=3 at the counterexample, then
                # retained as linear constraints on the convex averaging domain.
                pair_floor=3-U-2/(c*a)-coarse_tail
                offsum_floor=6-h
                g=pair_cap_constants(box,Tcap,U,F(profile['young_epsilon_1']),F(profile['young_epsilon_2']),pair_floor,offsum_floor)
            else:
                g=constants(box,Tcap,U,F(profile['young_epsilon_1']),F(profile['young_epsilon_2']))
            p=I(a,b)
            rT=Q(g['rT_factor'])*Q(g['rT_base'])**(p-2)
            rC=Q(g['rC_factor'])*Q(g['rC_base'])**(p-2)
            mt=1-Q(g['gT'])*(p/2)*rT
            mc=2*Q(c)-1/p-Q(g['gC'])*rC/2
            positive(mt,'norm-cap total curvature'); positive(mc,'norm-cap column curvature')
            curvature_rows.append(dict(a=str(a),b=str(b),total=str(mt),column=str(mc),
                total_lower=float(mt.lower()),column_lower=float(mc.lower()),
                constants={k:str(v) for k,v in g.items()}))
    if profile is not None:
        return dict(status='PASS',backend=backend,precision_bits=precision,profile=profile,p_interval=[str(lo),str(hi)],
            scalar_cells=len(scalar),upper_boxes=sum(len(s['t_cells']) for s in upper),contractor_slabs=len(slabs),
            lp_dual_certificates=sum(map(len,coarse['stages'])),geometry_constants_checked=True,
            min_envelope_margin_lower=min(margins),min_final_box_slacks=[min(v[i] for v in final_slacks) for i in range(4)],
            min_total_curvature_margin_lower=min(r['total_lower'] for r in curvature_rows),
            min_column_curvature_margin_lower=min(r['column_lower'] for r in curvature_rows),curvature=curvature_rows,
            scope='Finite numerical obligations; analytical convex-domain arguments are documented separately.',
            sha256={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(root.glob('*.json'))})
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
    parser=argparse.ArgumentParser(); parser.add_argument('--precision',type=int,default=192); parser.add_argument('--backend',choices=['arb','rational'],default='arb'); parser.add_argument('--directory',type=Path,default=Path('certificates')); parser.add_argument('--profile',type=Path); parser.add_argument('--output',type=Path,default=Path('results/verification.json')); args=parser.parse_args()
    profile=json.loads(args.profile.read_text()) if args.profile else None
    result=verify(args.directory,args.precision,args.backend,profile)
    args.output.parent.mkdir(exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='curvature'},indent=2))
