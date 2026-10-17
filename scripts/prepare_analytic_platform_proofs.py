"""Export actual norm bridges and the analytic cyclic upper bound to Prove2Me.

All local helper proofs are embedded. Platform imports are limited to the
original public definitions; no open theorem is imported.
"""
import hashlib,json,re
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
OUT=ROOT/'formalization/platform'
SOURCE='Yuxuan Xu, A computer-assisted sharp diagonal Hlawka inequality for real exponents p >= 21, v1 (2026), https://github.com/Anchen-AI4Math/hlawka-diagonal-certificates/blob/main/paper/main.pdf . '

def read(name):return (ROOT/f'formalization/Hlawka21/{name}.lean').read_text(encoding='utf-8')
def bundle(names,extra=''):
    imports=[];bodies=[]
    for name in names:
        code=read(name)
        for line in code.splitlines():
            if line.startswith(('import Mathlib.','import Definitions.')) and line not in imports:imports.append(line)
        body='\n'.join(line for line in code.splitlines() if not line.startswith(('import ','#print axioms ')))
        bodies.append(body)
    preamble='\n'.join(imports)+'\nopen HlawkaSchatten.DiagonalConstruction\n'
    return preamble,preamble+'\n'+extra+'\n'+'\n'.join(bodies)+'\n'

payloads=json.loads((OUT/'payloads.json').read_text(encoding='utf-8'))
keys={'cyclic_upper21','coarse_oriented21','coarse_oriented26','envelope_linear21','envelope_linear26'}
payloads=[p for p in payloads if p['key'] not in keys]
name='HlawkaSchatten.DiagonalCutoff21.cyclicConstant_upper21'
statement=f'''theorem {name} {{p : ℝ}} (hp : 21 ≤ p) (hp32 : p ≤ 32) :
    cyclicConstant p ≤ p/2 := by sorry'''
preamble,solution=bundle(['Tail','CyclicUpper'])
solution+=statement.replace('theorem '+name,'theorem solution').replace(' := by sorry',' := by\n  exact '+name+' hp hp32')+'\n\n#print axioms solution\n'
file='Sol_cyclic_upper21.lean';(OUT/file).write_text(solution,encoding='utf-8')
payloads.append(dict(key='cyclic_upper21',theorem_name=name,theorem_title='Cyclic Hlawka constant at most p/2 throughout [21,32]',
    formal_statement=statement,preamble=preamble,
    natural_language_statement=r'''Let $p$ be any real exponent with $21\le p\le32$. Define

$$A_p(t)=(t^p+2)^{1/p},\qquad B_p(t)=(2|1-t|^p+2^p)^{1/p},$$
$$R_p(t)=\frac{3A_p(t)-3^{1/p}|2-t|}{6A_p(t)-3B_p(t)},\qquad K_p=\sup_{1/2\le t\le2}R_p(t).$$

Then $K_p\le p/2$. The exponent ranges over the entire real interval. This is the upper-bound component of both scalar-window milestones in the source paper.''',
    source=SOURCE+'Section 2, equation (7), upper-bound component; elementary analytic proof in formalization/Hlawka21/CyclicUpper.lean.',
    tags=['hlawka-schatten','real-analysis','cyclic-constant'],solution_file='formalization/platform/'+file,
    explanation='Put a=3^(1/p) and b=2^(1/p). Logarithm and exponential bounds give a>=1+1/p, a<=3, 1+.69/p+.69^2/(2p^2)<=b<=1+1/p. Bernoulli and the proved two-tail estimate give Bp(t)<=2+10^-5. Since Ap(t)>=max(b,t), the quantity 2(p-1)Ap(t)+(2/3)a(2-t) is at least 2p+10^-3 for p>=21. On p<=32 this dominates p Bp(t). The denominator is positive from Ap(t)>=1+1/64, so rearranging proves Rp(t)<=p/2, and taking the supremum closes the result. The complete file proves all helpers and imports no open theorem.'))

for cutoff in [21,26]:
    code=read(f'CoarseConnection{cutoff}')
    start=code.index(f'theorem coarse_box{cutoff}_oriented')
    end=code.index(' := by',start)
    helper=f'HlawkaSchatten.DiagonalCutoff21.coarse_box{cutoff}_oriented'
    name=helper+'_bounds'
    statement=code[start:end].replace(f'theorem coarse_box{cutoff}_oriented','theorem '+name)
    statement=statement.replace('(X : Triple)','(X : Fin 3 → Fin 3 → ℝ)')
    boxline=statement.splitlines()[-1]
    profile=json.loads((ROOT/f'profiles/cutoff{cutoff}.json').read_text())
    box=profile['coarse_box']
    # The exported statement uses ordinary functions and coordinates only.
    from generate_coarse_lean import rat
    ell,u,v,w=[rat(box[k]) for k in ['diag_min','diag_max','off_min','off_max']]
    statement=statement[:statement.rindex(boxline)]+f'    (∀ i, -{u} ≤ X i i ∧ X i i ≤ -{ell}) ∧\n    (∀ j i, j ≠ i → {v} ≤ X j i ∧ X j i ≤ {w}) := by sorry'
    extra='''namespace HlawkaSchatten.DiagonalCutoff21
def coordinateBox (ell u v w : ℝ) (X : Fin 3 → Fin 3 → ℝ) : Prop :=
  ∀ j i, if j = i then -u ≤ X j i ∧ X j i ≤ -ell
    else v ≤ X j i ∧ X j i ≤ w
end HlawkaSchatten.DiagonalCutoff21
'''
    preamble,solution=bundle(['ContractionCore','NormBasic','NormGeometry','Tail',f'Coarse{cutoff}',f'CoarseConnection{cutoff}'],extra)
    solution+=statement.replace('theorem '+name,'theorem solution').replace(' := by sorry',
        ' := by\n  have h := '+helper+' p hp X N P T hNdef hP0 hP1 hP2 hTdef hS hNT hT1 hTcap hmain0 hmain1 hmain2 hfail\n  constructor\n  · intro i; simpa [HlawkaSchatten.DiagonalCutoff21.coordinateBox] using h i i\n  · intro j i hji; simpa [HlawkaSchatten.DiagonalCutoff21.coordinateBox, hji] using h j i')+'\n\n#print axioms solution\n'
    file=f'Sol_coarse_oriented{cutoff}.lean';(OUT/file).write_text(solution,encoding='utf-8')
    k0=str(__import__('fractions').Fraction(profile['c'])*cutoff)
    payloads.append(dict(key=f'coarse_oriented{cutoff}',theorem_name=name,
        theorem_title=f'Cutoff {cutoff}: coarse localization from oriented normalized norm data',
        formal_statement=statement,preamble=preamble,
        natural_language_statement=rf'''Let $p\ge{cutoff}$ be real, and let $X_0,X_1,X_2\in\mathbb R^3$. Write $N_i=\|X_i\|_p$, $T=\|X_0+X_1+X_2\|_p$ and $P_i=\|X_j+X_k\|_p$, where $\{{i,j,k\}}=\{{0,1,2\}}$. Put $A=3({profile['q']})$, $e={profile['orientation_loss']}$ and $k_0={k0}$.

Assume $\sum_iN_i=3$, $N_i\le T$, $1\le T\le A$, and $P_i-X_{{ji}}-X_{{ki}}\le e$ for every complementary pair. Assume also $T-k_0\sum_iP_i\le3-6k_0$.

Then

$$-{box['diag_max']}\le X_{{ii}}\le-{box['diag_min']},\qquad {box['off_min']}\le X_{{ji}}\le{box['off_max']}\quad(j\ne i).$$

This is the complete two-stage coarse localization implication in Section 3 of the paper, starting from actual coordinate norms. Orientation and normalization are explicit hypotheses; a pre-established coarse box or successful numerical-check predicate is not assumed.''',
        source=SOURCE+f'Section 3, equations (10)-(11), parameters for Window {"I" if cutoff==21 else "II"}. The source LP and pair half-tail estimate are both proved in the submitted file.',
        tags=['hlawka-schatten','localization','lp-norm'],solution_file='formalization/platform/'+file,
        explanation='Coordinate bounds and pair triangle inequalities supply every premise of the first exact LP stage. Its eighteen conclusions show that each non-main pair coordinate is at most half the nonnegative main coordinate, which is at most three. The actual p-norm half-tail theorem then proves P_i<=L_i+10^-5, including L_i=0. These three inequalities supply the extra premises of the second exact LP stage, yielding the requested coordinate box. All norm laws, rational linear proofs and the real-exponent tail proof are included, with attribution to the accepted cutoff32 implementation for reused generic norm lemmas.'))

for cutoff,c,q in [(21,'273/625','1011/2500'),(26,'443/1000','197/500')]:
    name=f'HlawkaSchatten.DiagonalCutoff21.envelope_linear{cutoff}'
    statement=f'''theorem {name} {{p : ℝ}} (hp : {cutoff} ≤ p) :
    scalarEnvelope p ({q} : ℝ) < ({c} : ℝ)*p := by sorry'''
    preamble,solution=bundle(['Tail','Envelope'])
    solution+=statement.replace('theorem '+name,'theorem solution').replace(' := by sorry',' := by\n  exact '+name+' hp')+'\n\n#print axioms solution\n'
    file=f'Sol_envelope_linear{cutoff}.lean';(OUT/file).write_text(solution,encoding='utf-8')
    payloads.append(dict(key=f'envelope_linear{cutoff}',theorem_name=name,
        theorem_title=f'Envelope strictly below the linear threshold for all real p >= {cutoff}',
        formal_statement=statement,preamble=preamble,
        natural_language_statement=rf'''For any real $p\ge{cutoff}$, define

$$E_p(q)=\frac{{1-q}}{{2(1-((1+q^p)/2)^{{1/p}})}}.$$

At $q={q}$ and $c={c}$ one has $E_p(q)<cp$. The assertion includes all real exponents above the endpoint, without an upper endpoint restriction. Together with the source paper's cyclic lower bound $cp<K_p$, it implies the required envelope comparison.''',
        source=SOURCE+'Section 2, equation (7), envelope comparison parameters in Table 1. This stronger linear comparison is proved by a rational endpoint certificate and Bernoulli scaling in formalization/Hlawka21/Envelope.lean.',
        tags=['hlawka-schatten','real-analysis','bernoulli-inequality'],solution_file='formalization/platform/'+file,
        explanation='Let m be the endpoint and d=(1-q)/(2c). An exact rational integer-power computation gives (1+q^m)/2<(1-d/m)^m. Since 0<=q<1, q^p<=q^m for every real p>=m. Bernoulli applied with exponent p/m proves (1-d/m)^m<=(1-d/p)^p. Taking positive p-th roots yields ((1+q^p)/2)^(1/p)<1-d/p. Its denominator is positive, so rearranging gives E_p(q)<cp. All endpoint computations and scaling steps are proved in the submitted Lean file.'))

for item in payloads:
    data=(ROOT/item['solution_file']).read_bytes()
    assert b'sorry' not in data and b'axiom ' not in data
    item['solution_sha256']=hashlib.sha256(data).hexdigest()
(OUT/'payloads.json').write_text(json.dumps(payloads,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
print('Prepared',len(payloads),'complete auxiliary proof files.')
