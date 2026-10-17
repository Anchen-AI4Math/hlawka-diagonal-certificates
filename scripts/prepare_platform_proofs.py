"""Create exact platform problem and solution payloads from compiled sources.

No network or authentication. Publication is handled separately, after compilation.
"""
import json,re,hashlib
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
OUT=ROOT/'formalization/platform'
SOURCE='Yuxuan Xu, A computer-assisted sharp diagonal Hlawka inequality for real exponents p >= 21, v1 (2026), https://github.com/Anchen-AI4Math/hlawka-diagonal-certificates/blob/main/paper/main.pdf . '

def make():
    OUT.mkdir(parents=True,exist_ok=True)
    payloads=[]
    for cutoff in [21,26]:
        path=ROOT/f'formalization/Hlawka21/Coarse{cutoff}.lean'
        code=path.read_text(encoding='utf-8')
        preamble=code[:code.index('theorem ')]
        for stage in [0,1]:
            name=f'HlawkaSchatten.DiagonalCutoff21.coarse{cutoff}_stage{stage}'
            begin=code.index('theorem '+name)
            end=code.index('\n#print axioms ',begin)
            proved=code[begin:end].strip()
            statement=proved[:proved.index(' := by')]+ ' := by sorry'
            solution=preamble+proved.replace('theorem '+name,'theorem solution',1)+'\n\n#print axioms solution\n'
            label=f'coarse{cutoff}_stage{stage}'
            (OUT/f'Sol_{label}.lean').write_text(solution,encoding='utf-8')
            common=r'''Use the sixteen real coordinates $v_0,\ldots,v_{15}$ to encode $X_{ji}=v_{3j+i}$, $N_j=v_{9+j}$, $P_i=v_{12+i}$, and $T=v_{15}$, for $i,j\in\{0,1,2\}$. Let $L_i=\sum_{j\ne i}X_{ji}$. The hypotheses are exactly the normalized rational LP system in equation (10) of the source: singleton bounds, norm-coordinate bounds, total-coordinate bounds, nonnegative pair quantities, orientation loss, the failure inequality, and $N_0+N_1+N_2=3$. All LP parameters are exact rational numbers from the indicated profile. '''
            if stage==0:
                nl=common+r'''Then $0\le L_i\le3$ for each $i$, and $\left|\sum_{j\ne i}X_{jk}\right|\le L_i/2$ for each $k\ne i$. This is a linear implication for every assignment of the sixteen real variables; no numerical solver report is assumed.'''
            else:
                box=json.loads((ROOT/f'profiles/cutoff{cutoff}.json').read_text())['coarse_box']
                nl=common+rf'''Assume also the three improved pair-tail inequalities $P_i-L_i\le10^{{-5}}$. Then every diagonal coordinate satisfies $-{box['diag_max']}\le X_{{ii}}\le-{box['diag_min']}$, and every off-diagonal coordinate satisfies ${box['off_min']}\le X_{{ji}}\le {box['off_max']}$ for $j\ne i$. This is the second rational LP implication yielding the coarse box in equation (11).'''
            explanation=r'''The conclusion is a conjunction of eighteen linear inequalities. For each one, a rational dual witness selects at most twelve of the LP inequalities and the normalization equality. Multiplying and adding those inequalities gives the requested bound. The Lean proof reconstructs these exact rational linear implications with `linarith`; it uses no floating-point solver or external verification oracle.''' 
            payloads.append(dict(key=label,theorem_name=name,theorem_title=f'Cutoff {cutoff}: exact coarse LP implications, stage {stage}',formal_statement=statement,natural_language_statement=nl,preamble=preamble,source=SOURCE+f'Section 3, equations (10)-(11), Table 1, and Section 8 finite certificate lemma; certificates/cutoff{cutoff}/coarse.json, stage {stage}.',tags=['hlawka-schatten','linear-programming','exact-arithmetic'],solution_file=f'formalization/platform/Sol_{label}.lean',explanation=explanation))
    code=(ROOT/'formalization/Hlawka21/Residual.lean').read_text(encoding='utf-8')
    name='HlawkaSchatten.DiagonalCutoff21.residual_energy_bound_rounded'
    begin=code.index('theorem residual_energy_bound_rounded')
    end=code.index(' := by',begin)
    statement=code[begin:end].replace('theorem residual_energy_bound_rounded','theorem '+name)+' := by sorry'
    solution=code[:code.index('\n#print axioms')]
    # This file contains the complete helper proofs before the top-level solution.
    solution+='\n'+statement.replace('theorem '+name,'theorem solution').replace(' := by sorry',' := by\n  exact '+name+' rho S a b hrho hS ha hb')+'\n\n#print axioms solution\n'
    (OUT/'Sol_residual_energy.lean').write_text(solution,encoding='utf-8')
    imports=code[:code.index('/-')]
    payloads.append(dict(key='residual_energy',theorem_name=name,theorem_title='Rational perturbation bound for the pair Hessian residual',formal_statement=statement,natural_language_statement=r'''For any finite index type $\iota$, real numbers $\rho,S\ge0$, and real families $a_i,b_i$ indexed by $\iota$, suppose $\sum_i a_i^2\le3S$ and $\sum_i b_i^2\le4\rho^2 S$. Then $\sum_i(a_i-b_i)^2\le(7/4+2\rho)^2S$. The assertion includes the empty index type, zero residuals and $\rho=0$. It is the algebraic energy estimate used after the two operator bounds in the pair-residual argument.''',preamble=imports,source=SOURCE+'Section 6.2, equation (34). This helper isolates the finite-dimensional perturbation-energy estimate; its proof first obtains the slightly stronger coefficient 3+7*rho+4*rho^2.',tags=['hlawka-schatten','quadratic-forms','convexity'],solution_file='formalization/platform/Sol_residual_energy.lean',explanation=r'''For $\rho>0$, summing the nonnegative squares $(\rho a_i+b_i)^2$ gives $\rho\sum_i(a_i-b_i)^2\le\rho(1+\rho)\sum_i a_i^2+(1+\rho)\sum_i b_i^2$. The two energy bounds yield the coefficient $3+7\rho+4\rho^2$, which is at most $(7/4+2\rho)^2$. If $\rho=0$, the second energy bound forces every $b_i$ to vanish, and the first bound closes the argument. The Lean file proves all these steps without imported open theorems.'''))
    pair_code=(ROOT/'formalization/Hlawka21/PairResidual.lean').read_text(encoding='utf-8')
    pair_imports='\n'.join(line for line in pair_code.splitlines() if line.startswith('import Mathlib.'))+'\n'
    name='HlawkaSchatten.DiagonalCutoff21.matrix_pair_residual_bound_explicit'
    av='(![U 1 1 + U 2 1, U 1 2 + U 2 2, U 0 0 + U 2 0, U 0 2 + U 2 2, U 0 0 + U 1 0, U 0 1 + U 1 1] : Fin 6 → ℝ)'
    bv='(![U 1 0 + U 2 0, U 1 0 + U 2 0, U 0 1 + U 2 1, U 0 1 + U 2 1, U 0 2 + U 1 2, U 0 2 + U 1 2] : Fin 6 → ℝ)'
    statement=f'''theorem {name} (U : Fin 3 → Fin 3 → ℝ)
    (theta : Fin 6 → ℝ) (rho : ℝ) (hrho : 0 ≤ rho)
    (htheta : ∀ i, |theta i| ≤ rho) :
    ∑ i, ({av} i - theta i * {bv} i) ^ 2 ≤
      (7 / 4 + 2 * rho) ^ 2 * (∑ j, ∑ i, U j i ^ 2) := by sorry'''
    helpers=code[:code.index('\n#print axioms')]
    # Keep every import at the beginning; embed the complete proved helpers.
    pair_body='\n'.join(line for line in pair_code.splitlines() if not line.startswith('import '))
    pair_body=pair_body[:pair_body.index('\n#print axioms')]
    solution=imports+pair_imports+helpers[len(imports):]+'\n'+pair_body+'\n'
    solution+=statement.replace('theorem '+name,'theorem solution').replace(' := by sorry',
        ' := by\n  simpa only [HlawkaSchatten.DiagonalCutoff21.matrixEnergy, HlawkaSchatten.DiagonalCutoff21.pairDirect, HlawkaSchatten.DiagonalCutoff21.pairMain] using\n    HlawkaSchatten.DiagonalCutoff21.matrix_pair_residual_bound U theta rho hrho htheta')+'\n\n#print axioms solution\n'
    (OUT/'Sol_matrix_pair_residual.lean').write_text(solution,encoding='utf-8')
    payloads.append(dict(key='matrix_pair_residual',theorem_name=name,
        theorem_title='Six pair residuals controlled by the full matrix energy',
        formal_statement=statement,preamble=imports+pair_imports,
        natural_language_statement=r'''Let $U$ be any real $3\times3$ matrix, let $\rho\ge0$, and let six real coefficients $\theta_{ki}$ satisfy $|\theta_{ki}|\le\rho$, indexed by $k,i\in\{0,1,2\}$ with $i\ne k$. If $\{j,r,k\}=\{0,1,2\}$, set $e_{ki}=U_{ji}+U_{ri}-\theta_{ki}(U_{jk}+U_{rk})$. Then

$$\sum_{k=0}^2\sum_{i\ne k}e_{ki}^2\le(7/4+2\rho)^2\sum_{j=0}^2\sum_{i=0}^2 U_{ji}^2.$$

This controls the non-radial error in the pair Hessian bound. It requires no orthogonality condition on $U$.

**Formalization Note** The six coefficients and residuals are ordered as $(k,i)=(0,1),(0,2),(1,0),(1,2),(2,0),(2,1)$.''',
        source=SOURCE+'Section 6.2, equation (34), including the two operator estimates immediately preceding it.',
        tags=['hlawka-schatten','quadratic-forms','convexity'],
        solution_file='formalization/platform/Sol_matrix_pair_residual.lean',
        explanation='The direct pair sums have squared energy at most 3 times the matrix energy, using the columnwise identity 3(x²+y²+z²)-(x+y)²-(x+z)²=(x-y-z)²+(y-z)². The main-coordinate sums occur twice, giving energy at most 4 times the matrix energy. Multiplication by the bounded theta coefficients gives the factor rho². The proved weighted-square estimate then yields the claimed rational coefficient. Every helper proof is included in the submitted file.'))
    for item in payloads:
        data=(ROOT/item['solution_file']).read_bytes()
        assert b'sorry' not in data and b'axiom ' not in data
        item['solution_sha256']=hashlib.sha256(data).hexdigest()
    (OUT/'payloads.json').write_text(json.dumps(payloads,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
    print('Prepared',len(payloads),'proofs for exact local compilation and platform verification.')

if __name__=='__main__':make()
