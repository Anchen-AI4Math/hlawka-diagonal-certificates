"""Translate the existing exact coarse LP witnesses into kernel-checked proofs.

This generator is untrusted. Each output implication is proved by linarith;
the selected hypotheses come from the nonzero entries of its rational dual.
The generated Lean contains no numerical oracle, axiom, or proof placeholder.
Coordinate encoding is v[3*j+i]=X[j,i], v[9+j]=N[j], v[12+i]=P[i], v[15]=T.
"""
import json
from fractions import Fraction as F
from pathlib import Path
from coarse_lp import model, add, scale, X, P, N, T

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'formalization' / 'Hlawka21'

def rat(value):
    value = F(value)
    if value.denominator == 1:
        return f'({value.numerator} : ℝ)'
    return f'({value.numerator} / {value.denominator} : ℝ)'

def linear(row):
    terms = []
    for i, coefficient in enumerate(map(F, row)):
        if coefficient:
            terms.append(f'{rat(coefficient)} * v {i}')
    return '(' + ' + '.join(terms) + ')' if terms else '(0 : ℝ)'

def generate(cutoff):
    profile = json.loads((ROOT/f'profiles/cutoff{cutoff}.json').read_text())
    data = json.loads((ROOT/f'certificates/cutoff{cutoff}/coarse.json').read_text())
    lo,c,q,loss = [F(profile[k]) for k in ['p_min','c','q','orientation_loss']]
    A,b,E,f = model(lo,c,q,loss)
    lines = [
        'import Mathlib.Data.Real.Basic',
        'import Mathlib.Tactic.Linarith',
        '',
        '/- Adapted from the exact LP model in scripts/coarse_lp.py and the',
        f'   cutoff-{cutoff} dual witnesses. Paper Section 3, equations (10)-(11).',
        '   v[3*j+i]=X[j,i], v[9+j]=N[j], v[12+i]=P[i], v[15]=T. -/',
        'set_option autoImplicit false',
        'set_option linter.unusedVariables false',
        'set_option maxHeartbeats 2000000',
        '',
    ]
    reports = []
    expected=[]
    for i in range(3):
        js=[j for j in range(3) if j!=i]
        large=add(*(X[j][i] for j in js))
        expected += [(large,F(0)),(scale(large,-1),F(-3))]
        for k in js:
            small=add(*(X[j][k] for j in js))
            for sign in [-1,1]:
                expected.append((add(scale(large,F(1,2)),scale(small,sign)),F(0)))
    for stage,records in enumerate(data['stages']):
        assert len(records)==len(expected)==18
        name=f'HlawkaSchatten.DiagonalCutoff21.coarse{cutoff}_stage{stage}'
        start=len(lines)
        lines += [f'theorem {name} (v : Fin 16 → ℝ)']
        for i,(row,bound) in enumerate(zip(A,b)):
            lines += [f'    (h{i} : {linear(row)} ≤ {rat(bound)})']
        lines += [f'    (heq : {linear(E[0])} = {rat(f[0])}) :']
        conclusions=[]
        for cert,(objective,target) in zip(records,expected):
            assert list(map(F,cert['objective']))==objective
            assert F(cert['target'])==target
            conclusions.append(f'{rat(target)} ≤ {linear(objective)}')
        lines += ['    '+' ∧\n    '.join(conclusions)+' := by']
        lines += ['  repeat\' constructor']
        for cert in records:
            used=[f'h{i}' for i,x in enumerate(cert['dual_ineq']) if F(x)]
            if F(cert['dual_eq'][0]):used.append('heq')
            lines += ['  · linarith only ['+', '.join(used)+']']
        lines += ['',f'#print axioms {name}','']
        reports.append(dict(name=name,stage=stage,premises=len(A),conclusions=len(records)))
        if stage==0:
            for i in range(3):
                js=[j for j in range(3) if j!=i]
                A.append(add(P[i],*(scale(X[j][i],-1) for j in js)))
                b.append(F(profile['half_tail']))
            box={k:F(v) for k,v in profile['coarse_box'].items()}
            expected=[]
            for j in range(3):
                for i in range(3):
                    low,high=(-box['diag_max'],-box['diag_min']) if i==j else (box['off_min'],box['off_max'])
                    expected += [(X[j][i],low),(scale(X[j][i],-1),-high)]
    output='\n'.join(lines)+'\n'
    assert 'sorry' not in output and 'axiom ' not in output
    (OUT/f'Coarse{cutoff}.lean').write_text(output,encoding='utf-8')
    return reports

if __name__=='__main__':
    OUT.mkdir(parents=True,exist_ok=True)
    report=[]
    for cutoff in [21,26]:report += generate(cutoff)
    print(json.dumps(report,indent=2))
