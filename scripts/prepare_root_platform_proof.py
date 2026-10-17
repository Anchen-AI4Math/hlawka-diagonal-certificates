"""Assemble the unchanged root with an explicit, already proved tail import.

The local check uses the exact same body and an explicit tail input, since the
accepted cutoff32 proof has not been independently rebuilt in this repository.
No local sorry placeholder or axiom is introduced for that tail.
"""
import hashlib
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]


def main():
    original=(ROOT/'platform/proposal/goal.lean').read_text(encoding='utf-8')
    statement=original[original.index('theorem '):].strip()
    rootname='HlawkaSchatten.DiagonalConstruction.campaign_cutoff21'
    imports='\n'.join('import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_'+s for s in
                     ['real_three_window21','real_three_window26','complex_least_of_real_three'])
    imports+='\nimport Mathlib.Tactic.Linarith\n'
    opens='open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff21\n'
    body=''' := by
  intro p hp
  by_cases hp32 : 32 ≤ p
  · exact TAIL p hp32
  · apply complex_least_of_real_three p (by linarith)
    by_cases hp26 : p ≤ 26
    · exact real_three_window21 p hp hp26
    · exact real_three_window26 p (by linarith) (by linarith)
'''
    tail='''∀ p : ℝ, 32 ≤ p →
      IsLeast {C : ℝ | ∀ n : ℕ,
        HasHlawkaConstant (lpNorm p : (Fin n → ℂ) → ℝ) C} (cyclicConstant p)'''
    conditional=imports+opens+'\n'+statement.replace('theorem '+rootname,
        'theorem checked_root_assembly (htail : '+tail+')').replace(' := by sorry',body.replace('TAIL','htail'))
    conditional+='\n#print axioms checked_root_assembly\n'
    cpath=ROOT/'formalization/platform/Check_root_assembly.lean'
    cpath.write_text(conditional,encoding='utf-8',newline='\n')
    source=imports+'import Theorems.Thm_HlawkaSchatten_DiagonalConstruction_campaign_cutoff32\n'+opens+'\n'
    source+=statement.replace('theorem '+rootname,'theorem solution').replace(' := by sorry',body.replace('TAIL','campaign_cutoff32'))
    source+='\n#print axioms solution\n'
    assert 'sorry' not in source+conditional
    path=ROOT/'formalization/platform/Sol_campaign_cutoff21.lean'
    path.write_text(source,encoding='utf-8',newline='\n')
    manifest=[dict(key='campaign_cutoff21',theorem_id='db286144-c8c4-4918-9bc9-03fcadedfffd',
        theorem_name=rootname,formal_statement=statement,
        solution_file=path.relative_to(ROOT).as_posix(),solution_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
        conditional_check_file=cpath.relative_to(ROOT).as_posix(),conditional_check_sha256=hashlib.sha256(cpath.read_bytes()).hexdigest(),
        local_check_scope='The exact same assembly body with an explicit cutoff32 tail input. The server file itself is checked by Prove2Me using its accepted tail theorem; the tail is not independently rebuilt locally.',
        explanation='The original full statement is unchanged. For p>=32 apply the already Proved campaign_cutoff32. For 21<=p<32 apply the already Proved universal real-three-to-complex least-constant theorem, using the original real-three window21 or window26 as appropriate. All natural dimensions including zero, all complex triples and IsLeast remain in the target. The two real-three windows are tracked dependencies: this is not a complete proof until both are Proved and the original root has zero open leaves. No self import or external validity axiom is used.')]
    (ROOT/'formalization/platform/root-proof.json').write_text(json.dumps(manifest,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
    check_manifest=[dict(key='conditional_root_assembly',solution_file=cpath.relative_to(ROOT).as_posix(),solution_sha256=hashlib.sha256(cpath.read_bytes()).hexdigest())]
    (ROOT/'formalization/platform/root-assembly-check.json').write_text(json.dumps(check_manifest,indent=2)+'\n',encoding='utf-8')
    print('Prepared unchanged root and explicit-tail local assembly check.')


if __name__=='__main__':main()
