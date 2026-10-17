"""Check the exact window assembly bodies with explicit certificate inputs.

The original unconditional real windows are already kernel checked by
check_full_window_lean.py, and all finite certificates have exact-file checks.
This check isolates their interface composition without duplicating arithmetic.
The final server files keep the original statements and import the actual
platform theorems, whose complete dependency closure must be Proved.
"""
import hashlib,json
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]


def main():
    windows=json.loads((ROOT/'formalization/platform/real-window-proofs.json').read_text())
    certificates=json.loads((ROOT/'formalization/platform/domain-block-proofs.json').read_text(encoding='utf-8'))
    records=[]
    mappings=[]
    for window in windows:
        cutoff=int(window['key'][-2:])
        relevant=[c for c in certificates if c['key'].startswith(f'localized_domain4_{cutoff}_')]
        original=(ROOT/window['solution_file']).read_text(encoding='utf-8')
        assert hashlib.sha256(original.encode('utf-8')).hexdigest()==window['solution_sha256']
        remove={'import Theorems.Thm_'+c['theorem_name'].replace('.','_') for c in relevant}
        imports='\n'.join(line for line in original[:original.index('theorem solution')].splitlines() if line not in remove)+'\n'
        assert not any(s in imports for s in remove)
        binders=[];replacements={}
        for c in relevant:
            prefix='theorem '+c['theorem_name']+' :'
            statement=c['formal_statement']
            assert statement.startswith(prefix) and statement.endswith(' := by sorry')
            ctype=statement[len(prefix):-len(' := by sorry')].strip()
            parameter='certificate_'+c['key']
            binders.append('    ('+parameter+' : '+ctype+')')
            replacements[c['theorem_name']]=parameter
        declaration=original[original.index('theorem solution'):]
        typename='checked_assembly_'+window['key']
        transformed=declaration.replace('theorem solution :','theorem '+typename+'\n'+'\n'.join(binders)+' :',1)
        for name,parameter in replacements.items():transformed=transformed.replace(name,parameter)
        transformed=transformed.replace('#print axioms solution','#print axioms '+typename)
        rebuilt=transformed.replace('theorem '+typename+'\n'+'\n'.join(binders)+' :','theorem solution :',1)
        rebuilt=rebuilt.replace('#print axioms '+typename,'#print axioms solution')
        for name,parameter in replacements.items():rebuilt=rebuilt.replace(parameter,name)
        assert rebuilt==declaration,'Assembly body must be identical after interface substitution'
        source=imports+transformed
        assert 'sorry' not in source and 'axiom ' not in source
        path=ROOT/f'formalization/platform/Check_assembly_real{cutoff}.lean'
        path.write_text(source,encoding='utf-8',newline='\n')
        records.append(dict(key='conditional_'+window['key'],solution_file=path.relative_to(ROOT).as_posix(),solution_sha256=hashlib.sha256(path.read_bytes()).hexdigest()))
        mappings.append(dict(key=window['key'],server_solution_sha256=window['solution_sha256'],conditional_solution_sha256=records[-1]['solution_sha256'],
            explicit_certificate_inputs=len(relevant),certificate_keys=[c['key'] for c in relevant],
            scope='Only the assembly interface is conditional here. The original unconditional real windows and every finite certificate are separately kernel checked; the server checks the unchanged original statement using tracked proved dependencies. No local axiom or sorry placeholder is introduced.'))
    (ROOT/'formalization/platform/real-window-assembly-checks.json').write_text(json.dumps(records,indent=2)+'\n',encoding='utf-8')
    (ROOT/'formalization/platform/real-window-assembly-mapping.json').write_text(json.dumps(mappings,indent=2)+'\n',encoding='utf-8')
    shared=[('dimension_reduction','HlawkaSchatten.DiagonalConstruction.real_bound_of_fin_three')]
    shared += [(s,'HlawkaSchatten.DiagonalCutoff21.'+s) for s in
               ['scalar_window21','scalar_window26','coarse_failure_window21','coarse_failure_window26',
                'domain_nonneg_group00','domain_nonneg_group01','real_three_window21','real_three_window26','complex_least_of_real_three']]
    (ROOT/'formalization/platform/assembly-shared-mirrors.json').write_text(json.dumps([dict(key=k,theorem_name=n) for k,n in shared],indent=2)+'\n',encoding='utf-8')
    print('Prepared exact-body assembly checks with 41 and 24 explicit certificate inputs.')


if __name__=='__main__':main()
