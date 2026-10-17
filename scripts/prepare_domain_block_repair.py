"""Repair one timed-out block by smaller faithful localization lemmas.

The parent statement and complete coverage stay unchanged. Original leaf proof
texts are reused verbatim (apart from indentation), and their arithmetic
dependencies are bundled only for the selected subintervals.
"""
import argparse,hashlib,json,re
from fractions import Fraction as F
from generate_contractor_lean import ROOT,rat
from prepare_real_chunk_platform_proofs import bundle,HELPER


def merge(path,items):
    old=json.loads(path.read_text(encoding='utf-8')) if path.exists() else []
    keys={r['key'] for r in items}
    path.write_text(json.dumps([r for r in old if r['key'] not in keys]+items,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('parent')
    parser.add_argument('--size',type=int,choices=[1,2],default=2)
    args=parser.parse_args()
    payloads=json.loads((ROOT/'formalization/platform/domain-block-proofs.json').read_text(encoding='utf-8'))
    covers=json.loads((ROOT/'formalization/domain-blocks.json').read_text())
    parent=next(p for p in payloads if p['key']==args.parent)
    row=next(p for p in covers if p['theorem_name']==parent['theorem_name'])
    state=json.loads((ROOT/'results/prove2me-domain-blocks.json').read_text())
    target=state['theorems'][args.parent]
    assert target['proof_status']=='ERROR','Repair only a confirmed terminal failure'
    assert 'timed out' in target.get('proof_error','').lower(),'Inspect non-timeout errors before decomposing'
    cutoff=row['cutoff'];indices=row['indices']
    assert len(indices)>args.size
    slabs=json.loads((ROOT/f'certificates/cutoff{cutoff}/contractor.json').read_text())
    original=(ROOT/'formalization'/(row['module'].replace('.','/')+'.lean')).read_text(encoding='utf-8')
    pstart=original.index(' := by\n')+len(' := by\n')
    header=original[:pstart]
    source_lines=original[pstart:].splitlines()
    leaves={}
    for i,line in enumerate(source_lines):
        m=re.match(r'^( *)have hh := localize'+str(cutoff)+r'_slab(\d+)',line)
        if not m:continue
        depth=len(m[1]);body=[]
        for candidate in source_lines[i:]:
            if candidate.strip() and len(candidate)-len(candidate.lstrip())<depth:break
            body.append(candidate[depth:] if candidate.strip() else '')
        leaves[int(m[2])]=body
    assert set(leaves)==set(indices)
    children=[]
    for part,start in enumerate(range(0,len(indices),args.size)):
        selected=indices[start:start+args.size]
        a,b=F(slabs[selected[0]]['a']),F(slabs[selected[-1]]['b'])
        key=args.parent.replace('domain4','domain'+str(args.size))+f'_part{part}'
        name='HlawkaSchatten.DiagonalCutoff21.'+key
        childheader='\n'.join(line for line in header.splitlines() if not line.startswith('import '))+'\n'
        childheader=childheader.replace('bounds_'+args.parent,'bounds_'+key)
        childheader=childheader.replace('hpa : '+rat(F(row['a']))+' ≤ p','hpa : '+rat(a)+' ≤ p')
        childheader=childheader.replace('hpb : p ≤ '+rat(F(row['b'])),'hpb : p ≤ '+rat(b))
        proof=[]
        if len(selected)==2:
            proof.append(f'  rcases le_total p {rat(F(slabs[selected[1]]["a"]))} with hl | hr')
            for k in selected:
                proof.append('  ·')
                proof += ['    '+line for line in leaves[k]]
        else:
            assert len(selected)==1
            proof += ['  '+line for line in leaves[selected[0]]]
        module=f'Hlawka21.DomainChildren{cutoff}.Block{row["index"]:02d}Size{args.size}Part{part}'
        path=ROOT/'formalization'/(module.replace('.','/')+'.lean')
        path.parent.mkdir(parents=True,exist_ok=True)
        imports='import Hlawka21.PieceTools\n'+'\n'.join(f'import Hlawka21.Localized{cutoff}.Slab{k:03d}' for k in selected)+'\n'
        path.write_text(imports+childheader+'\n'.join(proof)+'\n\nend HlawkaSchatten.DiagonalCutoff21\n',encoding='utf-8',newline='\n')
        oldinterval=f'∀ p : ℝ, {rat(F(row["a"]))} ≤ p → p ≤ {rat(F(row["b"]))}'
        newinterval=f'∀ p : ℝ, {rat(a)} ≤ p → p ≤ {rat(b)}'
        formal=parent['formal_statement'].replace(parent['theorem_name'],name).replace(oldinterval,newinterval)
        original_sol=(ROOT/parent['solution_file']).read_text(encoding='utf-8')
        wrapper=original_sol[original_sol.index('theorem solution'):].replace(oldinterval,newinterval).replace('bounds_'+args.parent,'bounds_'+key)
        preamble,body=bundle(module)
        assert not any(line.startswith('import Theorems.') for line in preamble.splitlines())
        body=body.replace('open HlawkaSchatten.DiagonalCutoff21\n','')
        sol=ROOT/f'formalization/platform/Sol_{key}.lean'
        sol.write_text(body+wrapper,encoding='utf-8',newline='\n')
        mirror=f'import {module}\nopen HlawkaSchatten HlawkaSchatten.DiagonalConstruction\n'+wrapper.replace('theorem solution','theorem '+name).replace('#print axioms solution','#print axioms '+name).replace(HELPER,'HlawkaSchatten.DiagonalCutoff21')
        (ROOT/'formalization/Theorems'/('Thm_'+name.replace('.','_')+'.lean')).write_text(mirror,encoding='utf-8',newline='\n')
        item=dict(parent,key=key,theorem_name=name,formal_statement=formal,theorem_title=f'Actual norm localization subblock [{a},{b}]',
                  solution_file=sol.relative_to(ROOT).as_posix(),solution_sha256=hashlib.sha256(sol.read_bytes()).hexdigest(),
                  parent_key=args.parent,a=str(a),b=str(b),indices=selected,
                  natural_language_statement=f'On [{a},{b}], the original norm data in the displayed coarse box imply the same explicit analytic-domain bounds as the parent localization theorem. This proves {len(selected)} consecutive original parameter slabs; it is a faithful subinterval decomposition of that same localization result, with no new validity premise.',
                  explanation=f'Complete actual-norm localization for {len(selected)} original slabs. The original leaf proof texts are reused and all integer-power inequalities and ten contraction rounds are checked here. No platform theorem imports or external numerical validity predicates are used. The parent timed out; this smaller proof will be recombined into its unchanged statement.')
        children.append(item)
    assert [i for c in children for i in c['indices']]==indices
    cursor=F(row['a'])
    for c in children:
        assert F(c['a'])==cursor<F(c['b']);cursor=F(c['b'])
    assert cursor==F(row['b'])
    statement=parent['formal_statement'].replace('theorem '+parent['theorem_name'],'theorem solution').replace(' := by sorry',' := by')
    imports='\n'.join('import Theorems.Thm_'+c['theorem_name'].replace('.','_') for c in children)+'\nimport Mathlib.Tactic.Linarith\nopen HlawkaSchatten HlawkaSchatten.DiagonalConstruction\n'
    lines=[imports,statement,'  intro p hp hpmax X hd ho hS hT hG']
    def emit(items,indent):
        if len(items)==1:
            lines.append(indent+f'exact {items[0]["theorem_name"]} p (by linarith) (by linarith) X hd ho hS hT hG')
        else:
            mid=len(items)//2
            lines.append(indent+f'rcases le_total p {rat(F(items[mid]["a"]))} with hl | hr')
            lines.append(indent+'·');emit(items[:mid],indent+'  ')
            lines.append(indent+'·');emit(items[mid:],indent+'  ')
    emit(children,'  ')
    lines+=['','#print axioms solution','']
    repair=ROOT/f'formalization/platform/Repair_{args.parent}_size{args.size}.lean'
    repair.write_text('\n'.join(lines),encoding='utf-8',newline='\n')
    merge(ROOT/'formalization/platform/domain-child-proofs.json',children)
    merge(ROOT/'formalization/platform/domain-repair-proofs.json',[dict(key=args.parent,theorem_id=target['theorem_id'],theorem_name=parent['theorem_name'],formal_statement=parent['formal_statement'],
        solution_file=repair.relative_to(ROOT).as_posix(),solution_sha256=hashlib.sha256(repair.read_bytes()).hexdigest(),
        children=[c['key'] for c in children],explanation='Faithful subinterval decomposition of the unchanged parent localization statement. Each smaller actual-norm certificate proves the same explicit conclusions on its subinterval; their closed cover proves the parent. This revised proof imports the children rather than rerunning the timed-out arithmetic file.')])
    print('Prepared',len(children),'faithful children and unchanged-parent reduction for',args.parent)


if __name__=='__main__':main()
