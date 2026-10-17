"""Record observed local and platform progress without upgrading pending jobs."""
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]


def read(path):
    return json.loads((ROOT/path).read_text(encoding='utf-8'))


def main():
    core=read('results/lean-full-window-build.json')
    localization=read('results/lean-localization-build.json')
    assert core['status']==localization['status']=='PASS'
    goals=read('results/prove2me-goals.json')
    root=next(r for r in goals['targets'] if r['key']=='goal')
    status=read('status.json')
    verification=status['verification']
    evidence=['results/lean-failure-build.json','results/prove2me-failure.json',
              'results/lean-localization-build.json','results/lean-geometry-build.json',
              'results/lean-real-chunks-build.json','results/lean-full-window-build.json',
              'results/lean-analytic-assembly-build.json','results/prove2me-analytic-assembly.json',
              'results/lean-real-platform-build.json','results/prove2me-real-chunks.json',
              'results/lean-real-pieces-build.json','results/prove2me-real-pieces.json',
              'results/lean-localization-platform-build.json','results/prove2me-localization.json',
              'results/lean-domain-blocks-build.json','results/prove2me-domain-blocks.json',
              'results/lean-root-assembly-build.json','results/prove2me-root.json',
              'results/lean-domain-children-build.json','results/prove2me-domain-children.json',
              'results/lean-domain-repairs-build.json','results/prove2me-domain-repairs.json']
    accepted=0
    for path in ['results/prove2me-auxiliary.json','results/prove2me-failure.json',
                 'results/prove2me-analytic-assembly.json','results/prove2me-real-pieces.json',
                 'results/prove2me-localization.json','results/prove2me-domain-blocks.json',
                 'results/prove2me-domain-children.json']:
        if (ROOT/path).exists():
            accepted+=sum(r.get('proof_status')=='ACCEPTED' for r in read(path)['theorems'].values())
    complete=root['status']=='Proved' and root.get('open_leaf_count')==0
    verification['full_cutoff21_lean_proof']=complete
    formal=verification['lean_formalization']
    local_files=0
    for path in ['results/lean-auxiliary-build.json','results/lean-failure-build.json',
                 'results/lean-analytic-assembly-build.json',
                 'results/lean-localization-platform-build.json','results/lean-domain-blocks-build.json',
                 'results/lean-domain-children-build.json','results/lean-domain-repairs-build.json']:
        if (ROOT/path).exists():
            local_files+=sum(r.get('status')=='PASS' for r in read(path)['proofs'])
    formal.update(stage='original_full_goal_proved' if complete else 'all_new_ingredients_kernel_checked; platform_closure_in_progress',
                  locally_compiled_auxiliary_files=local_files,
                  local_auxiliary_file_count_scope='Passing exact files in the current auxiliary submission manifests; the superseded large packet checks are recorded separately.',
                  platform_accepted_auxiliary_theorems=accepted,
                  root_status=root['status'],
                  locally_proved_original_real_windows=['real_three_window21','real_three_window26'],
                  actual_norm_localization_slabs=localization['slabs'],
                  localization_integer_power_certificates=localization['root_certificates'],
                  new_core_source_hashes=len(core['sources']),
                  new_core_axiom_checks=len(core['axiom_checks']),
                  new_core_evidence='results/lean-full-window-build.json',
                  local_final_assembly='Exact cutoff21 conclusion with an explicit cutoff32 tail input; the already Proved platform tail is not independently rebuilt here.',
                  platform_proved_original_milestones=[r['theorem_name'].rsplit('.',1)[-1] for r in goals['targets'] if r['key']!='goal' and r['status']=='Proved'],
                  compact_certificate_manifest='formalization/platform/domain-block-proofs.json',
                  compact_certificate_build='results/lean-domain-blocks-build.json',
                  compact_certificate_platform='results/prove2me-domain-blocks.json',
                  superseded_eight_slab_manifest='formalization/platform/real-piece-proofs.json',
                  original_large_certificate_attempt='The first three 16-slab packets and the first three 8-slab packets timed out at the server 300s limit. Local proofs pass; packet size is being tested rather than treated as a fixed remaining theorem count.',
                  minimal_localization_platform='results/prove2me-localization.json',
                  domain_block_manifest='formalization/platform/domain-block-proofs.json',
                  domain_block_coverage='formalization/domain-blocks.json',
                  domain_block_build='results/lean-domain-blocks-build.json',
                  domain_block_platform='results/prove2me-domain-blocks.json')
    if (ROOT/'results/prove2me-domain-blocks.json').exists():
        blocks=read('results/prove2me-domain-blocks.json')['theorems']
        formal.update(domain_blocks_closed=sum(r.get('theorem_status')=='Proved' and r.get('open_leaf_count')==0 for r in blocks.values()),
                      domain_block_target_count=65,
                      domain_block_repairs_pending=[k for k,r in blocks.items() if r.get('repair_pending')],
                      domain_repair_manifest='formalization/platform/domain-repair-proofs.json')
    if (ROOT/'results/prove2me-root.json').exists():
        assembly=read('results/prove2me-root.json')
        formal.update(root_submission_status=assembly.get('proof_status'),
                      root_assembly_open_leaf_count=assembly.get('open_leaf_count'),
                      root_assembly_evidence='results/prove2me-root.json')
    for path in evidence:
        if (ROOT/path).exists() and path not in verification['evidence']:
            verification['evidence'].append(path)
    (ROOT/'status.json').write_text(json.dumps(status,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
    print('Recorded',accepted,'accepted auxiliary proofs;',root['status'],'original full goal')


if __name__=='__main__':
    main()
