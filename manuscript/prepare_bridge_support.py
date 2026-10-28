"""2026-10-27: collect the existing arithmetic support for input (II), 31--46.

Run with ordinary Python 3.11+ and the standard library only:
    python -B prepare_bridge_support.py --workspace /path/to/kan-x
    python -B companions/bridge-support/read_bridge_support.py --inspect all

This selection preserves original 2026-10-25/26 files without editing them.
The work/ directory relations, original filenames, source comments, TeX
attribution and release paths inside the compressed inputs remain intact.
The original source hierarchy includes threshold31_20261008,
continuation_20261010 and BE_cutoff35_release_20261007. No new authorship or
mathematical scope is assigned by this collection.

31 consumes a30<1/100; the new preceding C30<=CE result supplies that premise.
32--34 need the complete current31 objects as well as their literal-index
support/count results. 35 and 36--38 have their own frozen inputs. 39 needs
the original failed positive39 return and its independently obtained scalar
recovery license. The resumed40 archive already embeds the entire failed40
return, so a second loose copy is deliberately omitted. 41 uses the original
floor40 indexed union; 42--46 use the original LOCAL42 family. Its stored
42--48 range is preserved, even though this manuscript uses it only to46.

Only sidecars actually read by the copied joins are selected. There are no
expanded numerical source trees, new hash lists, generated acceptance files
or copied cloud submissions beyond the job descriptions read by those joins.
Copying is preparation for inspection, not a proof or a numerical replay.
"""

import argparse
import filecmp
from pathlib import Path
import shutil


HERE = Path(__file__).resolve().parent
DEFAULT_DESTINATION = HERE / 'companions/bridge-support'
N31 = 'berry-esseen-n31-primary-check-20261025'
N35 = 'berry-esseen-n35-complete-20261025'
N36 = 'berry-esseen-n36-38-complete-20261026'
N39 = 'berry-esseen-n39-complete-20261026'
N40 = 'berry-esseen-n40-route-20261026'
N42 = 'berry-esseen-n41-48-route-20261026'


def selected_files():
    """Explicit reusable selection; archive contents keep their original paths."""
    files = []

    def add(directory, *names):
        files.extend(Path('work') / directory / name for name in names)

    add(N31,
        'sharp31_frozen_inputs_20261025.zip',
        'sharp31_fresh_parent_results_20261025.zip',
        'bridge32_34_frozen_inputs_20261025.zip',
        'join_sharp31_fresh_20261025.py',
        'sharp31_cloud_replay_20261025.py',  # literal frozen-input binding
        'join_bridge32_34_fresh_20261025.py',
        'check_bridge32_34_targets_20261025.py',  # imported interface functions
        'bridge32_34_cloud_replay_20261025.py',  # literal frozen-input binding
        'check_current31_composition_20261025.py',
        'check_n31_scalar_chain_20261025.py',
        'n31_fresh_jobs_20261025.json',  # original174-target compatibility plan
        'bridge34_native_proof_byte_join_20261025.json',  # consumed by35
        'sharp31_B7_D_domain_20261025.tex')
    # This original compressed source is consumed by the compatibility
    # module's standalone main. Keep it compressed and in its original sibling
    # directory; no unrelated source tree is expanded from it.
    add('berry-esseen-n49-check-20261025', 'closure31.zip')
    for n, returned in ((32, 'cnb-3gn-1k5pno3p2'),
                        (33, 'cnb-lds-1k5pnvfvd'),
                        (34, 'cnb-ho9-1k5po60tl')):
        add(N31, f'bridge{n}_cloud_job_20261025.json')
        add(N31, *(f'cloud-results-{returned}/' + name for name in (
            f'bridge{n}_fresh_results_20261025.zip',
            f'bridge{n}_fresh_summary_20261025.json', 'result.json', 'state.json')))
    add(N35, 'n35_frozen_inputs_20261025.zip',
        'check_n35_final_join_20261025.py', 'n35_cloud_job_20261025.json')
    add(N35, *('cloud-results-cnb-h5l-1k5pr0285/' + name for name in (
        'n35_fresh_results_20261025.zip', 'n35_fresh_summary_20261025.json',
        'result.json', 'state.json')))
    add(N36, 'actual36_38_frozen_inputs_20261026.zip',
        'check36_38_final_join_20261026.py', 'actual36_38_cloud_job_20261026.json')
    add(N36, *('cloud-results-cnb-qnv-1k5q0h0an/' + name for name in (
        'actual36_38_fresh_results_20261026.zip',
        'actual36_38_fresh_summary_20261026.json', 'result.json', 'state.json')))
    add(N39, 'n39_frozen_inputs_20261026.zip',
        'positive39_fresh_results_20261026.zip',  # its original exit1 is retained
        'positive39-recovery-run-20261026-04/positive39_recovery_license_20261026.zip',
        'check_sharp39_final_join_20261026.py', 'recover_positive39_20261026.py',
        'actual39_continuous_lemmas_20261026.tex',
        'check_actual39_continuous_domain_20261026.py')
    add(N39, *('cloud-results-cnb-1dh-1k5q80ukp/' + name for name in (
        'sharp39_fresh_results_20261026.zip',
        'sharp39_fresh_summary_20261026.json', 'state.json')))
    add(N40, 'actual40_frozen_inputs_20261026.zip',
        'actual40_resume_execution_inputs_20261026.zip',
        'check_actual40_resumed_final_join_20261026.py',
        'check_actual40_final_join_20261026.py', 'actual40_join_structures_20261026.py')
    add(N40, *('cloud-results-cnb-r79-1k5qiopeu/' + name for name in (
        'actual40_resume_fresh_results_20261026.zip',
        'actual40_resume_fresh_summary_20261026.json', 'state.json')))
    add(N42, 'uniform42_frozen_inputs_20261026.zip',
        'collect_uniform42_final_20261026.py', 'check_uniform42_cover_20261026.py',
        'cloud-results-cnb-7qf-1k5qgsik0/uniform42_fresh_results_20261026.zip')
    return files


def workspace_default():
    for candidate in HERE.parents:
        if (candidate / 'work' / N31).is_dir():
            return candidate
    return None


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--workspace', type=Path, default=workspace_default())
    parser.add_argument('--destination', type=Path, default=DEFAULT_DESTINATION)
    parser.add_argument('--plan', action='store_true', help='Print sizes without copying')
    args = parser.parse_args()
    if args.workspace is None:
        parser.error('The original workspace is required for collection; use --workspace.')
    workspace = args.workspace.resolve()
    destination = args.destination.resolve()
    reader = DEFAULT_DESTINATION / 'read_bridge_support.py'
    selected = selected_files()
    missing = [str(p) for p in selected if not (workspace / p).is_file()]
    if not reader.is_file():
        missing.append(str(reader))
    if missing:
        raise FileNotFoundError('Missing original supporting input(s):\n' + '\n'.join(missing))
    if destination == workspace or destination.is_relative_to(workspace / 'work'):
        raise ValueError('The collection destination must be separate from original work inputs.')
    total = sum((workspace / p).stat().st_size for p in selected)
    if args.plan:
        for p in selected:
            print(f'{(workspace / p).stat().st_size:>12}  {p.as_posix()}')
        print(f'{len(selected)} original files; {total:,} bytes; reader copied separately')
        return
    copied = unchanged = 0
    for relative in selected:
        source, target = workspace / relative, destination / relative
        target.resolve().relative_to(destination)
        if target.exists():
            if not target.is_file() or not filecmp.cmp(source, target, shallow=False):
                raise FileExistsError('Existing companion differs; inspect before replacing: ' + str(target))
            unchanged += 1
            continue
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(source, target)
        copied += 1
    target_reader = destination / reader.name
    if target_reader.resolve() != reader.resolve():
        if target_reader.exists() and not filecmp.cmp(reader, target_reader, shallow=False):
            raise FileExistsError('Existing reader differs: ' + str(target_reader))
        if not target_reader.exists():
            target_reader.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(reader, target_reader)
    print(f'Collected {copied} original files; {unchanged} already identical; {total:,} bytes.')
    print('Inspect recorded mathematical objects with:')
    print(f'  python -B "{target_reader}" --inspect all')


if __name__ == '__main__':
    main()
