"""Exercise the actual shipped CLI surface, with no compiler/prover on its PATH."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path

from evidence import digest, require_success, run_logged
from rust_differential import compare, requests_for
from rust_scenarios import EXAMPLES, scenarios


def run_case(root: Path, evidence: Path, binary: Path, name: str, content: bytes,
             exit_code: int, verdicts: list[str], command: str = 'prove') -> tuple[dict, dict]:
    source = evidence / f'{name}.weft'
    source.write_bytes(content)
    record = run_logged([str(binary), command, str(source)], root, evidence, name,
                        env={'PATH': '/no-toolchain'}, timeout=60)
    if record['exit_code'] != exit_code:
        raise ValueError(f'actual CLI exit differs: {name}')
    report = json.loads((evidence / f'{name}.stdout').read_text())
    if (report['schema'] != 'weft.report/1' or report['writfold_grounded'] is not False
            or report['effect_authority'] is not False):
        raise ValueError(f'CLI report overstated its scope: {name}')
    if [check['result'] for check in report['checks']] != verdicts:
        raise ValueError(f'actual CLI semantic outcomes differ: {name}')
    captured = report['source']
    if captured['sha256'] != hashlib.sha256(content).hexdigest() or captured['bytes'] != len(content):
        raise ValueError(f'CLI source identity differs: {name}')
    if captured['content']['encoding'] == 'hex':
        restored = bytes.fromhex(captured['content']['hex'])
    else:
        restored = captured['content']['text'].encode()
    if restored != content:
        raise ValueError(f'CLI source bytes changed: {name}')
    if name == 'output-limit' and not any(item['code'] == 'WF1601' and item['phase'] == 'report'
                                        for item in report['diagnostics']):
        raise ValueError('output limit did not produce its explicit report-stage refusal')
    collection_obligations(name, report)
    return report, {'id': name, 'status': 'pass', 'exit_code': exit_code,
                    'source_sha256': digest(source), 'results': verdicts, 'command': record}


def collection_obligations(name: str, report: dict) -> None:
    if name not in {'diamond-origins', 'failed-set-atomicity'}:
        return
    bindings = {binding['name']: binding for binding in report['review']['sets']}
    if name == 'failed-set-atomicity':
        if ([member['value']['value'] for member in bindings['good']['members']] != ['1']
                or 'members' in bindings['bad'] or 'cardinality' in bindings['bad']):
            raise ValueError('failed set altered a prior value or was published as an empty set')
        return
    diamond = bindings['diamond']
    if (diamond['raw_occurrences'] != 4 or diamond['cardinality'] != 3
            or [member['value']['value'] for member in diamond['members']] != ['1', '2', '3']):
        raise ValueError('diamond spread changed normalization or raw occurrence accounting')
    required = {binding['id'] for binding in bindings.values()}
    if not required.issubset(report['checks'][0]['dependencies']):
        raise ValueError('diamond spread lost a transitive binding dependency')
    origins = {origin['id']: origin for origin in report['origins']}
    pending, seen, references = [diamond['members'][0]['origin']], set(), set()
    while pending:
        identity = pending.pop()
        if identity in seen:
            continue
        seen.add(identity)
        origin = origins[identity]
        if origin['kind'] == 'reference':
            references.add(origin['declaration'])
        pending.extend(origin['inputs'])
    if not {bindings['left']['id'], bindings['right']['id']}.issubset(references):
        raise ValueError('deduplicated diamond member lost one source branch')


def qualify(root: Path, evidence: Path, binary: Path, reference: Path, finite_reference: Path) -> dict:
    cases, requests = [], []
    for name, verdicts in EXAMPLES.items():
        report, case = run_case(root, evidence, binary, f'example-{name}',
                                (root / f'examples/{name}.weft').read_bytes(), 1, verdicts)
        cases.append(case)
        requests.extend(requests_for(name, report))
    for name, content, exit_code, verdicts in scenarios():
        report, case = run_case(root, evidence, binary, name, content, exit_code, verdicts)
        cases.append(case)
        requests.extend(requests_for(name, report))
    for name in ('ordering', 'conditional'):
        source = root / f'examples/{name}.weft'
        record = run_logged([str(binary), 'analyze', str(source)], root, evidence, f'external-{name}',
                            env={'PATH': '/no-toolchain'}, timeout=30)
        report = json.loads((evidence / f'external-{name}.stdout').read_text())
        if record['exit_code'] != 2 or any(check['result'] != 'not-evaluated' for check in report['checks']):
            raise ValueError('external reference acquired an invented local interpretation')
        cases.append({'id': f'external-{name}', 'status': 'pass', 'command': record})
    source = evidence / 'analysis.weft'
    source.write_text('review a { context "c" at "s"; profile "weft.symbolic/1"; target p = proposal "p"; check q: true; }')
    record = run_logged([str(binary), 'analyze', str(source)], root, evidence, 'analysis', env={'PATH': '/no-toolchain'})
    require_success(record)
    analysis = json.loads((evidence / 'analysis.stdout').read_text())
    if analysis['scope'] != 'local-analysis' or analysis['checks'][0]['result'] != 'not-evaluated':
        raise ValueError('structural analysis asserted a proof')
    human = run_logged([str(binary), 'prove', str(source), '--human'], root, evidence, 'human', env={'PATH': '/no-toolchain'})
    if human['exit_code'] != 1 or b'\x1b' in (evidence / 'human.stdout').read_bytes():
        raise ValueError('human report failed or emitted terminal escape controls')
    require_success(run_logged([str(finite_reference)], root, evidence, 'finite-reference'))
    finite = [json.loads(line) for line in (evidence / 'finite-reference.stdout').read_text().splitlines()]
    if len(finite) != 17 or any(case['passed'] is not True for case in finite):
        raise ValueError('qualified finite reference changed behavior')
    differential = compare(root, evidence, reference, requests)
    return {'status': 'pass', 'binary_sha256': digest(binary), 'cases': cases,
            'analysis': record, 'human': human, 'finite_reference': finite,
            'differential': differential, 'child_PATH': '/no-toolchain'}
