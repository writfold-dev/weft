"""Validate complete requirement/source/evidence mapping without promoting blocked work."""
from __future__ import annotations

import argparse
import copy
import json
import sys
from pathlib import Path

sys.dont_write_bytecode = True

from contracts import reconcile
from evidence import capture_sources, digest, write_new


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def unique(rows: list[dict], key: str) -> dict:
    result = {row[key]: row for row in rows}
    require(len(result) == len(rows), f'duplicate {key} inventory')
    return result


def check(root: Path, data: dict) -> dict:
    contract = reconcile(root)
    adoption = json.loads((root / 'qualification/handover-adoption.json').read_text())
    theorems, gates, scenarios = (unique(data[key], 'id') for key in ('theorems', 'gates', 'scenarios'))
    require(set(theorems) == set(contract['theorem_ids']), 'theorem inventory differs')
    require(set(gates) == set(contract['stages']), 'stage inventory differs')
    require({row['gate'] for row in gates.values()} == set(contract['gates']), 'gate inventory differs')
    require(set(scenarios) == {f'S{number:02d}' for number in range(1, adoption['inventory']['scenarios'] + 1)},
            'scenario inventory differs')
    receipts = {}
    for name, reference in data['receipts'].items():
        path = Path(reference['path']).expanduser()
        if not path.is_absolute():
            path = root / path
        require(digest(path) == reference['sha256'], f'receipt identity changed: {name}')
        receipts[name] = (path, json.loads(path.read_text()))
    runtime_path, runtime = receipts['rust-runtime']
    require(runtime['status'] == 'pass' and runtime['scope'] == 'weft-local-symbolic-runtime-only',
            'runtime evidence has wrong status or scope')
    rust_sources = runtime['result']['source_manifest']
    _, proof = receipts['finite-reference']
    require(proof['status'] == 'pass', 'formal reference gate is not passed')
    producer = proof['result']['producer']
    require(producer['status'] == 'pass' and not producer['skipped'], 'formal producer is incomplete')
    formal_sources = producer['formal_source']
    ast = json.loads((runtime_path.parent / 'workspace-ast-policy.stdout').read_text())
    symbols = {(row['path'].removeprefix('/work/weft/'), row['name']) for row in ast['report']['counts']
               if row['kind'] == 'function'}
    expected_theorems = {row['id']: row for row in json.loads(
        (root / contract['authority'] / 'registries/theorems.json').read_text())['theorems']}
    expected_gates = {row['id']: row for row in json.loads(
        (root / contract['authority'] / 'registries/gates.json').read_text())['stages']}
    for identity, row in theorems.items():
        expected = expected_theorems[identity]
        require(row['declaration'] == expected['declaration'], f'wrong Lean declaration: {identity}')
        require(row.get('supporting_declarations', []) == expected.get('supporting_declarations', []),
                f'supporting declarations changed: {identity}')
        require(row['required'] is True and row['claim'] == expected['claim'], f'theorem contract changed: {identity}')
        for declaration in [row['declaration'], *expected.get('supporting_declarations', [])]:
            require(declaration in producer['axioms'], f'unaudited declaration: {declaration}')
        source_bound(root, row['lean_source'], formal_sources)
        for symbol in row['rust']:
            source_bound(root, symbol, rust_sources)
            require((symbol['path'], symbol['symbol']) in symbols, f'absent shipping symbol: {symbol}')
        for fixture in row['fixtures']:
            source_bound(root, fixture, rust_sources | formal_sources)
    for row in scenarios.values():
        require(all(family in theorems for family in row['theorem_families']), 'unknown scenario theorem')
        require(row['status'] in {'local-pass', 'scoped-evidence', 'blocked-external'}, 'invalid scenario scope')
        for fixture in row['fixtures']:
            source_bound(root, fixture, rust_sources | formal_sources)
        require(all(reference in receipts for reference in row['receipts']), 'missing scenario receipt')
    for identity, row in gates.items():
        require(all(row.get(key) == value for key, value in expected_gates[identity].items()),
                f'immutable gate requirements changed: {identity}')
        require(row['required'] is True and row['receipts'], f'required gate omitted evidence: {identity}')
        if row['status'] == 'pass':
            require(all(gates[parent]['status'] == 'pass' for parent in row['dependencies']),
                    f'blocked dependency promoted: {identity}')
            require(not row['external_prerequisites'], f'owner prerequisite falsely promoted: {identity}')
            require(all(receipts[reference][1].get('status') == 'pass' for reference in row['receipts']),
                    f'non-pass receipt promoted: {identity}')
        else:
            require(row['status'] == 'blocked-external', f'unknown gate state: {identity}')
    binary = runtime['result']['producer']['binary_sha256']
    require(digest(runtime_path.parent / 'weft') == binary, 'runtime artifact changed')
    require(receipts['scratch-runtime'][1]['binary_sha256'] == binary, 'scratch image qualified a different binary')
    return {'theorems': len(theorems), 'gates': len(gates), 'scenarios': len(scenarios),
            'shipping_symbols': sum(len(row['rust']) for row in theorems.values()), 'binary_sha256': binary}


def source_bound(root: Path, record: dict, qualified: dict) -> None:
    relative = Path(record['path'])
    require(not relative.is_absolute() and '..' not in relative.parts, 'source path escapes the checkout')
    require(qualified.get(record['path']) == record['sha256'], f'source is outside qualified closure: {relative}')
    require(digest(root / relative) == record['sha256'], f'current source changed: {relative}')


def calibrate(root: Path, data: dict) -> list[str]:
    mutations = []
    missing = copy.deepcopy(data); missing['theorems'].pop(); mutations.append(('missing-theorem', missing))
    duplicate = copy.deepcopy(data); duplicate['scenarios'].append(duplicate['scenarios'][0]); mutations.append(('duplicate-scenario', duplicate))
    promoted = copy.deepcopy(data); promoted['gates'][-1]['status'] = 'pass'; mutations.append(('blocked-release-promoted', promoted))
    symbol = copy.deepcopy(data); symbol['theorems'][0]['rust'][0]['symbol'] = 'unimplemented_symbol'; mutations.append(('invented-symbol', symbol))
    stale = copy.deepcopy(data); stale['theorems'][0]['fixtures'][0]['sha256'] = '0' * 64; mutations.append(('stale-source', stale))
    weakened = copy.deepcopy(data); weakened['gates'][-1]['dependencies'] = []; mutations.append(('removed-dependencies', weakened))
    rejected = []
    for name, mutated in mutations:
        try:
            check(root, mutated)
        except ValueError:
            rejected.append(name)
        else:
            raise ValueError(f'traceability negative control was accepted: {name}')
    return rejected


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--receipt', required=True, type=Path)
    args = parser.parse_args()
    root = Path(__file__).resolve().parent.parent
    receipt = args.receipt.expanduser().resolve()
    require(not receipt.is_relative_to(root), 'receipt must be outside source')
    receipt.parent.mkdir(parents=True, exist_ok=False)
    data = json.loads((root / 'qualification/traceability.json').read_text())
    result = {'schema_version': 1, 'status': 'fail', 'scope': 'requirement and source linkage only, not new theorem or runtime qualification'}
    try:
        result['source_snapshot'] = capture_sources(root,
            ['scripts/check_traceability.py', 'scripts/contracts.py', 'scripts/evidence.py',
             'qualification/traceability.json', 'qualification/handover-adoption.json'], receipt.parent / 'source.zip')
        result['inventory'] = check(root, data)
        result['negative_controls'] = calibrate(root, data)
        result['status'] = 'pass'
    except (OSError, ValueError, KeyError) as error:
        result['error'] = f'{type(error).__name__}: {error}'
    write_new(receipt, result)
    print(json.dumps(result, indent=2))
    return 0 if result['status'] == 'pass' else 1


if __name__ == '__main__':
    raise SystemExit(main())
