"""Check replayed traces and compare actual Rust outcomes/witnesses with Lean."""
from __future__ import annotations

import json
from pathlib import Path

from evidence import require_success, run_logged


def translate(nodes: dict, identity: int, atoms: dict) -> dict:
    node = nodes[identity]
    if 'value' in node:
        return {'kind': 'literal', 'value': node['value']}
    if 'atom' in node:
        return {'kind': 'atom', 'index': atoms[node['atom']]}
    operator = node['operator']
    children = node['inputs']
    if operator == 'not':
        return {'kind': 'not', 'inner': translate(nodes, children[0], atoms)}
    if operator not in {'and', 'or'} or len(children) != 2:
        raise ValueError('non-formula node used by a prepared check')
    return {'kind': operator, 'left': translate(nodes, children[0], atoms),
            'right': translate(nodes, children[1], atoms)}


def evaluate(formula: dict, assignment: list[bool]) -> bool:
    kind = formula['kind']
    if kind == 'literal':
        return formula['value']
    if kind == 'atom':
        return assignment[formula['index']]
    if kind == 'not':
        return not evaluate(formula['inner'], assignment)
    left, right = evaluate(formula['left'], assignment), evaluate(formula['right'], assignment)
    return left and right if kind == 'and' else left or right


def requests_for(name: str, report: dict) -> list[dict]:
    nodes = {node['id']: node for node in report['trace']}
    if len(nodes) != len(report['trace']):
        raise ValueError('duplicate trace identity')
    for node in report['trace']:
        if any(parent not in nodes or parent >= node['id'] for parent in node['inputs']):
            raise ValueError('trace has a missing or non-backward edge')
    result = []
    for check in report['checks']:
        if check['result'] == 'not-evaluated':
            continue
        matches = [node for node in report['trace'] if node['kind'] == 'evaluation' and node['check'] == check['id']]
        if len(matches) != 1:
            raise ValueError('evaluation inventory mismatch')
        node = matches[0]
        atoms = {identity: index for index, identity in enumerate(node['atoms'])}
        query = translate(nodes, node['query'], atoms)
        premises = [translate(nodes, identity, atoms) for identity in node['premises']]
        witnesses = []
        for polarity, key in [(True, 'positive'), (False, 'negative')]:
            model = check.get('models', {}).get(key)
            if model is not None:
                witnesses.append({'assignment': model['assignment'], 'polarity': polarity})
                for value in model['node_values']:
                    if evaluate(translate(nodes, value['node'], atoms), model['assignment']) != value['value']:
                        raise ValueError('retained model node value is not replayable')
        for row in node.get('rows', []):
            expected_assignment = [bool(row['valuation'] & (1 << shift)) for shift in reversed(range(len(atoms)))]
            expected_premises = [evaluate(premise, expected_assignment) for premise in premises]
            if (row['assignment'] != expected_assignment or row['premise_values'] != expected_premises
                    or row['premises_hold'] != all(expected_premises)
                    or row['query'] != evaluate(query, expected_assignment)):
                raise ValueError('valuation trace differs from its actual formula graph')
        result.append({'id': f'{name}:{check["name"]}', 'atoms': len(atoms),
                       'premises': premises, 'query': query, 'budget': report['budgets']['valuations'],
                       'witnesses': witnesses, 'expected': check['result']})
    return result


def compare(root: Path, evidence: Path, reference: Path, requests: list[dict]) -> dict:
    input_file = evidence / 'lean-rust-inputs.jsonl'
    input_file.write_text(''.join(json.dumps({key: value for key, value in request.items() if key != 'expected'}) + '\n'
                                  for request in requests))
    require_success(run_logged([str(reference), str(input_file)], root, evidence, 'lean-rust-differential'))
    actual = [json.loads(line) for line in (evidence / 'lean-rust-differential.stdout').read_text().splitlines()]
    expected = [{'id': request['id'], 'verdict': request['expected'],
                 'witness_checks': [True] * len(request['witnesses'])} for request in requests]
    if actual != expected:
        raise ValueError('actual Lean and Rust outcomes or supplied witness checks differ')
    return {'status': 'pass', 'checks': len(requests),
            'witnesses': sum(len(request['witnesses']) for request in requests),
            'scope': 'executed logical conformance and checked model witnesses; not a refinement theorem',
            'results': actual}
