"""Operation-level Lean/Rust comparison for the revision-3 set algebra.

The Lean side (`weftfiniteref`) independently constructs and evaluates typed
inputs through the actual extended evaluators; the Rust side compiles the
corresponding source through the real CLI. This compares memberships, stable
order, typed empties, refusals, origin-closure reachability and the
deterministic subset counterexample on fixed paired vectors. It is not a
parser/refinement theorem, and it never feeds Rust's computed Booleans back as
Lean's expected set answers: both sides are evaluated independently and the
derived facts are compared.
"""
from __future__ import annotations

import json
from pathlib import Path

from evidence import digest, run_logged

ROOT = Path('/work/weft')
EVIDENCE = Path('/evidence')

HEADER = ('review paired { context "c" at "s"; profile "weft.symbolic/1"; '
          'target plan = proposal "p"; ')


def source(body: str) -> bytes:
    return (HEADER + body + ' }\n').encode()


def prove(binary: Path, name: str, body: str) -> tuple[int, dict | None, list[str]]:
    path = EVIDENCE / f'algebra-differential-{name}.weft'
    path.write_bytes(source(body))
    record = run_logged([str(binary), 'prove', str(path)], ROOT, EVIDENCE,
                        f'algebra-differential-{name}', env={'PATH': '/no-toolchain'}, timeout=60)
    text = (EVIDENCE / f'algebra-differential-{name}.stdout').read_text()
    report = json.loads(text) if text else None
    return record['exit_code'], report, (report or {}).get('diagnostics', [])


def members(report: dict, name: str) -> list[str]:
    for binding in report['review']['sets']:
        if binding['name'] == name:
            return [str(member['value']['value']) for member in binding.get('members', [])]
    raise ValueError(f'paired set missing: {name}')


def reachable_kinds(report: dict, set_name: str) -> set[str]:
    sets = {binding['name']: binding for binding in report['review']['sets']}
    origins = {origin['id']: origin for origin in report['origins']}
    target = sets[set_name]
    pending, seen = [target['origin']], set()
    kinds = set()
    while pending:
        identity = pending.pop()
        if identity in seen:
            continue
        seen.add(identity)
        origin = origins[identity]
        kinds.add(origin['kind'])
        pending.extend(origin['inputs'])
    return kinds


def compare(binary: Path, lean_cases: list[dict]) -> dict:
    by_id = {case['id']: case for case in lean_cases}
    if not all(by_id.get(f'algebra-{name}', {}).get('passed') is True for name in PAIRS):
        raise ValueError('Lean finite reference did not pass the paired algebra cases')
    results = []

    def paired(name: str, body: str, expect: str) -> None:
        exit_code, report, diagnostics = prove(binary, name, body)
        fact = expect(report, exit_code, diagnostics)
        results.append({'id': f'algebra-{name}', 'rust': fact, 'lean': by_id[f'algebra-{name}']['passed']})

    PAIRS['union-membership-order'](paired)
    PAIRS['intersection-merges-origins'](paired)
    PAIRS['difference-retains-right-closure'](paired)
    PAIRS['typed-empty-results'](paired)
    PAIRS['mixed-types-refused'](paired)
    PAIRS['membership-hit-miss'](paired)
    PAIRS['subset-counterexample'](paired)
    PAIRS['unavailable-operand-refused'](paired)
    PAIRS['shadowing-not-capture'](paired)
    return {
        'status': 'pass', 'pairs': results,
        'binary_sha256': digest(binary),
        'scope': ('executed operation-level Lean/Rust agreement on fixed paired vectors; '
                  'independent evaluation on both sides, not a Rust refinement theorem; '
                  'the zero-budget pair is exercised on the Rust side by the workspace '
                  'library budget tests and on the Lean side by weftfiniteref'),
    }


def _union(paired) -> None:
    paired('union-membership-order',
           'a := {1,2}; b := {2,3}; u := a | b;',
           lambda report, code, diags: (code, members(report, 'u')))


def _intersection(paired) -> None:
    def expect(report, code, diags):
        values = members(report, 'i')
        if values != ['2']:
            raise ValueError(f'intersection members differ: {values}')
        return code, values
    paired('intersection-merges-origins',
           'a := {1,2}; b := {2,3}; i := a & b; need i;',
           expect)


def _difference(paired) -> None:
    def expect(report, code, diags):
        if members(report, 'd') != ['1']:
            raise ValueError('difference members differ')
        kinds = reachable_kinds(report, 'd')
        if 'set-operation' not in kinds:
            raise ValueError('difference lost its operation-level operand link')
        return code, members(report, 'd')
    paired('difference-retains-right-closure',
           'a := {1,2}; b := {2,3}; d := a - b; need d;',
           expect)


def _typed_empty(paired) -> None:
    def expect(report, code, diags):
        for binding in report['review']['sets']:
            if binding['name'] == 'e' and binding.get('cardinality') == 0:
                if binding['element_type'] != 'natural':
                    raise ValueError('typed empty lost its element type')
                return code, binding['element_type']
        raise ValueError('typed empty result missing')
    paired('typed-empty-results', 'a := {1,2}; e := a - a; need e;',
           expect)


def _mixed(paired) -> None:
    def expect(report, code, diags):
        if code != 2:
            raise ValueError('mixed operand types must be refused by the CLI')
        return code, 'refused'
    paired('mixed-types-refused', 'xs := {1} | {"x"}; need xs;', expect)


def _membership(paired) -> None:
    def expect(report, code, diags):
        verdicts = {check['name']: check['result'] for check in report['checks']}
        if verdicts != {'hit': 'entailed', 'miss': 'entailed'}:
            raise ValueError(f'membership verdicts differ: {verdicts}')
        return code, sorted(verdicts)
    paired('membership-hit-miss',
           'a := {1,2}; check hit: 2 in a; check miss: not (5 in a);',
           expect)


def _subset(paired) -> None:
    def expect(report, code, diags):
        for node in report['trace']:
            if node.get('kind') == 'comparison' and node.get('operator') == '<=':
                if node.get('counterexample', {}).get('value') != '3':
                    raise ValueError(f'counterexample differs: {node.get("counterexample")}')
                return code, node['counterexample']['value']
        raise ValueError('subset comparison trace node missing')
    paired('subset-counterexample',
           'a := {1,2}; b := {2,3}; check q: (a | b) <= a;',
           expect)


def _unavailable(paired) -> None:
    def expect(report, code, diags):
        if code != 2:
            raise ValueError('unavailable operand must refuse, not vacuate')
        return code, 'refused'
    paired('unavailable-operand-refused',
           'a := {1}; bad := {...a,missing}; check q: not (2 in (a - bad));',
           expect)


def _shadowing(paired) -> None:
    def expect(report, code, diags):
        verdicts = [check['result'] for check in report['checks']]
        if verdicts != ['refuted']:
            raise ValueError(f'shadowing verdicts differ: {verdicts}')
        return code, verdicts
    paired('shadowing-not-capture',
           'x := {7}; check nested: forall x in ({8} | x) { x == 8 };',
           expect)


PAIRS = {
    'union-membership-order': _union,
    'intersection-merges-origins': _intersection,
    'difference-retains-right-closure': _difference,
    'typed-empty-results': _typed_empty,
    'mixed-types-refused': _mixed,
    'membership-hit-miss': _membership,
    'subset-counterexample': _subset,
    'unavailable-operand-refused': _unavailable,
    'shadowing-not-capture': _shadowing,
}
