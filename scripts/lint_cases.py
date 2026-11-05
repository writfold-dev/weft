"""Calibrate mandatory, type-resolved operation lints inside the offline tool image.

AST operation checks are intentionally syntactic. This producer binds its fixtures,
commands, and compiler diagnostics; callers must also run FORBIDDEN_FLAGS against
the exact qualified workspace and tool sources, including their test targets.
"""
from __future__ import annotations

import json
from pathlib import Path
import tempfile

from evidence import capture_sources, digest, manifest, run_logged, write_new

FORBIDDEN_FLAGS = [
    '-F', 'unsafe_code',
    '-F', 'clippy::unwrap_used', '-F', 'clippy::expect_used',
    '-F', 'clippy::panic', '-F', 'clippy::todo',
    '-F', 'clippy::unimplemented', '-F', 'clippy::unreachable',
]
MANIFEST = '''[package]
name = "lint-fixture"
version = "0.0.0"
edition = "2024"
publish = false

[workspace]
'''
LOCK = '''version = 4

[[package]]
name = "lint-fixture"
version = "0.0.0"
'''


def fixtures() -> list[dict]:
    cases = []
    operations = [
        ('option-unwrap', 'let x: Option<u8> = std::env::args().next().map(|_| 1); x.unwrap();', 'unwrap_used'),
        ('result-unwrap', 'let x: Result<u8, ()> = Err(()); x.unwrap();', 'unwrap_used'),
        ('option-expect', 'let x: Option<u8> = None; x.expect("value");', 'expect_used'),
        ('result-expect', 'let x: Result<u8, ()> = Err(()); x.expect("value");', 'expect_used'),
        ('result-unwrap-err', 'let x: Result<(), u8> = Ok(()); x.unwrap_err();', 'unwrap_used'),
        ('result-expect-err', 'let x: Result<(), u8> = Ok(()); x.expect_err("error");', 'expect_used'),
        ('ufcs-unwrap', 'let x: Option<u8> = None; Option::unwrap(x);', 'unwrap_used'),
        ('ufcs-expect', 'let x: Result<u8, ()> = Err(()); Result::expect(x, "value");', 'expect_used'),
        ('macro-unwrap', 'macro_rules! call { ($x:expr) => { $x.unwrap() }; } let x: Option<u8> = None; call!(x);', 'unwrap_used'),
        ('macro-expect', 'macro_rules! call { ($x:expr) => { $x.expect("value") }; } let x: Option<u8> = None; call!(x);', 'expect_used'),
        ('panic', 'panic!("stop");', 'panic'),
        ('todo', 'todo!();', 'todo'),
        ('unimplemented', 'unimplemented!();', 'unimplemented'),
        ('unreachable', 'unreachable!();', 'unreachable'),
    ]
    for name, body, lint in operations:
        cases.append({'name': name, 'source': '#![forbid(unsafe_code)]\nfn main() { ' + body + ' }\n',
                      'diagnostic': f'clippy::{lint}', 'override': False,
                      'macro_policy': {'macro-unwrap': 'WQ203', 'macro-expect': 'WQ204'}.get(name)})
    for lint, method in [('unwrap_used', 'unwrap()'), ('expect_used', 'expect("value")')]:
        for level in ['allow', 'warn', 'expect']:
            cases.append({
                'name': f'override-{level}-{lint}',
                'source': f'#![forbid(unsafe_code)]\n#![{level}(clippy::{lint})]\n'
                          f'fn main() {{ let x: Option<u8> = None; x.{method}; }}\n',
                'diagnostic': f'clippy::{lint}', 'override': True,
            })
    cases += [
        {'name': 'expanded-unsafe', 'diagnostic': 'unsafe_code', 'override': False,
         'source': '#![forbid(unsafe_code)]\n'
                   'macro_rules! block { ($kind:tt) => { $kind {} }; }\n'
                   'fn main() { block!(unsafe); }\n'},
        {'name': 'custom-fallible-expect', 'diagnostic': None, 'override': False,
         'source': '#![forbid(unsafe_code)]\n'
                   'struct Cursor;\n'
                   'impl Cursor {\n'
                   '    fn expect(&self, _: &str) -> Result<(), ()> { Ok(()) }\n'
                   '    fn unwrap(&self) -> Result<(), ()> { Ok(()) }\n'
                   '}\n'
                   'fn main() -> Result<(), ()> {\n'
                   '    let cursor = Cursor;\n'
                   '    cursor.expect("token")?;\n'
                   '    Cursor::expect(&cursor, "token")?;\n'
                   '    cursor.unwrap()?;\n'
                   '    Ok(())\n'
                   '}\n'},
        {'name': 'opaque-unsafe-token', 'diagnostic': None, 'override': False,
         'source': '#![forbid(unsafe_code)]\n'
                   'macro_rules! token { (unsafe) => { () }; }\n'
                   'fn main() { token!(unsafe); }\n'},
    ]
    return cases


def diagnostics(stdout: Path) -> list[dict]:
    messages = []
    for line in stdout.read_text().splitlines():
        if not line.strip():
            continue
        record = json.loads(line)
        if record.get('reason') == 'compiler-message':
            message = record['message']
            if message['level'] == 'error':
                messages.append(message)
    return messages


def intended(message: dict, case: dict, source: Path) -> bool:
    code = (message.get('code') or {}).get('code')
    matches = code == case['diagnostic']
    if case['override'] and code == 'E0453':
        matches = case['diagnostic'] in (message.get('rendered') or message['message'])
    spans = message.get('spans', [])
    bound = any(span.get('is_primary') and
                (source / span['file_name']).resolve() == (source / 'src/main.rs').resolve()
                for span in spans)
    return matches and bound


def run_case(case: dict, source: Path, output: Path, evidence: Path, quality: Path) -> dict:
    command = run_logged([
        'cargo', 'clippy', '--offline', '--locked', '--all-targets',
        '--message-format=json', '--manifest-path', str(source / 'Cargo.toml'),
        '--target-dir', str(output), '--', *FORBIDDEN_FLAGS,
    ], source, evidence, case['name'])
    errors = diagnostics(evidence / f"{case['name']}.stdout")
    macro_check = None
    if case.get('macro_policy'):
        macro_check = run_logged([str(quality), '--crate', 'weft-quality', str(source / 'src/main.rs')],
                                 source, evidence, f'{case["name"]}-ast')
        report = json.loads((evidence / f'{case["name"]}-ast.stdout').read_text())
        findings = [finding for finding in report['report']['findings'] if finding['severity'] == 'error']
        compiler_valid = ((command['exit_code'] == 0 and not errors)
                          or (command['exit_code'] not in (0, None) and bool(errors)
                              and all(intended(error, case, source) for error in errors)))
        passed = (compiler_valid and macro_check['exit_code'] == 1 and bool(findings)
                  and all(finding['code'] == case['macro_policy'] and finding.get('span')
                          and Path(finding['path']).resolve() == (source / 'src/main.rs').resolve()
                          for finding in findings))
    elif case['diagnostic'] is None:
        passed = command['exit_code'] == 0 and not errors
    else:
        passed = (command['exit_code'] not in (0, None) and command['failure'] is None
                  and bool(errors) and all(intended(error, case, source) for error in errors))
    return {'name': case['name'], 'status': 'pass' if passed else 'fail',
            'expected_diagnostic': case['diagnostic'], 'override_attempt': case['override'],
            'source_manifest': manifest(source, ['Cargo.toml', 'Cargo.lock', 'src/main.rs']),
            'command': command, 'errors': errors, 'macro_check': macro_check,
            'macro_policy': case.get('macro_policy')}


def calibrate(root: Path, evidence: Path, target: Path, quality: Path) -> dict:
    """Require compiler-resolved checks and structural rejection of macro lint gaps.

    Run in the already admitted offline container. No dependency preparation or
    host/container launch occurs here. Only the unique TemporaryDirectory is
    removed; persistent evidence is exclusively created in a new child directory.
    """
    root, evidence, target = root.resolve(), evidence.resolve(), target.resolve()
    producer_inputs = ['scripts/lint_cases.py', 'scripts/evidence.py', 'tools/weft-quality']
    before = manifest(root, producer_inputs)
    logs = evidence / 'lint-calibration'
    logs.mkdir()
    target.mkdir(parents=True, exist_ok=True)
    result = {'schema_version': 1, 'status': 'fail', 'evidence': str(logs),
              'scope': 'compiler-and-macro-operation-policy-calibration', 'forbidden_flags': FORBIDDEN_FLAGS,
              'producer_sources': before, 'macro_checker_sha256': digest(quality), 'cases': []}
    try:
        with tempfile.TemporaryDirectory(prefix='lint-calibration-', dir=target) as temporary:
            owned = Path(temporary)
            cases = fixtures()
            for case in cases:
                source = owned / 'sources' / case['name']
                (source / 'src').mkdir(parents=True)
                (source / 'Cargo.toml').write_text(MANIFEST)
                (source / 'Cargo.lock').write_text(LOCK)
                (source / 'src/main.rs').write_text(case['source'])
            result['fixtures'] = capture_sources(owned, ['sources'], logs / 'fixtures.zip')
            for case in cases:
                source = owned / 'sources' / case['name']
                result['cases'].append(run_case(case, source, owned / 'output' / case['name'], logs, quality))
            after = manifest(owned, ['sources'])
            if after != result['fixtures']['sources']:
                raise ValueError('calibration fixtures changed while checking')
        if before != manifest(root, producer_inputs):
            raise ValueError('calibration producer sources changed while checking')
        if all(case['status'] == 'pass' for case in result['cases']):
            result['status'] = 'pass'
    except (OSError, ValueError, KeyError) as error:
        result['error'] = f'{type(error).__name__}: {error}'
    write_new(logs / 'results.json', result)
    return result
