"""Exercise nominal API boundaries with the actual admitted Rust compiler."""
from __future__ import annotations

import json
from pathlib import Path

from evidence import digest, run_logged, write_new

CASES = [
    ('checked-construction', None, '''use weft_domain::{SourceSpan, InvariantError};
pub fn checked() -> Result<SourceSpan, InvariantError> { SourceSpan::checked("x", 0, 1) }
'''),
    ('cross-kind', 'E0308', '''use weft_domain::{DeclId, NodeId};
pub fn wrong(value: DeclId) -> NodeId { value }
'''),
    ('raw-conversion', 'E0277', '''use weft_domain::NodeId;
pub fn wrong(value: usize) -> NodeId { value.into() }
'''),
    ('private-span', 'E0451', '''use weft_domain::SourceSpan;
pub fn wrong() -> SourceSpan { SourceSpan { start: 0, end: 1 } }
'''),
    ('requested-is-not-identity', 'E0308', '''use weft_domain::{BindingRequest, IdentityValue};
pub fn wrong(value: BindingRequest) -> IdentityValue { value }
'''),
]


def qualify(root: Path, evidence: Path, library: Path, target: str) -> list[dict]:
    directory = evidence / 'nominal-cases'
    directory.mkdir()
    output = directory / 'output'
    output.mkdir()
    records = []
    for name, expected, body in CASES:
        source = directory / f'{name}.rs'
        source.write_text('#![forbid(unsafe_code)]\n' + body)
        result = run_logged([
            'rustc', '--edition=2024', '--crate-type=lib', '--crate-name', name.replace('-', '_'),
            '--emit=metadata', '--error-format=json', '--target', target,
            '--extern', f'weft_domain={library}', '-L', f'dependency={library.parent}',
            '--out-dir', str(output), str(source),
        ], root, directory, name, timeout=60)
        messages = [json.loads(line) for line in (directory / f'{name}.stderr').read_text().splitlines()
                    if line.startswith('{')]
        codes = [message['code']['code'] for message in messages
                 if message.get('level') == 'error' and message.get('code')]
        passed = result['exit_code'] == 0 if expected is None else (
            result['exit_code'] != 0 and result['exit_code'] is not None
            and expected in codes and all(code == expected for code in codes))
        record = {'id': name, 'expected_error': expected, 'diagnostic_codes': codes,
                  'source_sha256': digest(source), 'passed': passed, 'command': result}
        records.append(record)
        write_new(directory / f'{name}.result.json', record)
        if not passed:
            raise ValueError(f'nominal compiler calibration failed: {name}')
    return records
