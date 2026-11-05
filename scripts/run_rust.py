"""Qualify the exact local Rust compiler/interpreter/report binary, not Writfold integration."""
from __future__ import annotations

import json
import os
from pathlib import Path
import re
import shutil

from evidence import digest, manifest, process_env, require_success, run_logged, write_new
from lint_cases import FORBIDDEN_FLAGS, calibrate
from nominal_cases import qualify as nominal_qualify
from rust_smoke import qualify as smoke_qualify

ROOT = Path('/work/weft')
EVIDENCE = Path('/evidence')
TRIPLE = 'x86_64-unknown-linux-musl'


def cargo(args: list[str], label: str, target: Path, *, policy: bool = False) -> dict:
    command = ['cargo', args[0], '--locked', '--offline']
    if policy:
        command += ['--manifest-path', 'tools/weft-quality/Cargo.toml']
    command += args[1:]
    result = run_logged(command, ROOT, EVIDENCE, label,
                        env=process_env(CARGO_TARGET_DIR=str(target)), timeout=600)
    require_success(result)
    return result


def artifact_paths(path: Path) -> tuple[Path, Path]:
    messages = [json.loads(line) for line in path.read_text().splitlines() if line.startswith('{')]
    executables, libraries = [], []
    for message in messages:
        if message.get('reason') != 'compiler-artifact':
            continue
        target = message['target']['name']
        if target == 'weft' and message.get('executable'):
            executables.append(Path(message['executable']))
        if target == 'weft_domain':
            libraries += [Path(name) for name in message['filenames'] if name.endswith('.rlib')]
    if len(executables) != 1 or len(libraries) != 1:
        raise ValueError('build did not identify one real executable and one nominal domain library')
    return executables[0], libraries[0]


def dependencies() -> dict:
    packages = {}
    for label in ['workspace-metadata', 'policy-metadata']:
        metadata = json.loads((EVIDENCE / f'{label}.stdout').read_text())
        for package in metadata['packages']:
            key = (package['name'], package['version'])
            if not package.get('license') and not package.get('license_file'):
                raise ValueError(f'dependency license is unidentified: {key}')
            if any(marker in package['name'] for marker in ['openssl', 'native-tls', 'dolt']):
                raise ValueError(f'prohibited dependency: {key}')
            packages[key] = {'name': key[0], 'version': key[1], 'license': package.get('license'),
                             'license_file': package.get('license_file'), 'source': package.get('source')}
    return {'packages': [packages[key] for key in sorted(packages)],
            'workspace_lock_sha256': digest(ROOT / 'Cargo.lock'),
            'policy_lock_sha256': digest(ROOT / 'tools/weft-quality/Cargo.lock'),
            'advisory_snapshot': {'status': 'unavailable',
                                  'scope': 'No current advisory database is admitted to this offline qualification; no vulnerability-free claim.'}}


def main() -> int:
    result = {'schema_version': 1, 'status': 'fail', 'scope': 'weft-local-symbolic-runtime-only',
              'skipped': [], 'external_release': 'blocked by real Writfold owner prerequisites'}
    try:
        identity = os.environ.get('WEFT_SOURCE_SHA256', '')
        if not re.fullmatch('[0-9a-f]{64}', identity):
            raise ValueError('qualified binary source identity is absent')
        target = Path('/cache/target/rust-1.98.0') / identity
        policy_target = target / 'policy'
        result['source_manifest'] = manifest(ROOT, ['Cargo.toml', 'Cargo.lock', 'crates', 'tools/weft-quality'])
        for policy, prefix, cache in [(False, 'workspace', target), (True, 'policy', policy_target)]:
            # cargo fmt is a rustfmt driver and does not accept Cargo lock flags.
            command = ['cargo', 'fmt', '--all']
            if policy:
                command += ['--manifest-path', 'tools/weft-quality/Cargo.toml']
            command += ['--', '--check']
            require_success(run_logged(command, ROOT, EVIDENCE, f'{prefix}-format'))
            cargo(['metadata', '--format-version=1'], f'{prefix}-metadata', cache, policy=policy)
            cargo(['test', '--workspace', '--all-targets'], f'{prefix}-tests', cache, policy=policy)
            cargo(['clippy', '--workspace', '--all-targets', '--', '-D', 'warnings', *FORBIDDEN_FLAGS],
                  f'{prefix}-clippy', cache, policy=policy)
        result['dependencies'] = dependencies()
        for prefix in ['workspace', 'policy']:
            cargo(['run', '--quiet', '--', '--metadata', str(EVIDENCE / f'{prefix}-metadata.stdout'),
                   '--nominal', 'IdentityValue'], f'{prefix}-ast-policy', policy_target, policy=True)
        result['compiler_lint_calibration'] = calibrate(
            ROOT, EVIDENCE, target, policy_target / 'debug/weft-quality')
        if result['compiler_lint_calibration']['status'] != 'pass':
            raise ValueError('compiler/macro operation calibration failed')
        cargo(['build', '--release', '--target', TRIPLE, '--package', 'weft-cli', '--message-format=json'],
              'musl-build', target)
        executable, library = artifact_paths(EVIDENCE / 'musl-build.stdout')
        binary = EVIDENCE / 'weft'
        shutil.copy2(executable, binary)
        require_success(run_logged(['file', str(binary)], ROOT, EVIDENCE, 'elf-file'))
        require_success(run_logged(['readelf', '-l', '-d', str(binary)], ROOT, EVIDENCE, 'elf-linkage'))
        linkage = (EVIDENCE / 'elf-linkage.stdout').read_text()
        if 'INTERP' in linkage or 'NEEDED' in linkage:
            raise ValueError('delivered executable is not independent of a dynamic loader/library set')
        require_success(run_logged([str(binary), '--version'], ROOT, EVIDENCE, 'binary-version',
                                   env={'PATH': '/no-toolchain'}))
        result['nominal_cases'] = nominal_qualify(ROOT, EVIDENCE, library, TRIPLE)
        result['smoke'] = smoke_qualify(ROOT, EVIDENCE, binary, EVIDENCE / 'weftref', EVIDENCE / 'weftfiniteref')
        result['binary_sha256'] = digest(binary)
        result['binary_source_sha256'] = identity
        result['status'] = 'pass'
    except (OSError, ValueError, KeyError, TypeError) as error:
        result['error'] = f'{type(error).__name__}: {error}'
    write_new(EVIDENCE / 'rust-results.json', result)
    print(json.dumps(result, indent=2))
    return 0 if result['status'] == 'pass' else 1


if __name__ == '__main__':
    raise SystemExit(main())
