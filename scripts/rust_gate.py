"""Host orchestration for isolated Rust preparation and local runtime qualification."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import uuid

from contracts import reconcile
from evidence import capture_sources, digest, manifest, process_env, require_success, run_logged


def proof_prerequisite(root: Path, attempt: Path) -> dict:
    record = json.loads((root / 'qualification/finite-calculus.json').read_text())
    receipt = Path(record['receipt'])
    if record['status'] != 'pass' or digest(receipt) != record['receipt_sha256']:
        raise ValueError('finite calculus prerequisite is absent or its receipt changed')
    initial = json.loads(receipt.read_text())
    reference = json.loads((root / 'qualification/reference-calibration.json').read_text())
    if (reference['status'] != 'pass'
            or reference['calculus_prerequisite']['sha256'] != digest(root / 'qualification/finite-calculus.json')):
        raise ValueError('reference calibration does not bind the first calculus checkpoint')
    receipt = Path(reference['receipt'])
    if digest(receipt) != reference['receipt_sha256']:
        raise ValueError('qualified executable reference receipt changed')
    proof = json.loads(receipt.read_text())
    producer = proof['result']['producer']
    if (initial['status'] != 'pass' or proof['status'] != 'pass'
            or producer['status'] != 'pass' or producer['skipped']):
        raise ValueError('finite calculus prerequisite is incomplete')
    original = initial['result']['producer']['formal_source']
    for path, expected in original.items():
        if path != 'formal/Weft/Reference.lean' and producer['formal_source'].get(path) != expected:
            raise ValueError(f'calculus body changed after proof-first admission: {path}')
    if producer['formal_source'] != manifest(root, ['formal']):
        raise ValueError('formal source changed after the qualified finite calculus')
    contract = reconcile(root)
    if (contract['manifest_sha256'] != proof['contract']['manifest_sha256']
            or contract['theorem_ids'] != proof['contract']['theorem_ids']
            or contract['audit_policy_sha256'] != proof['contract']['audit_policy_sha256']):
        raise ValueError('calculus authority or obligations changed')
    artifacts = {}
    for name, key in [('weftref', 'reference_binary_sha256'),
                      ('weftfiniteref', 'finite_reference_binary_sha256')]:
        source = receipt.parent / name
        if digest(source) != producer[key]:
            raise ValueError(f'qualified reference artifact changed: {name}')
        target = attempt / name
        shutil.copy2(source, target)
        artifacts[name] = digest(target)
    return {'receipt': str(receipt), 'sha256': reference['receipt_sha256'],
            'initial_calculus_receipt': record['receipt'], 'initial_calculus_sha256': record['receipt_sha256'],
            'formal_source': producer['formal_source'], 'artifacts': artifacts,
            'image_id': proof['result']['image_id'],
            'scope': 'exact calculus bodies and authority; reference protocol separately requalified without relabelling the first proof checkpoint'}


def run(root: Path, attempt: Path, image: str, prepare: bool) -> dict:
    inputs = ['Cargo.toml', 'LICENSE', 'crates', 'tools/weft-quality', 'scripts/evidence.py',
              'scripts/rust_gate.py', 'scripts/prepare_rust.py', 'toolchains.lock.json', 'compose.yaml',
              'qualification/engineering-adoption.json', 'qualification/finite-calculus.json',
              'qualification/reference-calibration.json']
    if (root / 'Cargo.lock').exists():
        inputs.append('Cargo.lock')
    proof = proof_prerequisite(root, attempt)
    if proof['image_id'] != image:
        raise ValueError('Rust and calculus tool-image identities differ')
    if not prepare:
        inputs += ['scripts/run_rust.py', 'scripts/rust_smoke.py', 'scripts/nominal_cases.py',
                   'scripts/rust_differential.py', 'scripts/rust_scenarios.py', 'scripts/lint_cases.py',
                   'scripts/algebra_differential.py',
                   'examples', 'spec', 'docs/implementation-profile.md', 'docs/rust-implementation.md',
                   'docker/Dockerfile.runtime']
        if not (root / 'Cargo.lock').is_file() or not (root / 'tools/weft-quality/Cargo.lock').is_file():
            raise ValueError('offline lock preparation must precede Rust qualification')
    before = manifest(root, inputs)
    capture_sources(root, list(before), attempt / 'rust-source.zip')
    code = manifest(root, ['Cargo.toml', 'crates'] + (['Cargo.lock'] if (root / 'Cargo.lock').exists() else []))
    source_digest = hashlib.sha256(json.dumps(code, sort_keys=True, separators=(',', ':')).encode()).hexdigest()
    name = f'weft-rust-{uuid.uuid4().hex}'
    script = 'scripts/prepare_rust.py' if prepare else 'scripts/run_rust.py'
    label = 'compose-prepare' if prepare else 'compose-rust'
    try:
        require_success(run_logged([
            'docker', 'compose', 'run', '--rm', '--name', name,
            '-e', f'WEFT_SOURCE_SHA256={source_digest}',
            'qualify', 'timeout', '--signal=TERM', '--kill-after=30', '1800', 'python3', script,
        ], root, attempt, label,
            env=process_env(WEFT_TOOL_IMAGE=image, WEFT_ATTEMPT=str(attempt)), timeout=1900))
    finally:
        subprocess.run(['docker', 'rm', '--force', name], capture_output=True, check=False)
    if before != manifest(root, inputs):
        raise ValueError('Rust inputs changed during qualification')
    result = json.loads((attempt / ('prepare-results.json' if prepare else 'rust-results.json')).read_text())
    expected = 'prepared' if prepare else 'pass'
    if result['status'] != expected:
        raise ValueError('Rust producer did not complete its stated scope')
    return {'image_id': image, 'source_manifest': before, 'binary_source_sha256': source_digest,
            'proof_prerequisite': proof, 'producer': result}
