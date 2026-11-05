"""Generate offline locks and rustfmt output in an owned copy, never the source mount."""
from __future__ import annotations

import json
from pathlib import Path
import shutil
import tempfile
import zipfile

from evidence import digest, manifest, require_success, run_logged, write_new

ROOT = Path('/work/weft')
EVIDENCE = Path('/evidence')
CACHE = Path('/cache/target/rust-1.98.0')
INPUTS = ['Cargo.toml', 'crates', 'tools/weft-quality']


def main() -> int:
    result = {'schema_version': 1, 'status': 'fail', 'scope': 'format-and-lock-preparation-only'}
    owned = None
    try:
        inputs = manifest(ROOT, INPUTS)
        CACHE.mkdir(parents=True, exist_ok=True)
        owned = Path(tempfile.mkdtemp(prefix='prepare-', dir=CACHE))
        source = owned / 'source'
        source.mkdir()
        shutil.copy2(ROOT / 'Cargo.toml', source / 'Cargo.toml')
        shutil.copytree(ROOT / 'crates', source / 'crates')
        shutil.copytree(ROOT / 'tools/weft-quality', source / 'tools/weft-quality',
                        ignore=shutil.ignore_patterns('target'))
        if (ROOT / 'Cargo.lock').exists():
            shutil.copy2(ROOT / 'Cargo.lock', source / 'Cargo.lock')
        for label, workspace in [('workspace', source), ('policy', source / 'tools/weft-quality')]:
            if (workspace / 'Cargo.lock').exists():
                command = ['cargo', 'metadata', '--locked', '--offline', '--no-deps', '--format-version=1']
            else:
                command = ['cargo', 'generate-lockfile', '--offline']
            require_success(run_logged(command, workspace, EVIDENCE, f'{label}-lock'))
            require_success(run_logged(['cargo', 'fmt', '--all'], workspace,
                                       EVIDENCE, f'{label}-format'))
        generated = sorted([path for path in source.rglob('*')
                            if path.is_file() and (path.suffix == '.rs' or path.name == 'Cargo.lock')])
        output = EVIDENCE / 'prepared-rust.zip'
        with zipfile.ZipFile(output, 'x', compression=zipfile.ZIP_DEFLATED) as bundle:
            for path in generated:
                bundle.write(path, str(path.relative_to(source)))
        if inputs != manifest(ROOT, INPUTS):
            raise ValueError('source changed during isolated Rust preparation')
        result.update(status='prepared', source_manifest=inputs,
                      output={'path': output.name, 'sha256': digest(output)},
                      generated={str(path.relative_to(source)): digest(path) for path in generated})
    except (OSError, ValueError, KeyError) as error:
        result['error'] = f'{type(error).__name__}: {error}'
    finally:
        if owned is not None:
            shutil.rmtree(owned)
    write_new(EVIDENCE / 'prepare-results.json', result)
    print(json.dumps(result, indent=2))
    return 0 if result['status'] == 'prepared' else 1


if __name__ == '__main__':
    raise SystemExit(main())
