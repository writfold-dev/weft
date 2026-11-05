"""Collect exact third-party notices from the qualified offline Cargo closure."""
from __future__ import annotations

import json
from pathlib import Path
import zipfile

from evidence import digest, write_new

EVIDENCE = Path('/evidence')


def main() -> None:
    packages = {}
    for name in ('workspace-metadata.json', 'policy-metadata.json'):
        for package in json.loads((EVIDENCE / name).read_text())['packages']:
            packages[(package['name'], package['version'])] = package
    records = []
    archive = EVIDENCE / 'third-party-licenses.zip'
    with zipfile.ZipFile(archive, 'x', compression=zipfile.ZIP_DEFLATED) as bundle:
        for key, package in sorted(packages.items()):
            if package['source'] is None:
                records.append({'name': key[0], 'version': key[1], 'license': package.get('license'),
                                'scope': 'project-owned private package; no public license grant'})
                continue
            root = Path(package['manifest_path']).parent
            candidates = {path for path in root.iterdir() if path.is_file()
                          and path.name.upper().startswith(('LICENSE', 'LICENCE', 'COPYING', 'NOTICE'))}
            if package.get('license_file'):
                candidates.add(root / package['license_file'])
            if not candidates:
                raise ValueError(f'no actual license text found for {key}')
            files = []
            for path in sorted(candidates):
                if path.is_symlink() or not path.resolve().is_relative_to(root.resolve()):
                    raise ValueError(f'license source escapes its qualified package: {path}')
                if path.stat().st_size > 1_048_576:
                    raise ValueError(f'license source unexpectedly large: {path}')
                member = f'licenses/{key[0]}-{key[1]}/{path.relative_to(root)}'
                bundle.write(path, member)
                files.append({'member': member, 'sha256': digest(path)})
            records.append({'name': key[0], 'version': key[1], 'license': package.get('license'),
                            'source': package['source'], 'files': files})
    write_new(EVIDENCE / 'third-party-licenses.json', {'schema_version': 1, 'packages': records,
              'archive_sha256': digest(archive),
              'scope': 'Complete qualified workspace/tool dependency notice inventory; includes test/build-only dependencies, not a claim they all ship in the executable.'})
    print(json.dumps({'packages': len(records), 'archive_sha256': digest(archive)}))


if __name__ == '__main__':
    main()
