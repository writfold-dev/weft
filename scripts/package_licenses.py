"""Collect exact project and third-party notices from the qualified Cargo closure."""
from __future__ import annotations

import json
from pathlib import Path
import zipfile

from evidence import digest, write_new

EVIDENCE = Path('/evidence')
ROOT = Path(__file__).resolve().parents[1]


def main() -> None:
    packages = {}
    for name in ('workspace-metadata.json', 'policy-metadata.json'):
        for package in json.loads((EVIDENCE / name).read_text())['packages']:
            packages[(package['name'], package['version'])] = package
    records = []
    archive = EVIDENCE / 'third-party-licenses.zip'
    with zipfile.ZipFile(archive, 'x', compression=zipfile.ZIP_DEFLATED) as bundle:
        project_license = ROOT / 'LICENSE'
        if project_license.is_symlink() or not project_license.is_file():
            raise ValueError('project MIT license must be a retained regular file')
        project_member = 'licenses/weft/LICENSE'
        bundle.write(project_license, project_member)
        project_notice = {'member': project_member, 'sha256': digest(project_license)}
        for key, package in sorted(packages.items()):
            if package['source'] is None:
                manifest = Path(package['manifest_path']).resolve()
                if not manifest.is_relative_to(ROOT) or package.get('license') != 'MIT':
                    raise ValueError(f'unadmitted project license metadata: {key}')
                records.append({'name': key[0], 'version': key[1], 'license': 'MIT',
                                'scope': 'project-owned MIT package; repository visibility is separate',
                                'source': None, 'files': [project_notice]})
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
