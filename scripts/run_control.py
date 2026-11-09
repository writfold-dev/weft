"""Qualify the Weft control client against the owner-pinned writfold binary.

Runs inside the admitted Compose image. The wrapper has already verified and
copied the pinned artifacts into the evidence directory. This producer checks
the vendored contract archive byte-for-byte, runs the client unit suites, then
exercises a real stdio control session and the shipped `weft control` command,
including its refusal path. It qualifies transport control only: no corpus,
assessment, retention or effect service is claimed.
"""
from __future__ import annotations

import hashlib
import json
import tarfile
from pathlib import Path

from evidence import digest, process_env, require_success, run_logged, write_new

ROOT = Path('/work/weft')
EVIDENCE = Path('/evidence')
ARCHIVE_SHA256 = '1b4049c481eff17a29f1d4e1cc81918f6c58014800937ee295b792105b7fe626'
CONTRACT_SHA256 = '0baf69b21f1051ee620ca89ba4ec659605c0cf3ddc4ae82a7a9ad8eaf1d9ac3f'
BINARY_SHA256 = '91a1924f5bae025a131bda99ea047c30adcc404d96429abf70956a7757230f4d'
MEMBERS = ('contract.json', 'methods.json', 'trial-methods.json', 'request.schema.json',
           'response.schema.json', 'citation-binding.schema.json', 'vectors.json')


def member_text(archive: Path, name: str) -> bytes:
    with tarfile.open(archive, 'r:gz') as bundle:
        member = bundle.extractfile(name)
        if member is None:
            raise ValueError(f'contract member absent: {name}')
        return member.read()


def verify_vendored_contract() -> dict:
    archive = ROOT / 'contracts/writfold-agent-1/writfold-agent-contract.tar.gz'
    if digest(archive) != ARCHIVE_SHA256:
        raise ValueError('vendored contract archive bytes changed')
    members = {name: hashlib.sha256(member_text(archive, name)).hexdigest() for name in MEMBERS}
    if members['contract.json'] != CONTRACT_SHA256:
        raise ValueError('vendored contract.json digest changed')
    contract = json.loads(member_text(archive, 'contract.json'))
    for entry in contract['files']:
        if members.get(entry['path']) != entry['sha256']:
            raise ValueError(f"vendored member disagrees with the root contract: {entry['path']}")
    if (contract['profile'] != 'writfold.agent/1'
            or contract['implementation_scope'] != 'transport-control-only'
            or contract['implemented_methods'] != ['initialize', 'shutdown', 'trial/show',
                                                   'trial/retain', 'trial/prepare']
            or contract['advertised_capabilities'] != ['notifications', 'writfold.trial/1']):
        raise ValueError('vendored contract is not the pinned control profile')
    return {'archive_sha256': ARCHIVE_SHA256, 'members': members,
            'profile': contract['profile'], 'scope': contract['implementation_scope']}


def main() -> int:
    result = {'schema_version': 1, 'status': 'fail',
              'scope': 'weft-control-client-transport-only',
              'skipped': [], 'external_release': 'blocked by real Writfold data services'}
    try:
        result['vendored_contract'] = verify_vendored_contract()
        binary = EVIDENCE / 'writfold'
        observed = digest(binary)
        if observed != BINARY_SHA256:
            raise ValueError('supplied writfold executable is not the pinned artifact')
        result['peer_binary_sha256'] = observed
        require_success(run_logged(['file', str(binary)], ROOT, EVIDENCE, 'peer-file'))
        require_success(run_logged(
            ['cargo', 'test', '--locked', '--offline', '-p', 'weft-wire', '-p', 'weft-writfold'],
            ROOT, EVIDENCE, 'client-unit-tests', timeout=600))
        record = run_logged(
            ['cargo', 'test', '--locked', '--offline', '-p', 'weft-writfold', '--test', 'control'],
            ROOT, EVIDENCE, 'client-live-session',
            env=process_env(WRITFOLD_CONTROL_BIN=str(binary)), timeout=300)
        require_success(record)
        if '1 passed' not in (EVIDENCE / 'client-live-session.stdout').read_text():
            raise ValueError('live control session test did not run')
        cli = ['cargo', 'run', '--quiet', '--locked', '--offline', '-p', 'weft-cli', '--']
        session = run_logged([*cli, 'control', str(binary), '--expect-sha256', BINARY_SHA256],
                             ROOT, EVIDENCE, 'cli-control-session', timeout=300)
        require_success(session)
        envelope = json.loads((EVIDENCE / 'cli-control-session.stdout').read_text())
        if (envelope['schema'] != 'weft.control/1' or envelope['execution'] != 'complete'
                or envelope['session']['contract_sha256'] != CONTRACT_SHA256
                or envelope['session']['initialize_generation'] != 1
                or envelope['session']['shutdown_generation'] != 2
                or envelope['writfold_grounded'] is not False
                or envelope['effect_authority'] is not False):
            raise ValueError('control session envelope overstated or misrecorded its scope')
        original = binary.read_bytes()
        tampered = EVIDENCE / 'writfold-tampered'
        tampered.write_bytes(bytes([original[0] ^ 1]) + original[1:])
        refusal = run_logged([*cli, 'control', str(tampered), '--expect-sha256', BINARY_SHA256],
                             ROOT, EVIDENCE, 'cli-control-refusal', timeout=300)
        if refusal['exit_code'] != 2:
            raise ValueError('a digest-mismatched peer was not refused before spawning')
        refused = json.loads((EVIDENCE / 'cli-control-refusal.stdout').read_text())
        if refused['execution'] != 'failed' or refused['writfold_grounded'] is not False:
            raise ValueError('refusal envelope overstated its scope')
        result['status'] = 'pass'
    except (OSError, ValueError, KeyError, TypeError) as error:
        result['error'] = f'{type(error).__name__}: {error}'
    write_new(EVIDENCE / 'control-results.json', result)
    print(json.dumps(result, indent=2))
    return 0 if result['status'] == 'pass' else 1


if __name__ == '__main__':
    raise SystemExit(main())
