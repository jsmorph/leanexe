"""Identity checks for an already checked lidar bundle (not a proof checker)."""
import hashlib
import json


def checked_artifacts(bundle):
    """Load once, identify the checked bytes, and execute those same bytes."""
    receipt = json.loads((bundle / 'checked.json').read_text())
    if receipt.get('schema') != 1:
        raise ValueError('unsupported lidar proof receipt')
    artifacts = {name: (bundle / name).read_bytes()
                 for name in ['scan.wgsl', 'summary.wgsl', 'controller.wasm']}
    for name, data in artifacts.items():
        if hashlib.sha256(data).hexdigest() != receipt['artifacts'].get(name):
            raise ValueError(f'{name} differs from the checked artifact; rebuild the bundle')
    return artifacts
