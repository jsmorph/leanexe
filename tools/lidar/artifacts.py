"""Identity checks for an already checked lidar bundle (not a proof checker)."""
import hashlib
import json


def checked_artifacts(bundle):
    """Load once, identify the checked bytes, and execute those same bytes."""
    receipt = json.loads((bundle / 'checked.json').read_text())
    if receipt.get('schema') != 1:
        raise ValueError('unsupported lidar proof receipt')
    mode = receipt.get('mode', 'cardinal')  # Original schema-1 cardinal receipts omit mode.
    if mode not in ('cardinal', 'oblique', 'interval'):
        raise ValueError('unsupported lidar mode')
    names = ['scan.wgsl', 'summary.wgsl', 'controller.wasm']
    if mode == 'interval':
        names.append('inner.wgsl')
    if set(receipt['artifacts']) != set(names):
        raise ValueError('unexpected artifact set in proof receipt')
    artifacts = {name: (bundle / name).read_bytes() for name in names}
    for name, data in artifacts.items():
        if hashlib.sha256(data).hexdigest() != receipt['artifacts'].get(name):
            raise ValueError(f'{name} differs from the checked artifact; rebuild the bundle')
    return artifacts
