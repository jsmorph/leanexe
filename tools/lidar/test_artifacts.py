"""Fault injection at the checked-bundle/runtime boundary."""
import hashlib
import json
from pathlib import Path
import tempfile
import unittest
from artifacts import checked_artifacts


class ArtifactIdentity(unittest.TestCase):
    def test_changed_files_and_missing_receipt(self):
        with tempfile.TemporaryDirectory() as temp:
            bundle = Path(temp)
            files = {'scan.wgsl': b'scan', 'summary.wgsl': b'summary',
                     'controller.wasm': b'\0asm'}
            receipt = {'schema': 1, 'artifacts': {
                name: hashlib.sha256(data).hexdigest() for name, data in files.items()}}
            for name, data in files.items():
                (bundle / name).write_bytes(data)
            with self.assertRaises(FileNotFoundError):
                checked_artifacts(bundle)
            (bundle / 'checked.json').write_text(json.dumps(receipt))
            self.assertEqual(checked_artifacts(bundle), files)
            for name, data in files.items():
                with self.subTest(name=name):
                    (bundle / name).write_bytes(data + b'changed')
                    with self.assertRaisesRegex(ValueError, 'differs from the checked artifact'):
                        checked_artifacts(bundle)
                    (bundle / name).write_bytes(data)


if __name__ == '__main__':
    unittest.main()
