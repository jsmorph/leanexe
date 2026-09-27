"""Regression checks for import safety and explicit Vulkan CLI startup."""
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

import cli

ROOT = Path(__file__).resolve().parents[2]
RUNNERS = ['run', 'run_oblique', 'run_interval', 'run_stream']


class CliStartup(unittest.TestCase):
    def test_imports_leave_embedding_process_and_environment_intact(self):
        for package in [False, True]:
            with self.subTest(package=package):
                modules = [('tools.lidar.' if package else '') + name for name in RUNNERS]
                source = (
                    'import importlib, os, sys; '
                    'sys.path.insert(0, "tools/lidar"); '
                    'before = dict(os.environ); '
                    f'[importlib.import_module(name) for name in {modules!r}]; '
                    'assert dict(os.environ) == before; print("import completed")'
                )
                env = dict(os.environ)
                env.pop('LEANEXE_LIDAR_CONFIGURED', None)
                result = subprocess.run([sys.executable, '-c', source], cwd=ROOT,
                                        env=env, capture_output=True, text=True, timeout=30)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertEqual(result.stdout.strip(), 'import completed')

    def test_restart_preserves_original_invocation_and_user_environment(self):
        invocations = [
            ['python', '-W', 'error', 'tools/lidar/run.py', '--output', 'a b.json'],
            ['python', '-X', 'dev', '-m', 'tools.lidar.run_stream', '--help'],
            ['python', '-c', 'from cli import configure_cli; configure_cli()', 'argument'],
        ]
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            (root/'build/lidar/vulkan').mkdir(parents=True)
            original_env = {'LD_LIBRARY_PATH': '/custom/libs', 'VK_DRIVER_FILES': '/custom/icd.json',
                            'XDG_RUNTIME_DIR': '/custom/runtime', 'XDG_CACHE_HOME': '/custom/cache'}
            for argv in invocations:
                with self.subTest(argv=argv), patch.object(cli, 'ROOT', root), \
                        patch.dict(os.environ, original_env, clear=True), \
                        patch.object(sys, 'orig_argv', argv), patch.object(os, 'execve') as execute:
                    cli.configure_cli()
                    executable, restarted, env = execute.call_args.args
                    self.assertEqual(executable, sys.executable)
                    self.assertEqual(restarted, [sys.executable, *argv[1:]])
                    self.assertEqual(env['LEANEXE_LIDAR_CONFIGURED'], '1')
                    self.assertTrue(env['LD_LIBRARY_PATH'].endswith(':/custom/libs'))
                    for key in ['VK_DRIVER_FILES', 'XDG_RUNTIME_DIR', 'XDG_CACHE_HOME']:
                        self.assertEqual(env[key], original_env[key])
                    self.assertEqual(dict(os.environ), original_env)
                    with patch.dict(os.environ, env, clear=True):
                        cli.configure_cli()
                    execute.assert_called_once()

    def test_no_local_vulkan_needs_no_restart(self):
        with tempfile.TemporaryDirectory() as temp, patch.object(cli, 'ROOT', Path(temp)), \
                patch.dict(os.environ, {}, clear=True), patch.object(os, 'execve') as execute:
            cli.configure_cli()
            execute.assert_not_called()

    def test_script_and_module_entry_points(self):
        for module in RUNNERS:
            for entry in [[f'tools/lidar/{module}.py'], ['-m', f'tools.lidar.{module}']]:
                with self.subTest(entry=entry):
                    env = dict(os.environ)
                    env.pop('LEANEXE_LIDAR_CONFIGURED', None)
                    result = subprocess.run([sys.executable, '-W', 'ignore', *entry, '--help'],
                                            cwd=ROOT, env=env, capture_output=True, text=True, timeout=30)
                    self.assertEqual(result.returncode, 0, result.stderr)
                    self.assertIn('usage:', result.stdout)


if __name__ == '__main__':
    unittest.main()
