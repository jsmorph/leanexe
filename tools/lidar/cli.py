"""Optional local Vulkan setup, explicitly invoked by demonstration CLIs."""
import os
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]


def configure_cli():
    """Restart this CLI once so the dynamic loader sees the local Vulkan libs.

    Library imports never call this. Embedders should set their GPU environment
    before starting Python instead of restarting a process they do not own.
    """
    vulkan = ROOT / 'build/lidar/vulkan'
    if not vulkan.exists() or os.environ.get('LEANEXE_LIDAR_CONFIGURED'):
        return
    env = dict(os.environ, LEANEXE_LIDAR_CONFIGURED='1')
    env['LD_LIBRARY_PATH'] = str(vulkan / 'usr/lib/x86_64-linux-gnu') + ':' + env.get('LD_LIBRARY_PATH', '')
    env.setdefault('VK_DRIVER_FILES', str(vulkan / 'usr/share/vulkan/icd.d/lvp_icd.json'))
    env.setdefault('XDG_RUNTIME_DIR', '/tmp')
    cache = ROOT / 'build/lidar/gpu-cache'
    cache.mkdir(parents=True, exist_ok=True)
    env.setdefault('XDG_CACHE_HOME', str(cache))
    # argv omits interpreter flags, -m's module name, and -c's source text.
    os.execve(sys.executable, [sys.executable, *sys.orig_argv[1:]], env)
