import os
from pathlib import Path


def repo_root_from(test_file):
    return Path(test_file).resolve().parents[2]


def configure_pythonpath(repo_root):
    os.environ.setdefault("STEVIA_ROOT", str(repo_root))
    os.environ["PYTHONPATH"] = (
        f"{repo_root}{os.pathsep}{os.environ.get('PYTHONPATH', '')}"
    )
    return os.environ["PYTHONPATH"]


def output_dirs(test_file, hdl_toplevel, config_name):
    repo_root = repo_root_from(test_file)
    outputs_dir = Path(os.environ.get("STEVIA_OUTPUTS_DIR", repo_root / "test/outputs"))
    run_dir = outputs_dir / hdl_toplevel / config_name
    build_dir = run_dir / "sim_build"
    run_dir.mkdir(parents=True, exist_ok=True)
    return repo_root, run_dir, build_dir


def runner_extra_env(repo_root):
    return {
        "PYTHONPATH": configure_pythonpath(repo_root),
        "STEVIA_ROOT": str(repo_root),
    }
