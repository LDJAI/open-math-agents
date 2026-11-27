"""Build the Lean sources and audit their public theorem dependencies."""
import os
import re
import subprocess
import tempfile
from graphlib import TopologicalSorter
from pathlib import Path

root = Path(__file__).resolve().parent
sources = {p.stem: p for p in root.glob("*.lean")}
imports = {
    name: set(re.findall(r"^import (\w+)$", path.read_text(), re.M)) & sources.keys()
    for name, path in sources.items()
}
with tempfile.TemporaryDirectory() as build:
    env = dict(os.environ)
    current = [str(Path(p).resolve()) for p in env.get("LEAN_PATH", "").split(os.pathsep) if p]
    env["LEAN_PATH"] = os.pathsep.join([build, *current])
    for name in TopologicalSorter(imports).static_order():
        print(f"Checking {name}", flush=True)
        subprocess.run(
            ["lean", "-j", "1", "-R", str(root), "-o", f"{build}/{name}.olean", str(sources[name])],
            env=env, check=True,
        )
    audit = root / "audit.txt"
    checked = Path(build, "Audit.lean")
    checked.write_text(audit.read_text())
    result = subprocess.run(
        ["lean", "-j", "1", str(checked)], cwd=build, env=env,
        check=True, capture_output=True, text=True,
    )
    print(result.stdout, end="")
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    if "sorryAx" in result.stdout:
        raise SystemExit("An audited theorem contains a proof placeholder")
    for block in re.findall(r"depends on axioms:\s*\[([^\]]*)\]", result.stdout):
        unexpected = {name.strip() for name in block.split(",")} - allowed
        if unexpected:
            raise SystemExit(f"Unexpected axioms: {unexpected}")
