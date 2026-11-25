"""Rebuild the public V11 source snapshot; no private platform access is used."""
from pathlib import Path
import argparse
import hashlib
import json
import re
import subprocess

ROOT = Path(__file__).resolve().parent
EXTERNAL = {
    "Mathlib", "Lean", "Init", "Std", "Batteries", "Qq", "Aesop",
    "ProofWidgets", "LeanSearchClient", "ImportGraph", "Plausible", "Cli",
}
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def code_without_comments_or_strings(text):
    result = []
    i = depth = 0
    string = False
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                depth += 1
                i += 2
            elif text.startswith("-/", i):
                depth -= 1
                i += 2
            else:
                if text[i] == "\n":
                    result.append("\n")
                i += 1
        elif string:
            if text[i] == "\\":
                i += 2
            elif text[i] == '"':
                string = False
                i += 1
            else:
                if text[i] == "\n":
                    result.append("\n")
                i += 1
        elif text.startswith("/-", i):
            depth = 1
            i += 2
        elif text.startswith("--", i):
            j = text.find("\n", i)
            i = len(text) if j < 0 else j
        elif text[i] == '"':
            string = True
            result.append(" ")
            i += 1
        else:
            result.append(text[i])
            i += 1
    return "".join(result)


def check_sources():
    manifest = json.loads((ROOT / "source_manifest.json").read_text())
    order = json.loads((ROOT / "module_order.json").read_text())
    if len(order) != 261 or len(set(order)) != len(order):
        raise SystemExit("Unexpected module order")
    for name, expected in manifest["files"].items():
        if hashlib.sha256((ROOT / name).read_bytes()).hexdigest() != expected:
            raise SystemExit("Changed frozen source/configuration: " + name)
    names = {p.stem for p in ROOT.glob("*.lean") if p.name != "lakefile.lean"}
    if names != set(order):
        raise SystemExit("Unexpected or missing Lean source modules")
    positions = {name: i for i, name in enumerate(order)}
    for module in order:
        code = code_without_comments_or_strings((ROOT / (module + ".lean")).read_text())
        if re.search(r"\b(?:sorry|admit|axiom)\b", code):
            raise SystemExit("Unproved declaration in " + module)
        for header in re.findall(r"(?m)^\s*(?:(?:public|private|meta)\s+)*import\s+([^\n]*)", code):
            imports = header.split()
            if imports and imports[0] == "all":
                imports = imports[1:]
            for dependency in imports:
                if dependency in positions:
                    if positions[dependency] >= positions[module]:
                        raise SystemExit("Invalid dependency order: " + module)
                elif dependency.split(".")[0] not in EXTERNAL:
                    raise SystemExit("Missing import: " + dependency)
    print("PASS: source hashes and import closure (261 modules)", flush=True)
    return order


def rebuild(order):
    expected_audits = json.loads((ROOT / "auxiliary_audit_counts.json").read_text())
    build = ROOT / ".lake/build/lib/lean"
    build.mkdir(parents=True, exist_ok=True)
    logs = ROOT / "ReproductionLogs"
    logs.mkdir(exist_ok=True)
    for module in order:
        path = ROOT / (module + ".lean")
        digest = hashlib.sha256(path.read_bytes()).hexdigest()
        log = logs / (module + ".log")
        with log.open("w") as stream:
            run = subprocess.run(
                ["lake", "env", "lean", "-DautoImplicit=false", "-o",
                 str(build / (module + ".olean")), module + ".lean"],
                cwd=ROOT, stdout=stream, stderr=subprocess.STDOUT,
            )
        text = log.read_text()
        if run.returncode or hashlib.sha256(path.read_bytes()).hexdigest() != digest:
            raise SystemExit("FAIL " + module + "; inspect " + str(log))
        if any(marker in text for marker in ["error:", "error(", "sorryAx"]):
            raise SystemExit("FAIL " + module + "; inspect " + str(log))
        groups = re.findall(r"depends on axioms: \[([^\]]*)\]", text, re.S)
        used = {a.strip() for group in groups for a in group.split(",") if a.strip()}
        if used - STANDARD_AXIOMS:
            raise SystemExit("Unexpected axioms in " + module + ": " + repr(used))
        audit_count = len(groups) + text.count("does not depend on any axioms")
        if module in expected_audits and audit_count != expected_audits[module]:
            raise SystemExit("Incomplete axiom audit in " + module)
        print("PASS " + module, flush=True)
    print("Supporting library checked. Theorems A, B and C remain unproved.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-only", action="store_true", help="Check sources without invoking Lean")
    args = parser.parse_args()
    module_order = check_sources()
    if not args.check_only:
        rebuild(module_order)
