#!/usr/bin/env python3
"""One entry point for every local check of this repository.

    python scripts/verify.py [--fetch-cache] [--skip-build]

In order: the pins (lean-toolchain and the Mathlib revision of lake-manifest.json are the committed
ones), the source guard, the definition comparison between Challenge.lean and HK/Defs.lean, the
statement comparison between Challenge.lean and Solution.lean, the exact replay scripts/check_hk.py,
the exact certificates under note/certificates/ (if any), the metadata (formalization.yaml parses;
its title length, main results and alignment against comparator.json; no definition holes; no
original-proof source), the Lean build of every target (including the Test audit, which fails on
any axiom beyond propext, Classical.choice and Quot.sound), the module-resolution check, the
elaboration check of the compared definitions (printed with pp.all from the Challenge and from
HK.Defs, which must agree exactly, as the registry's comparator demands), and Palomar's
core-notation audit of the compared declarations. The compared definitions are read from
Challenge.lean at run time: every `def` and `noncomputable def` at the start of a line, in namespace
HK (the inductive `Model` is compared through `scripts/check_definitions.py`). `--fetch-cache` runs
`lake exe cache get` first (network); `--skip-build` leaves out the four Lean steps. The last line
is `VERIFY: PASS` or `VERIFY: FAIL`. Exit status 0 on PASS only.
"""

from pathlib import Path
import json
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
TOOLCHAIN = "leanprover/lean4:v4.35.0-rc2"
MATHLIB_REV = "065356127b1dc0016f66b7283ce0ce2c4055aa55"
TARGETS = ["HK", "Challenge", "Solution", "Test"]
NAMESPACE = "HK"
DEF_HEAD = re.compile(r"^(?:noncomputable )?def ([\w.']+)", flags=re.M)


def definitions():
    """Every definition of Challenge.lean, fully qualified. They are fully specified in the Challenge,
    so comparator.json lists none of them in definition_names (a name there is a definition HOLE
    whose value the Solution supplies); the elaboration check and the notation audit cover them all."""
    text = (ROOT / "Challenge.lean").read_text(encoding="utf-8")
    return [f"{NAMESPACE}.{name}" for name in DEF_HEAD.findall(text)]


def run(args, **kw):
    print("+", " ".join(args), flush=True)
    return subprocess.run(args, cwd=ROOT, text=True, encoding="utf-8", errors="replace", **kw)


def step(name, ok, detail=""):
    print(f"[{'ok' if ok else 'FAIL'}] {name}" + (f": {detail}" if detail else ""), flush=True)
    return ok


def check_pins():
    toolchain = (ROOT / "lean-toolchain").read_text(encoding="utf-8").strip()
    manifest = json.loads((ROOT / "lake-manifest.json").read_text(encoding="utf-8"))
    revs = {p["name"]: p.get("rev") for p in manifest.get("packages", [])}
    ok = toolchain == TOOLCHAIN and revs.get("mathlib") == MATHLIB_REV
    return step("pins", ok, f"toolchain {toolchain}, mathlib {revs.get('mathlib')}")


def check_script(name, args):
    result = run([sys.executable] + args, capture_output=True)
    tail = (result.stdout + result.stderr).strip().splitlines()[-1:] or [""]
    return step(name, result.returncode == 0, tail[0])


def check_replay():
    result = run([sys.executable, "-I", "scripts/check_hk.py"], capture_output=True)
    lines = result.stdout.strip().splitlines()
    good = result.returncode == 0 and lines[-1:] == ["VERDICT: PASS"]
    return step("check_hk.py (the standard-library replay)", good,
                lines[-1] if lines else (result.stderr.strip().splitlines()[-1:] or [""])[0])


def check_certificates():
    ok = True
    for path in sorted((ROOT / "note" / "certificates").glob("*/verify.py")):
        result = run([sys.executable, str(path)], capture_output=True)
        verdict = [line for line in result.stdout.splitlines() if line.startswith("VERDICT")]
        good = result.returncode == 0 and verdict == ["VERDICT: PASS"]
        ok &= step(f"certificate {path.parent.name}", good, verdict[-1] if verdict else "no verdict")
    return ok


def check_yaml():
    """formalization.yaml parses; its title is within the registry's limit; its main_results match
    comparator.json; its alignment covers every compared theorem; comparator.json lists no definition
    holes; no original-proof source. With jsonschema installed and scripts/formalization.schema.json
    present, also validates the schema."""
    path = ROOT / "formalization.yaml"
    if not path.exists():
        return step("formalization.yaml", False, "missing")
    try:
        import yaml
    except ImportError:
        return step("formalization.yaml", False, "PyYAML is not installed (pip install pyyaml)")
    try:
        data = yaml.safe_load(path.read_text(encoding="utf-8"))
        config = json.loads((ROOT / "comparator.json").read_text(encoding="utf-8"))
        problems = []
        title = data["project"]["name"]
        if len(title) > 300:
            problems.append(f"title has {len(title)} characters (limit 300)")
        mains = [m["declaration"] for m in data["status"]["main_results"]]
        if mains != config["theorem_names"]:
            problems.append("status.main_results differ from comparator.json theorem_names")
        aligned = {a["lean"] for a in data.get("alignment", {}).get("statements", [])}
        gap = set(config["theorem_names"]) - aligned
        if gap:
            problems.append("alignment.statements misses " + ", ".join(sorted(gap)))
        if config.get("definition_names"):
            problems.append("comparator.json lists definition holes; this entry's definitions are "
                            "fully specified")
        if any(src.get("type") == "original-proof" for src in data.get("sources", [])):
            problems.append("an original-proof source would force other/background on every other "
                            "source")
    except (KeyError, TypeError, ValueError) as error:
        return step("formalization.yaml", False, f"malformed: {error!r}")
    schema = ROOT / "scripts" / "formalization.schema.json"
    if schema.exists():
        try:
            import jsonschema
            jsonschema.validate(data, json.loads(schema.read_text(encoding="utf-8")))
        except ImportError:
            problems.append("jsonschema is not installed; schema not validated")
        except Exception as error:  # the validator's first line is the message
            problems.append("schema: " + str(error).splitlines()[0])
    detail = "; ".join(problems) if problems else (
        f"parses; title {len(title)} chars; {len(mains)} main results; "
        f"{len(data.get('sources', []))} sources" + ("; schema valid" if schema.exists() else ""))
    return step("formalization.yaml", not problems, detail)


def check_build():
    ok = True
    for target in TARGETS:
        result = run(["lake", "build", target], capture_output=True)
        bad = [line for line in result.stdout.splitlines() if "error" in line.lower()]
        ok &= step(f"lake build {target}", result.returncode == 0 and not bad,
                   bad[0] if bad else "built")
    return ok


def check_module_resolution():
    result = run(["lake", "env", sys.executable, "scripts/check_module_resolution.py"],
                 capture_output=True)
    text = (result.stdout + result.stderr).strip()
    return step("module resolution", result.returncode == 0, text.splitlines()[-1] if text else "")


def check_definition_elaboration(names):
    """The compared definitions, printed with pp.all from the Challenge and from the development's
    definitions module, must agree exactly: the comparator judges the elaborated constants, which
    depend on the imports through instance resolution."""
    config = json.loads((ROOT / "comparator.json").read_text(encoding="utf-8"))
    scratch = ROOT / ".scratch"
    scratch.mkdir(exist_ok=True)
    outputs = []
    for module in (config["challenge_module"], f"{NAMESPACE}.Defs"):
        path = scratch / f"verify_pp_{module.replace('.', '_')}.lean"
        header = "import " + module + "\nset_option pp.all true\n"
        path.write_text(header + "".join("#print " + n + "\n" for n in names), encoding="utf-8")
        result = run(["lake", "env", "lean", str(path)], capture_output=True)
        outputs.append((result.returncode, result.stdout))
        path.unlink()
    ok = all(rc == 0 for rc, _ in outputs) and outputs[0][1].strip() != "" and \
        outputs[0][1] == outputs[1][1]
    return step(f"definition elaboration (Challenge vs {NAMESPACE}.Defs, pp.all, {len(names)} names)",
                ok, "identical" if ok else "the printed terms differ or a print failed")


def check_notation_audit(names):
    config = json.loads((ROOT / "comparator.json").read_text(encoding="utf-8"))
    args = ["lake", "env", "lean", "--run", "scripts/core_notation_audit.lean",
            config["challenge_module"]]
    for name in config["theorem_names"]:
        args += ["theorem", name]
    for name in names:
        args += ["def", name]
    result = run(args, capture_output=True)
    try:
        rows = json.loads(result.stdout)
    except ValueError:
        rows = []
    expected = len(config["theorem_names"]) + len(names)
    printed = {row.get("name") for row in rows} if isinstance(rows, list) else set()
    ok = result.returncode == 0 and len(printed) == expected and \
        printed == set(config["theorem_names"]) | set(names)
    return step("core-notation audit", ok, f"{len(printed)} of {expected} declarations printed")


def main():
    fetch = "--fetch-cache" in sys.argv
    skip_build = "--skip-build" in sys.argv
    names = definitions()
    ok = step("compared definitions read from Challenge.lean", len(names) > 0,
              f"{len(names)} names")
    ok &= check_pins()
    ok &= check_script("source guard", ["scripts/check-source.py"])
    ok &= check_script("definitions", ["scripts/check_definitions.py"])
    ok &= check_script("statements", ["scripts/check_statements.py"])
    ok &= check_replay()
    ok &= check_certificates()
    ok &= check_yaml()
    if not skip_build:
        if fetch:
            ok &= step("lake exe cache get", run(["lake", "exe", "cache", "get"]).returncode == 0)
        ok &= check_build()
        ok &= check_module_resolution()
        ok &= check_definition_elaboration(names)
        ok &= check_notation_audit(names)
    print("VERIFY: PASS" if ok else "VERIFY: FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
