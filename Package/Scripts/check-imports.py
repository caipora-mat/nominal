#!/usr/bin/env python3
"""Check Package import coverage using pinned Lean's own header parser.

Header discovery does not validate Lean bodies; run the registered build and
direct consumers/audit as well. ``--self-test`` uses disposable source trees.
"""

from pathlib import Path
import argparse
import json
import subprocess
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[2]


class CoverageError(RuntimeError):
    """A missing import, unsupported dependency, or incomplete closure."""


def inventory(root: Path) -> dict[str, Path]:
    root_module = root / "Package.lean"
    if not root_module.is_file():
        raise CoverageError(f"missing public root: {root_module}")
    paths = [root_module, *sorted((root / "Package").rglob("*.lean"))]
    return {".".join(p.relative_to(root).with_suffix("").parts): p for p in paths}


def decode_imports(paths: list[Path], output: str) -> dict[Path, set[str]]:
    """Validate per-file results; Lean can report these errors with exit code 0."""
    try:
        data = json.loads(output)
    except json.JSONDecodeError as error:
        raise CoverageError(f"invalid dependency JSON: {error}") from error
    entries = data.get("imports") if isinstance(data, dict) else None
    if not isinstance(entries, list) or len(entries) != len(paths):
        raise CoverageError("dependency JSON result count does not match source count")
    imports = {}
    for path, entry in zip(paths, entries):
        if not isinstance(entry, dict) or entry.get("errors") != []:
            raise CoverageError(f"{path}: header parser errors: {entry}")
        result = entry.get("result")
        if not isinstance(result, dict) or not isinstance(result.get("imports"), list):
            raise CoverageError(f"{path}: missing or malformed header result")
        names = set()
        for dependency in result["imports"]:
            if (not isinstance(dependency, dict)
                    or not isinstance(dependency.get("module"), str)
                    or not dependency["module"]):
                raise CoverageError(f"{path}: malformed import: {dependency}")
            names.add(dependency["module"])
        imports[path] = names
    return imports


def read_imports(paths: list[Path], cwd: Path) -> dict[Path, set[str]]:
    result = subprocess.run(["lake", "env", "lean", "--deps-json",
                             *(str(p.resolve()) for p in paths)], cwd=cwd,
                            capture_output=True, text=True, check=False)
    if result.returncode:
        raise CoverageError(f"Lean header parser failed: {result.stderr or result.stdout}")
    return decode_imports(paths, result.stdout)


def category(module: str) -> str:
    if module == "Package" or module.startswith("Package.Foundations."):
        return "production"
    if module == "Package.Tests.AxiomAudit":
        return "audit"
    raise CoverageError(f"unclassified Package source: {module}")


def check(root: Path, imports: dict[Path, set[str]]) -> tuple[int, int]:
    sources = inventory(root)
    if set(imports) != set(sources.values()):
        raise CoverageError("parsed source inventory does not match files on disk")
    categories = {module: category(module) for module in sources}
    graph = {}
    for module, path in sources.items():
        graph[module] = set()
        for dependency in sorted(imports[path]):
            prefix = dependency.split(".")[0]
            if prefix == "Package":
                if dependency not in sources:
                    raise CoverageError(f"{module}: missing Package target {dependency}")
                src, dst = categories[module], categories[dependency]
                if src == "production" and dst != "production":
                    raise CoverageError(f"{module}: {src} cannot import {dst} {dependency}")
                graph[module].add(dependency)
            elif prefix not in {"Mathlib", "Lean", "Init"}:
                raise CoverageError(f"{module}: forbidden dependency {dependency}")

    def closure(start):
        reached, pending = set(), [start]
        while pending:
            module = pending.pop()
            if module not in reached:
                reached.add(module)
                pending.extend(graph[module])
        return reached

    roots = {"production": "Package", "audit": "Package.Tests.AxiomAudit"}
    counts = []
    for kind, entry in roots.items():
        if entry not in sources:
            raise CoverageError(f"missing {kind} root: {entry}")
        expected = {module for module in sources if categories[module] == kind}
        missing = expected - closure(entry)
        if missing:
            raise CoverageError(f"{kind} unreached modules: {sorted(missing)}")
        counts.append(len(expected))
    missing = sources.keys() - closure(roots["audit"])
    if missing:
        raise CoverageError(f"audit unreached modules: {sorted(missing)}")
    return tuple(counts)


def main() -> None:
    try:
        sources = inventory(ROOT)
        counts = check(ROOT, read_imports(list(sources.values()), ROOT))
    except (CoverageError, OSError) as error:
        raise SystemExit(str(error)) from error
    for kind, count in zip(("production", "audit"), counts):
        print(f"Package {kind}: all {count} source modules reached")


def self_test() -> None:
    """Exercise the actual parser/validators, without modifying project sources."""

    class CoverageTests(unittest.TestCase):
        def setUp(self):
            self.temp = tempfile.TemporaryDirectory(prefix="package-import-test-")
            self.addCleanup(self.temp.cleanup)
            self.root = Path(self.temp.name)
            for name, source in {
                "Package.lean": "import Package.Foundations.Core\n",
                "Package/Foundations/Core.lean": "import Init\n",
                "Package/Tests/AxiomAudit.lean": "import Package\n",
            }.items():
                self.write(name, source)

        def write(self, name, source):
            path = self.root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(source)

        def validate(self):
            sources = inventory(self.root)
            return check(self.root, read_imports(list(sources.values()), ROOT))

        def test_complete_closures(self):
            self.assertEqual(self.validate(), (2, 1))

        def test_orphan_production(self):
            self.write("Package/Foundations/Orphan.lean", "import Init\n")
            with self.assertRaisesRegex(CoverageError, "unreached.*Package.Foundations.Orphan"):
                self.validate()

        def test_no_standalone_examples_layer(self):
            self.write("Package/Examples/Consumer.lean", "import Package\n")
            with self.assertRaisesRegex(CoverageError, "unclassified.*Package.Examples.Consumer"):
                self.validate()

        def test_unclassified_source(self):
            self.write("Package/Unknown.lean", "import Init\n")
            with self.assertRaisesRegex(CoverageError, "unclassified.*Package.Unknown"):
                self.validate()

        def test_missing_target(self):
            self.write("Package.lean", "import Package.Foundations.Missing\n")
            with self.assertRaisesRegex(CoverageError, "missing.*Package.Foundations.Missing"):
                self.validate()

        def test_forbidden_import_even_in_orphan(self):
            self.write("Package/Foundations/Orphan.lean", "import Nominal\n")
            with self.assertRaisesRegex(CoverageError, "forbidden.*Nominal"):
                self.validate()

        def test_production_cannot_import_audit(self):
            self.write("Package.lean", "import Package.Tests.AxiomAudit\n")
            with self.assertRaisesRegex(CoverageError, "production.*audit"):
                self.validate()

        def test_audit_must_reach_production(self):
            self.write("Package/Tests/AxiomAudit.lean", "import Init\n")
            with self.assertRaisesRegex(CoverageError, "audit unreached"):
                self.validate()

        def test_comment_and_import_syntax(self):
            self.write("Package.lean", "module\n/- outer /- import Nominal -/ -/\n"
                       "-- import Instances\npublic import Package.Foundations.Core\n"
                       "import Init import Lean\n")
            self.assertEqual(self.validate(), (2, 1))

        def test_header_error_even_when_lean_exits_zero(self):
            self.write("Package.lean", "public import Init\n")
            with self.assertRaisesRegex(CoverageError, "Package.lean.*header"):
                self.validate()

        def test_json_validation(self):
            path = self.root / "Package.lean"
            for payload in ["not json", "{}", '{"imports":[]}',
                            '{"imports":[{"errors":[],"result":null}]}',
                            '{"imports":[{"errors":["broken"],"result":{}}]}',
                            '{"imports":[{"errors":[],"result":{"imports":[{}]}}]}']:
                with self.subTest(payload=payload), self.assertRaises(CoverageError):
                    decode_imports([path], payload)

        def test_duplicate_meta_imports(self):
            path = self.root / "Package.lean"
            payload = json.dumps({"imports": [{"errors": [], "result": {
                "imports": [{"module": "Init", "isMeta": False},
                            {"module": "Init", "isMeta": True}]}}]})
            self.assertEqual(decode_imports([path], payload), {path: {"Init"}})

        def test_body_syntax_is_checked_by_lean(self):
            path = self.root / "BadBody.lean"
            path.write_text("import Init Init\n")
            result = subprocess.run(["lake", "env", "lean", str(path)], cwd=ROOT,
                                    capture_output=True, text=True, check=False)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("unexpected identifier", result.stdout + result.stderr)

    result = unittest.TextTestRunner(verbosity=1).run(
        unittest.defaultTestLoader.loadTestsFromTestCase(CoverageTests))
    if not result.wasSuccessful():
        raise SystemExit(1)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    if args.self_test:
        self_test()
    else:
        main()
