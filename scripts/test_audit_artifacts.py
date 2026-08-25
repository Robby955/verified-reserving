import unittest
from pathlib import Path


SCRIPTS = Path(__file__).resolve().parent


class AuditArtifactTest(unittest.TestCase):
    def test_findings_source_matches_rendered_audit(self):
        findings = (SCRIPTS / "audit" / "FINDINGS.md").read_text().strip()
        rendered = (SCRIPTS / "audit" / "AUDIT_RESULTS.md").read_text()
        rendered_findings = rendered.split("## Findings\n\n", 1)[1].split(
            "\n\n## Aggregate tables", 1
        )[0]
        self.assertEqual(findings, rendered_findings.strip())


if __name__ == "__main__":
    unittest.main()
