import copy
import io
import json
import os
import tempfile
import unittest
from contextlib import redirect_stdout

import reproduce_mack1993


class ReproductionExitStatusTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        source = os.path.join(
            reproduce_mack1993.HERE,
            "data",
            "mack1993_published_results.json",
        )
        with open(source) as fh:
            cls.published = json.load(fh)

    def run_with_published(self, published):
        with tempfile.NamedTemporaryFile(mode="w", suffix=".json") as fh:
            json.dump(published, fh)
            fh.flush()
            with redirect_stdout(io.StringIO()):
                return reproduce_mack1993.main(fh.name)

    def test_reviewed_reference_exits_zero(self):
        self.assertEqual(0, self.run_with_published(self.published))

    def test_factor_mismatch_exits_nonzero(self):
        published = copy.deepcopy(self.published)
        published["development_factors_fk_as_printed"][0] += 1
        self.assertEqual(1, self.run_with_published(published))

    def test_nonfinal_sigma_mismatch_exits_nonzero(self):
        published = copy.deepcopy(self.published)
        published["sigma_k_squared_over_1000_as_printed"][0] += 10
        self.assertEqual(1, self.run_with_published(published))

    def test_unexpected_final_sigma_mismatch_exits_nonzero(self):
        published = copy.deepcopy(self.published)
        published["sigma_k_squared_over_1000_as_printed"][-1] = 999
        self.assertEqual(1, self.run_with_published(published))

    def test_published_final_sigma_is_kept_separate_from_computed_value(self):
        triangle = reproduce_mack1993.load_triangle(
            os.path.join(
                reproduce_mack1993.HERE,
                "data",
                "taylor_ashe_cumulative.csv",
            )
        )
        computed = reproduce_mack1993.mack(triangle)[1][-1] / 1000
        published = self.published["sigma_k_squared_over_1000_as_printed"][-1]
        self.assertEqual(0.477, published)
        self.assertAlmostEqual(0.446616550105352, computed, places=12)
        self.assertNotEqual(published, computed)


if __name__ == "__main__":
    unittest.main()
