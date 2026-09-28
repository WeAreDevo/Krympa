import contextlib
import io
from pathlib import Path
import subprocess
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import run_stitch as rs
import demo_compare as dc


class AbstractionTests(unittest.TestCase):
    def test_nested_matches_recover_original_by_consistent_substitution(self):
        body = 'op(op(X0,X1),X2) = op(X3,op(X0,X1))'
        fwd, rev = rs.build_xn_mapping([body])
        abstract = rs.apply_pattern_to_formula(body, rs.parse_fof_term('op(A,B)'), fwd, rev)
        self.assertEqual(abstract, 'op(Y0, X2) = op(X3, Y0)')
        recovered = abstract.replace('Y0', 'op(X0,X1)')
        self.assertEqual([rs.parse_fof_term(s) for s in rs.split_top_level_eq(body)],
                         [rs.parse_fof_term(s) for s in rs.split_top_level_eq(recovered)])

    def test_different_concrete_matches_are_not_collapsed(self):
        body = 'op(X0,X1) = op(X2,X3)'
        fwd, rev = rs.build_xn_mapping([body])
        self.assertIsNone(rs.apply_pattern_to_formula(body, rs.parse_fof_term('op(A,B)'), fwd, rev))

    def test_fresh_variable_and_single_line_conjecture_preserve_following_axiom(self):
        content = ('fof(c,conjecture, ! [X0,X1,Y0] : '
                   '(op(op(X0,X1),Y0) = op(Y0,op(X0,X1)))).\n'
                   'fof(a1, axiom, ! [X0] : (op(X0,X0) = X0)).\n')
        patterns = SimpleNamespace(abstractions=[SimpleNamespace(name='fn_0', body='(op #0 #1)')])
        with patch.object(rs, 'compress', return_value=patterns):
            result = rs.abstract_single_lemma(content, 3, 3)
        self.assertIsNotNone(result)
        self.assertIn('fof(a1, axiom,', result[0])
        _, variables, body = rs.parse_conjecture_block(result[0])
        self.assertIn('Y1', variables)
        self.assertEqual(body, 'op(Y1, Y0) = op(Y0, Y1)')

    def test_empty_input_clears_old_output(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / 'big-step').mkdir()
            mode = root / 'abstracted_stitch'
            mode.mkdir()
            stale = mode / 'abstracted_stitch_lemma_0001.p'
            stale.write_text('stale')
            subprocess.run([sys.executable, rs.__file__, str(root/'big-step'), str(root)],
                           check=True, capture_output=True)
            self.assertFalse(stale.exists())


class ComparisonTests(unittest.TestCase):
    def test_only_explicit_success_counts(self):
        for text in ['RESULT: CounterSatisfiable', '% SZS status Unknown',
                     '% SZS status Timeout', '', 'RESULT: Satisfiable']:
            self.assertFalse(dc.proof_succeeded(text), text)
        for text in ['RESULT: Theorem (the conjecture is true).', '% SZS status Unsatisfiable']:
            self.assertTrue(dc.proof_succeeded(text))

    def test_vampire_counts_upstream_trivial_inequality_step(self):
        self.assertEqual(dc.count_vampire_steps(
            '1. op(X0,X0) = X0 [input]\n'
            '2. X0 != X0 [resolution 1]\n'
            '3. $false [trivial inequality removal 2]\n'), 2)

    def test_current_stitch_mode(self):
        mode, number, prover = dc.parse_proof_filename('abstracted_stitch_lemma_0008_twee.proof')
        self.assertEqual((number, prover), (8, 'twee'))
        self.assertIsNotNone(dc.STITCH_RE.match(mode))
        self.assertIsNone(dc.STITCH_RE.match('abstracted'))

    def test_all_rows_and_countermodel_excluded_from_scores(self):
        import json
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            proofs = root / 'proofs/twee_tmp'
            proofs.mkdir(parents=True)
            for number in range(1, 82):
                (proofs/f'abstracted_stitch_lemma_{number:04}_twee.proof').write_text(
                    'RESULT: Theorem\nProof:\n= { by axiom 1 }\n')
            (proofs/'abstracted_lemma_0081_twee.proof').write_text('RESULT: CounterSatisfiable')
            (root/'summary_test.json').write_text(json.dumps({str(n): [f'abstracted_stitch_lemma_{n:04}', 'twee', ''] for n in range(1,82)}))
            problem = root/'test.p'
            problem.write_text('')
            output = io.StringIO()
            with patch.object(dc, 'OUTPUT_DIR', root), patch.object(dc, 'PROOFS_DIR', root/'proofs'), patch.object(dc, 'LEMMAS_DIR', root/'lemmas'), patch.object(sys, 'argv', ['demo_compare.py', '--skip-pipeline', str(problem)]), contextlib.redirect_stdout(output):
                dc.main()
            text = output.getvalue()
            self.assertIn('Stitch mode was the winner        : 81', text)
            self.assertNotIn('more lemmas omitted', text)
            row = next(line for line in text.splitlines() if line.strip().startswith('81 '))
            self.assertIn('—', row)


if __name__ == '__main__':
    unittest.main()
