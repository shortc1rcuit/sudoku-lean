import Sudoku.Lemmas

def test : Progress := [[some 1, some 2, none,   some 4],
                        [some 3, some 4, some 1, some 2],
                        [some 2, some 1, some 4, some 3],
                        [some 4, some 3, some 2, some 1]]

theorem test_solve (g : Grid) (hg : SudokuRules g)
    (hg_0_0 : g (0, 0) = 1) (hg_0_1 : g (0, 1) = 2)                         (hg_0_3 : g (0, 3) = 4)
    (hg_1_0 : g (1, 0) = 3) (hg_1_1 : g (1, 1) = 4) (hg_1_2 : g (1, 2) = 1) (hg_1_3 : g (1, 3) = 2)
    (hg_2_0 : g (2, 0) = 2) (hg_2_1 : g (2, 1) = 1) (hg_2_2 : g (2, 2) = 4) (hg_2_3 : g (2, 3) = 3)
    (hg_3_0 : g (3, 0) = 4) (hg_3_1 : g (3, 1) = 3) (hg_3_2 : g (3, 2) = 2) (hg_3_3 : g (3, 3) = 1)
    : Solvable g test := by
  unfold test
  apply Solvable.Set _ _ (0, 2) 3
  · decide
  · apply cell_elim hg
    intro n hn hn'
    fin_cases hn <;> simp at hn' ⊢
    · exact row_conflict hg (by decide) hg_0_0
    · exact row_conflict hg (by decide) hg_0_1
    · exact row_conflict hg (by decide) hg_0_3
  simp [Progress.set']
  apply Solvable.Done
  · decide
  · constructor <;> decide
