import Sudoku.Lemmas
import Sudoku.Tactics

def one_cell_test : Progress := [[some 1, some 2, none,   some 4],
                                 [some 3, some 4, some 1, some 2],
                                 [some 2, some 1, some 4, some 3],
                                 [some 4, some 3, some 2, some 1]]

theorem one_cell_test_solve (g : Grid) (hg : SudokuRules g)
    (hg_0_0 : g (0, 0) = 1) (hg_0_1 : g (0, 1) = 2)                         (hg_0_3 : g (0, 3) = 4)
    (hg_1_0 : g (1, 0) = 3) (hg_1_1 : g (1, 1) = 4) (hg_1_2 : g (1, 2) = 1) (hg_1_3 : g (1, 3) = 2)
    (hg_2_0 : g (2, 0) = 2) (hg_2_1 : g (2, 1) = 1) (hg_2_2 : g (2, 2) = 4) (hg_2_3 : g (2, 3) = 3)
    (hg_3_0 : g (3, 0) = 4) (hg_3_1 : g (3, 1) = 3) (hg_3_2 : g (3, 2) = 2) (hg_3_3 : g (3, 3) = 1)
    : Solvable g one_cell_test := by
  unfold one_cell_test
  apply Solvable.Set _ _ (0, 2) 3
  · decide
  · apply cell_elim (by decide)
    intro n hn hn'
    fin_cases hn <;> simp at hn' ⊢
    · exact row_conflict (by decide) hg_0_0
    · exact row_conflict (by decide) hg_0_1
    · exact row_conflict (by decide) hg_0_3
  dsimp [Progress.set', List.get!, List.set]
  apply Solvable.Done
  · decide
  · constructor <;> decide

def four_by_four_test : Progress := [[none,   some 1, some 3, none  ],
                                     [some 2, none,   none,   none  ],
                                     [none,   none,   none,   some 3],
                                     [none,   some 2, some 1, none  ]]

theorem four_by_four_test_solve (g : Grid) (hg : SudokuRules g)
    (hg_0_1 : g (0, 1) = 1) (hg_0_2 : g (0, 2) = 3) (hg_1_0 : g (1, 0) = 2)
    (hg_2_3 : g (2, 3) = 3) (hg_3_1 : g (3, 1) = 2) (hg_3_2 : g (3, 2) = 1)
    : Solvable g four_by_four_test := by
  unfold four_by_four_test
  have hg_1_3 : g (1, 3) = 1 := by
    elimination row_elim
    · simp [hg_1_0]
    · exact col_conflict (by decide) hg_0_1
    · exact col_conflict (by decide) hg_3_2
  apply Solvable.Set _ _ _ _ (by decide) hg_1_3
  dsimp [Progress.set', List.get!, List.set]
  have hg_0_3 : g (0, 3) = 2 := by
    elimination col_elim
    · simp [hg_1_3]
    · simp [hg_2_3]
    · exact row_conflict (by decide) hg_3_1
  apply Solvable.Set _ _ _ _ (by decide) hg_0_3
  dsimp [Progress.set', List.get!, List.set]
  have hg_1_2 : g (1, 2) = 4 := by
    elimination cell_elim
    · exact reg_conflict (by decide) (by decide) hg_1_3
    · exact reg_conflict (by decide) (by decide) hg_0_3
    · exact reg_conflict (by decide) (by decide) hg_0_2
  apply Solvable.Set _ _ _ _ (by decide) hg_1_2
  dsimp [Progress.set', List.get!, List.set]
  have hg_3_0 : g (3, 0) = 3 := by
    elimination reg_elim <;> simp [reg_coords, -ne_eq]
    · exact row_conflict (by decide) hg_2_3
    · exact row_conflict (by decide) hg_2_3
    · simp [hg_3_1]
  apply Solvable.Set _ _ _ _ (by decide) hg_3_0
  dsimp [Progress.set', List.get!, List.set]
  have hg_3_3 : g (3, 3) = 4 := by
    elimination row_elim
    · simp [hg_3_0]
    · simp [hg_3_1]
    · simp [hg_3_2]
  apply Solvable.Set _ _ _ _ (by decide) hg_3_3
  dsimp [Progress.set', List.get!, List.set]
  have hg_2_2 : g (2, 2) = 2 := by
    elimination reg_elim <;> simp [reg_coords, -ne_eq]
    · simp [hg_2_3]
    · simp [hg_3_2]
    · simp [hg_3_3]
  apply Solvable.Set _ _ _ _ (by decide) hg_2_2
  dsimp [Progress.set', List.get!, List.set]
  have hg_1_1 : g (1, 1) = 3 := by
    elimination row_elim
    · simp [hg_1_0]
    · simp [hg_1_2]
    · simp [hg_1_3]
  apply Solvable.Set _ _ _ _ (by decide) hg_1_1
  dsimp [Progress.set', List.get!, List.set]
  have hg_2_1 : g (2, 1) = 4 := by
    elimination col_elim
    · simp [hg_0_1]
    · simp [hg_1_1]
    · simp [hg_3_1]
  apply Solvable.Set _ _ _ _ (by decide) hg_2_1
  dsimp [Progress.set', List.get!, List.set]
  have hg_0_0 : g (0, 0) = 4 := by
    elimination row_elim
    · simp [hg_0_1]
    · simp [hg_0_2]
    · simp [hg_0_3]
  apply Solvable.Set _ _ _ _ (by decide) hg_0_0
  dsimp [Progress.set', List.get!, List.set]
  have hg_2_0 : g (2, 0) = 1 := by
    elimination row_elim
    · simp [hg_2_1]
    · simp [hg_2_2]
    · simp [hg_2_3]
  apply Solvable.Set _ _ _ _ (by decide) hg_2_0
  dsimp [Progress.set', List.get!, List.set]
  finish
