import Sudoku.Defs

lemma cell_elim {g : Grid} (hg : SudokuRules g) {c : Coords} {n : ℕ} (hc : ∀ n' ∈ Finset.Icc 1 4, n' ≠ n → g c ≠ n') : g c = n := by
  have : ∃ (a : ℕ), g c = a := exists_eq'
  contrapose! this
  intro a
  obtain ha | ha := em' (a ∈ Finset.Icc 1 4)
  · rw [←Finset.forall_mem_not_eq'] at ha
    exact ha _ (hg.cases c)
  · obtain ha' | ha' := eq_or_ne a n
    · rw [ha']
      exact this
    · exact hc a ha ha'
