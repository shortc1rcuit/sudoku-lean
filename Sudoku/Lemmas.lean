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

lemma row_conflict {g : Grid} (hg : SudokuRules g) {row a b : Fin 4} (hab : a ≠ b) {n : ℕ} (hg' : g (row, a) = n) : g (row, b) ≠ n := by
  rw [←hg']
  apply hg.row_check
  exact hab.symm

def row_emb {g : Grid} (hg : SudokuRules g) (row : Fin 4) : Fin 4 ↪ ℕ where
  toFun := fun a => g (row, a)
  inj' := by
    intro a b hab
    contrapose! hab
    exact hg.row_check row a b hab

lemma row_map {g : Grid} (hg : SudokuRules g) (row : Fin 4) : Finset.map (row_emb hg row) Finset.univ = Finset.Icc 1 4 := by
  apply Finset.eq_of_subset_of_card_le
  · intro n hn
    simp [row_emb] at hn
    obtain ⟨a, ha⟩ := hn
    rw [←ha]
    apply hg.cases
  · simp

lemma row_elim {g : Grid} (hg : SudokuRules g) {row a : Fin 4} {n : ℕ} (hn : n ∈ Finset.Icc 1 4) (h_row : ∀ b ≠ a, g (row, b) ≠ n) : g (row, a) = n := by
  simp [←row_map hg row, row_emb] at hn
  contrapose! hn
  intro a'
  obtain ha' | ha' := eq_or_ne a' a
  · rw [ha']
    exact hn
  · exact h_row a' ha'
