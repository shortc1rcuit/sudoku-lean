import Sudoku.Defs

lemma cell_elim {g : Grid} [hg : SudokuRules g] {c : Coords} {n : ℕ} (hc : ∀ n' ∈ Finset.Icc 1 4, n' ≠ n → g c ≠ n') : g c = n := by
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

lemma row_conflict {g : Grid} [hg : SudokuRules g] {row a b : Fin 4} (hab : a ≠ b) {n : ℕ} (hg' : g (row, a) = n) : g (row, b) ≠ n := by
  rw [←hg']
  apply hg.row_check _ _ _ hab.symm

def row_emb (g : Grid) [hg : SudokuRules g] (row : Fin 4) : Fin 4 ↪ ℕ where
  toFun := fun a => g (row, a)
  inj' := by
    intro a b hab
    contrapose! hab
    exact hg.row_check row a b hab

lemma row_map (g : Grid) [hg : SudokuRules g] (row : Fin 4) : Finset.map (row_emb g row) Finset.univ = Finset.Icc 1 4 := by
  apply Finset.eq_of_subset_of_card_le
  · intro n hn
    simp [row_emb] at hn
    obtain ⟨a, ha⟩ := hn
    rw [←ha]
    apply hg.cases
  · simp

lemma row_elim {g : Grid} [hg : SudokuRules g] {row a : Fin 4} {n : ℕ} (hn : n ∈ Finset.Icc 1 4) (h_row : ∀ b ≠ a, g (row, b) ≠ n) : g (row, a) = n := by
  simp [←row_map g row, row_emb] at hn
  contrapose! hn
  intro a'
  obtain ha' | ha' := eq_or_ne a' a
  · rw [ha']
    exact hn
  · exact h_row a' ha'

lemma col_conflict {g : Grid} [hg : SudokuRules g] {col a b : Fin 4} (hab : a ≠ b) {n : ℕ} (hg' : g (a, col) = n) : g (b, col) ≠ n := by
  rw [←hg']
  apply hg.col_check _ _ _ hab.symm

def col_emb (g : Grid) [hg : SudokuRules g] (col : Fin 4) : Fin 4 ↪ ℕ where
  toFun := fun a => g (a, col)
  inj' := by
    intro a b hab
    contrapose! hab
    exact hg.col_check col a b hab

lemma col_map (g : Grid) [hg : SudokuRules g] (col : Fin 4) : Finset.map (col_emb g col) Finset.univ = Finset.Icc 1 4 := by
  apply Finset.eq_of_subset_of_card_le
  · intro n hn
    simp [col_emb] at hn
    obtain ⟨a, ha⟩ := hn
    rw [←ha]
    apply hg.cases
  · simp

lemma col_elim {g : Grid} [hg : SudokuRules g] {col a : Fin 4} {n : ℕ} (hn : n ∈ Finset.Icc 1 4) (h_col : ∀ b ≠ a, g (b, col) ≠ n) : g (a, col) = n := by
  simp [←col_map g col, col_emb] at hn
  contrapose! hn
  intro a'
  obtain ha' | ha' := eq_or_ne a' a
  · rw [ha']
    exact hn
  · exact h_col a' ha'

lemma reg_coords_rw (c : Coords) : c = reg_coords (c.1 / 2 * 2 + c.2 / 2) (c.1 % 2 * 2 + c.2 % 2) := by
  unfold reg_coords
  have h : 4 = 2 * 2 := by norm_num
  conv =>
    right
    congr
    · rw [Fin.add_def]
      left
      rw [Fin.val_mul, Fin.div_val, Fin.val_add, Fin.val_mul]
      simp
      simp only [h]
      rw [Nat.mod_mul_right_div_self, Nat.add_div_of_dvd_right (by simp), @Nat.div_eq_of_lt (c.2 / 2) 2 (Nat.div_lt_of_lt_mul c.2.isLt)]
      simp
      rw [@Nat.mod_eq_of_lt (c.1 / 2) 2 (Nat.div_lt_of_lt_mul c.1.isLt), Fin.val_add, Fin.val_mul]
      simp
      simp only [h]
      rw [Nat.mod_mul_right_div_self, Nat.add_div_of_dvd_right (by simp)]
      simp
      rw [Nat.div_add_mod', Nat.mod_eq_of_lt (c.1.isLt)]
    · rw [Fin.add_def]
      left
      rw [Fin.val_mul, Fin.mod_val, Fin.val_add, Fin.val_mul]
      simp
      rw [Nat.mod_mod_of_dvd _ (by norm_num), Nat.add_mod _ _ 2, Nat.mul_mod_left]
      simp
      rw [@Nat.mod_eq_of_lt (c.2 / 2) 2 (Nat.div_lt_of_lt_mul c.2.isLt), Fin.val_add, Fin.val_mul]
      simp
      rw [Nat.mod_mod_of_dvd _ (by norm_num), Nat.add_mod _ _ 2, Nat.mul_mod_left]
      simp
      rw [Nat.div_add_mod', Nat.mod_eq_of_lt (c.2.isLt)]

lemma reg_conflict {g : Grid} [hg : SudokuRules g] {c₁ c₂ : Coords} (hc : c₁ ≠ c₂) (hc' : c₁.1 / 2 = c₂.1 / 2 ∧ c₁.2 / 2 = c₂.2 / 2) (hg' : g c₁ = n) : g c₂ ≠ n := by
  rw [←hg', reg_coords_rw c₂, reg_coords_rw c₁, hc'.1, hc'.2]
  apply hg.reg_check
  contrapose! hc
  rw [Prod.eq_iff_fst_eq_snd_eq]
  conv at hc' =>
    congr <;> {
      simp [Fin.ext_iff, Fin.div_val]
    }
  have h : 4 = 2 * 2 := by norm_num
  constructor
  · apply Fin.eq_of_val_eq
    rw [←Nat.div_add_mod' c₁.1 2, ←Nat.div_add_mod' c₂.1 2]
    replace hc := congrArg (fun a => a.val / 2) hc
    conv at hc =>
      simp
      congr <;> {
        rw [Fin.val_add, Fin.val_mul, Fin.mod_val, Fin.mod_val]
        simp
        simp only [h]
        rw [Nat.mod_mul_right_div_self, Nat.add_div_of_dvd_right (by simp)]
        simp
      }
    rw [hc'.1, hc]
  · apply Fin.eq_of_val_eq
    rw [←Nat.div_add_mod' c₁.2 2, ←Nat.div_add_mod' c₂.2 2]
    replace hc := congrArg (fun a => a.val % 2) hc
    conv at hc =>
      simp
      congr <;> {
        rw [Fin.val_add, Fin.val_mul, Fin.mod_val, Fin.mod_val]
        simp
        rw [Nat.mod_mod_of_dvd _ (by norm_num), Nat.add_mod]
        simp
      }
    rw [hc'.2, hc]

def reg_emb (g : Grid) [hg : SudokuRules g] (reg : Fin 4) : Fin 4 ↪ ℕ where
  toFun := fun a => g (reg_coords reg a)
  inj' := by
    intro a b hab
    contrapose! hab
    exact hg.reg_check reg a b hab

lemma reg_map (g : Grid) [hg : SudokuRules g] (reg : Fin 4) : Finset.map (reg_emb g reg) Finset.univ = Finset.Icc 1 4 := by
  apply Finset.eq_of_subset_of_card_le
  · intro n hn
    simp [reg_emb] at hn
    obtain ⟨a, ha⟩ := hn
    rw [←ha]
    apply hg.cases
  · simp

lemma reg_elim {g : Grid} [hg : SudokuRules g] {c : Coords} {n : ℕ} (hn : n ∈ Finset.Icc 1 4) (h_reg : ∀ c' : Fin 4, c' ≠ c.1 % 2 * 2 + c.2 % 2 → g (reg_coords (c.1 / 2 * 2 + c.2 / 2) c') ≠ n) : g c = n := by
  simp [←reg_map g (c.1 / 2 * 2 + c.2 / 2), reg_emb] at hn
  contrapose! hn
  intro a
  obtain ha | ha := eq_or_ne a (c.1 % 2 * 2 + c.2 % 2)
  · rw [ha, ←reg_coords_rw]
    exact hn
  · exact h_reg a ha
