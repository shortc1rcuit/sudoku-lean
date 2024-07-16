import Mathlib.Tactic

abbrev Coords := Fin 4 × Fin 4

--The Grid function is the "Pure" version of the sudoku that we write propositions about.
abbrev Grid := Coords → Fin 4

--The equations are written this way such that SudokuRules is Decideable.
structure SudokuRules (grid : Grid) : Prop where
  row_check : ∀ row a b: Fin 4, a ≠ b → grid (row, a) ≠ grid (row, b)
  col_check : ∀ col a b: Fin 4, a ≠ b → grid (a, col) ≠ grid (b, col)
  reg_check : ∀ reg₁ reg₂ a₁ a₂ b₁ b₂: Fin 2, (a₁, a₂) ≠ (b₁, b₂) → grid (2 * reg₁ + a₁, 2 * reg₂ + a₂) ≠ grid (2 * reg₁ + b₁, 2 * reg₂ + b₂)

--Progress represents what parts of the sudoku we do and don't know.
abbrev Progress := List (List (Option (Fin 4)))

def Progress.get (p : Progress) (c : Coords) := (p.get! c.1).get! c.2
def Progress.set' (p : Progress) (c : Coords) (n : Option (Fin 4)) : Progress :=
  p.set c.1 ((p.get! c.1).set c.2 n)

def filled : Progress := [[some 1, some 2, some 3, some 4],
                          [some 3, some 4, some 1, some 2],
                          [some 2, some 1, some 4, some 3],
                          [some 4, some 3, some 2, some 1]]

lemma filled_filled : ∀ (c: Coords), (filled.get c).isSome = true := by
  decide

theorem filled_valid : SudokuRules (fun c => (filled.get c).get (filled_filled c)) := by
  constructor
  decide
  decide
  decide

/-
The Sudoku will be implemented similar to https://github.com/dwrensha/animate-lean-proofs/blob/main/Chess.lean
Specifically the ForcedWin type.
The type is called Solvable. It will take in a Grid and a Progress equivalent to the grid, and will have two cases, Set and Done.
Set will take in a coordinate c and a value n.
When applied, it will create the goals "(progress.get c).isNone = true", "grid c = n" and a new Solvable object with progress c set to n.
Done, when applied, will create two goals, one which states that all the cells in progress are Some, and another that states that the values of progress satisfy the rules of a Sudoku.
-/

inductive Solvable : Grid → Progress → Prop where
| Set (grid : Grid) (progress : Progress) (c : Coords) (n : Fin 4) : (progress.get c).isNone = true → grid c = n → (Solvable grid (progress.set' c (some n))) → (Solvable grid progress)
| Done (grid : Grid) (progress : Progress) : (∀ (c: Coords), (progress.get c).isSome = true) → SudokuRules (fun c => (progress.get c).get!) → Solvable grid progress

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
  · set a := g (0, 2) with ha
    clear_value a
    fin_cases a <;> simp at ha
    · absurd ha
      reduce at hg_0_3
      simp at hg_0_3
      nth_rewrite 1 [←hg_0_3]
      apply hg.row_check
      decide
    · absurd ha
      rw [←hg_0_0]
      apply hg.row_check
      decide
    · absurd ha
      nth_rewrite 1 [←hg_0_1]
      apply hg.row_check
      decide
    · rfl
  simp [Progress.set']
  apply Solvable.Done
  · decide
  · constructor <;> decide
