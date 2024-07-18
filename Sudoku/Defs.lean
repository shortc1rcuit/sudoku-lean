import Mathlib.Tactic

abbrev Coords := Fin 4 × Fin 4

--The Grid function is the "Pure" version of the sudoku that we write propositions about.
abbrev Grid := Coords → ℕ

--The equations are written this way such that SudokuRules is Decideable.
structure SudokuRules (grid : Grid) : Prop where
  cases : ∀ c : Coords, grid c ∈ Finset.Icc 1 4
  row_check : ∀ row a b : Fin 4, a ≠ b → grid (row, a) ≠ grid (row, b)
  col_check : ∀ col a b : Fin 4, a ≠ b → grid (a, col) ≠ grid (b, col)
  reg_check : ∀ c₁ c₂ : Coords, c₁ ≠ c₂ → c₁.1 / 2 = c₂.1 / 2 ∧ c₁.2 / 2 = c₂.2 / 2 → grid c₁ ≠ grid c₂

--Progress represents what parts of the sudoku we do and don't know.
abbrev Progress := List (List (Option ℕ))

def Progress.get (p : Progress) (c : Coords) := (p.get! c.1).get! c.2
def Progress.set' (p : Progress) (c : Coords) (n : Option ℕ) : Progress :=
  p.set c.1 ((p.get! c.1).set c.2 n)

/-
The Sudoku will be implemented similar to https://github.com/dwrensha/animate-lean-proofs/blob/main/Chess.lean
Specifically the ForcedWin type.
The type is called Solvable. It will take in a Grid and a Progress equivalent to the grid, and will have two cases, Set and Done.
Set will take in a coordinate c and a value n.
When applied, it will create the goals "(progress.get c).isNone = true", "grid c = n" and a new Solvable object with progress c set to n.
Done, when applied, will create two goals, one which states that all the cells in progress are Some, and another that states that the values of progress satisfy the rules of a Sudoku.
-/

inductive Solvable : Grid → Progress → Prop where
| Set (grid : Grid) (progress : Progress) (c : Coords) (n : ℕ) : (progress.get c).isNone = true → grid c = n → (Solvable grid (progress.set' c (some n))) → (Solvable grid progress)
| Done (grid : Grid) (progress : Progress) : (∀ (c: Coords), (progress.get c).isSome = true) → SudokuRules (fun c => (progress.get c).get!) → Solvable grid progress
