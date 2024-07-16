import Mathlib.Tactic

--The Grid function is the "Pure" version of the sudoku that we write propositions about.
abbrev Grid := Fin 4 × Fin 4 → Fin 4

--The equations are written this way such that SudokuRules is Decideable.
structure SudokuRules (grid : Grid) : Prop where
  row_check : ∀ row a b: Fin 4, a ≠ b → grid (row, a) ≠ grid (row, b)
  col_check : ∀ col a b: Fin 4, a ≠ b → grid (a, col) ≠ grid (b, col)
  reg_check : ∀ reg₁ reg₂ a₁ a₂ b₁ b₂: Fin 2, (a₁, a₂) ≠ (b₁, b₂) → grid (2 * reg₁ + a₁, 2 * reg₂ + a₂) ≠ grid (2 * reg₁ + b₁, 2 * reg₂ + b₂)

--Progress represents what parts of the sudoku we do and don't know.
abbrev Progress := List (List (Option (Fin 4)))

def filled : Progress := [[some 1, some 2, some 3, some 4],
                          [some 3, some 4, some 1, some 2],
                          [some 2, some 1, some 4, some 3],
                          [some 4, some 3, some 2, some 1]]

lemma filled_filled : ∀ (row col: Fin 4), ((filled.get! row).get! col).isSome = true := by
  decide

theorem filled_valid : SudokuRules (fun (row, col) => ((filled.get! row).get! col).get (filled_filled row col)) := by
  constructor
  decide
  decide
  decide

/-
The Sudoku will be implemented similar to https://github.com/dwrensha/animate-lean-proofs/blob/main/Chess.lean
Specifically the ForcedWin type.
The type is called Solvable. It will take in a Grid and a Progress equivalent to the grid, and will have two cases, Set and Done.
Set will take in a coordinate (x, y) and a value n.
When applied, it will create the goals "progress(x, y).isNone = true", "grid(x, y) = n" and a new Solvable object with progress(x, y) set to n.
Done, when applied, will create two goals, one which states that all the cells in progress are Some, and another that states that the values of progress satisfy the rules of a Sudoku.
-/
