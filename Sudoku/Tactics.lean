import Lean
import Mathlib.Tactic
import Sudoku.Defs

open Lean.Meta Lean.Elab.Tactic

syntax "elimination " term : tactic

macro_rules
| `(tactic| elimination $elim:term) => `(tactic|
  apply $elim (by decide);
  intro n hn hn';
  fin_cases hn <;> simp [-ne_eq] at hn' ⊢ <;> first | (absurd hn'; rfl) | clear hn'
)

syntax "finish" : tactic

macro_rules
| `(tactic| finish) => `(tactic|
  apply Solvable.Done;
  decide;
  constructor <;> decide
)
