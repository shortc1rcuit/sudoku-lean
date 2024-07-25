import Lean
import Mathlib.Tactic
open Lean.Meta Lean.Elab.Tactic

syntax "elimination " term : tactic

macro_rules
| `(tactic| elimination $elim:term) => `(tactic|
  apply $elim (by decide);
  intro b hb;
  fin_cases b <;> simp [-ne_eq] at hb ⊢ <;> clear hb
)
