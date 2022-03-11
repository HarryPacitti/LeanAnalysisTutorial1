import data.real.basic

/-In this quick Lean tutorial, we aim to get to grips with using convergent
sequences in Lean. We start by defining convergence in a similar manner to
the analysis 1 course.-/

def converges_to (s : ℕ → ℝ) (a : ℝ) :=
∀ ε > 0, ∃ N, ∀ n ≥ N, abs (s n - a) < ε