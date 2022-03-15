import data.real.basic

def converges_to (s : ℕ → ℝ) (a : ℝ) :=
∀ ε > 0, ∃ N, ∀ n ≥ N, abs (s n - a) < ε

variables {s t : ℕ → ℝ} {a b c: ℝ}

theorem converges_to_ze
  (cs : converges_to (abs s) 0): converges_to (λ n, s n ) (0) :=
begin
intros ε εpos, --Introduce the hypotheses ε:ℝ and εpos:ε>0 
dsimp,
cases cs _ εpos with h₁ h₂,
use h₁,
intros n h₃,
specialize @h₂ n h₃,
rw sub_zero,
rw sub_zero at h₂,
apply lt_of_abs_lt h₂,
end

theorem squeeze (cs :converges_to s 0) 
(h₁: ∀ (e:ℕ), (abs t e) < s e ): converges_to (λ n, t n) (0):=
begin
intros ε εpos, 
dsimp,
cases cs ε εpos with h₂ h₃,
use h₂,
intros n h₄,
specialize @h₃ n h₄,
rw sub_zero,
rw sub_zero at h₃,
specialize @h₁ n,
have h₅: s n ≤  |s n|,
exact le_abs_self (s n),
apply lt_trans (lt_of_lt_of_le h₁ h₆) h₃,
end

theorem conv_inv (cs : converges_to s a) (h₁: a ≠ 0) (h₂: ∀(m:ℕ), s m ≠ 0) : converges_to(λ n, 1/(s n))(1/a):=
begin
intros ε εpos,
have inv_εpos: 1/ε > 0,
finish,
dsimp,
cases cs (1/ε) inv_εpos with N h₃,
use N,
intro n,
intro h₄,
specialize @h₃ n h₄,
sorry,

end
