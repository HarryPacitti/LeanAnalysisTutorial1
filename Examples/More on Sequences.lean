import data.real.basic



def converges_to (s : ℕ → ℝ) (a : ℝ) :=
∀ ε > 0, ∃ N, ∀ n ≥ N, abs (s n - a) < ε

def cauchy_seq (s : ℕ → ℝ) :=
∀ ε > 0, ∃ N, ∀ n m ≥ N, abs (s n - s m) < ε

variables {s t : ℕ → ℝ} {a b c d : ℝ} {z:ℕ }
variable (x : ℕ → ℝ )  := x. + x.2

theorem conv_is_cauchy (h: converges_to s a): 
cauchy_seq (λ n , s n) :=
begin
intros ε εpos, --Introduce ε: ℝ and εpos: ε > 0
dsimp, --This makes our goal easier to read 
have εpos2 : 0 < ε / 2, 
linarith, --This follows from ε > 0
cases h (ε / 2) εpos2 with N₁ h₂, --Using the convergence of s with ε/2
cases h (ε / 2) εpos2 with N₂ h₃, --Using the convergence of s with ε/2
use max N₁ N₂, --We have that  n ≥ max N₁ N₂
intros p q r t, --Introduce the natural numbers p and r which are both greater than max N₁ N₂
have h₄: p ≥ N₁,finish, --This above follows from p ≥ max N₁ N₂
have h₅: r ≥ N₂, finish,
specialize @h₂ p h₄, -- This gives h₂: |s p - a| < ε / 2
specialize @h₃ r h₅, -- This gives h₃: |s r - a| < ε / 2
rw abs_sub_comm (s r) a at h₃, --Rewrite |s r - a| as |a - s r|
have h₆: |s p - a| + |a - s r| < ε/2 +ε/2,
apply add_lt_add h₂ h₃, -- Add h₂ and h₃ together
norm_num at h₆, --ε / 2 + ε / 2 = ε 
have h₇: |s p - s r| ≤ |s p - a| + |a - s r|,
exact abs_sub_le (s p) a (s r), --Follows from the triangle inequality
apply lt_of_le_of_lt h₇ h₆, --Inequalities h₇ and h₆ imply the result
end

theorem conv0_cauchy (u : ℕ → ℝ) 
(h₁: ∀ (n m :ℕ ) ,   |s n - s m| ≤ u n)
(h₂: converges_to u 0) : cauchy_seq (λ n, s n):=
begin
intros ε εpos, --Introduce ε: ℝ and εpos: ε > 0
dsimp, --This makes our hypothesis easier to read
cases h₂ ε εpos with N h₃, --Convergence of u lets us have N: ℕ and  h₃: ∀ (n : ℕ), n ≥ N → |u n - 0| < ε
use N, -- Our goal is now ∀ (n : ℕ), n ≥ N → ∀ (m : ℕ), m ≥ N → |s n - s m| < ε
intros n ineqn m ineqm, --We have n: ℕ ineqn: n ≥ N m: ℕ and ineqm: m ≥ N
specialize @h₃ n ineqn, --h₃ becomes |u n - 0| < ε
rw sub_zero at h₃, -- |u n - 0| = |u n|
specialize @h₁ n m,-- h₁ now reads as |s n - s m| ≤ u n
have h₄: u n ≤ |u n|,
exact le_abs_self (u n),--This is definitional
apply lt_of_le_of_lt h₁ (lt_of_le_of_lt h₄ h₃),-- h₁ h₄ and h₃ together imply the goal
end


