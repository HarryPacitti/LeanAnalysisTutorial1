import data.real.basic
import data.nat.basic
variables (x y : ℝ) 


example (A B : Prop) : (¬ A) ∨ (B) ↔ (A ∧ B) ∨ (¬ A) :=
begin
split,
intro h,
cases h with ha hab,
right,
exact ha,
by_cases h:A,
left,
split,
exact h,
exact hab,
right,
exact h,
intro h,
by_cases ha:A,
right,
cases h with h₁ h₂,
cases h₁ with h₃ h₄,
exact h₄,
exfalso,
apply h₂,
exact ha,
left,
exact ha,

end

theorem de_morgan1 (A B : Prop) : ¬ (A∨B) ↔ (¬A) ∧ (¬B) :=
begin
split, --We consider each implication separately
intro h₁, --We introduce ¬(A ∨ B) as the hypothesis h₁
split, --Instead of showing ¬A ∧ ¬B, we will show ¬A and ¬B separately
intro h₂, --The goal ¬A changes to false, and we the hypothesis h₂:A
apply h₁,
left,
exact h₂,
intro h₂,
apply h₁,
right,
exact h₂,
intros h₁ h₂,
cases h₁ with h₃ h₄,
cases h₂ with h₅ h₆,
apply h₃,
exact h₅,
apply h₄,
exact h₆,
end

theorem de_morgan2 (A B : Prop) : ¬(A∧B) ↔ (¬A)∨(¬B):=
begin
split,
intro h₁,
by_cases h:A,
right,
intro h₂,
apply h₁,
split,
exact h,
exact h₂,
left,
exact h,
intros h₁ h₂,
cases h₂ with h₃ h₄,
cases h₁ with h₅ h₆,
apply h₅,
exact h₃,
apply h₆,
apply h₄,
end

theorem lawofcomm (A B : Prop) : A∧B ↔ B∧A:=
begin
split, --We consider the separate implications ⊢ A ∧ B → B ∧ A and ⊢B ∧ A → A ∧ B
intro h₁, --This lets us consider the hypothesis A ∧ B
cases h₁ with h₂ h₃, -- h₁:A ∧ B changes to h₂:A and h₃:B
split,--Instead of showing B ∧ A we show B and A separately
exact h₃,
exact h₂,
intro h₁,
cases h₁ with h₂ h₃, 
split,
exact h₃,
exact h₂,
end

theorem lawofcomm (A B : Prop) : A∧B ↔ B∧A:=
begin
split, --We consider the separate implications ⊢ A ∧ B → B ∧ A and ⊢B ∧ A → A ∧ B
iterate 2
{intro h₁, --This lets us consider the hypothesis A ∧ B
cases h₁ with h₂ h₃, -- h₁:A ∧ B changes to h₂:A and h₃:B
split,--Instead of showing B ∧ A we show B and A separately
exact h₃,
exact h₂,},
end

theorem lawofassoc (A B C : Prop) : A∧(B∧C) ↔ (A∧B)∧C:=
begin
split,
intro h₁,
split, 
cases h₁ with h₂ h₃,
cases h₃ with h₄ h₅,
split,
exact h₂,
exact h₄,
cases h₁ with h₂ h₃,
cases h₃ with h₄ h₅,
exact h₅,
intro h₁,
split, 
cases h₁ with h₂ h₃,
cases h₂ with h₄ h₅,
exact h₄,
cases h₁ with h₂ h₃,
cases h₂ with h₄ h₅,
split,
exact h₅,
exact h₃,
end

theorem lawofdist (A B C : Prop) : A∧(B∨C) ↔ (A∧B)∨(A∧C):=
begin
split,
intro h₁,
cases h₁ with h₂ h₃,
cases h₃ with h₄ h₅,
left,
split,
exact h₂,
exact h₄,
right,
split,
exact h₂,
exact h₅,
intro h₁,
cases h₁ with h₂ h₃,
cases h₂ with h₄ h₅,
split,
exact h₄,
left,
exact h₅,
split,
cases h₃ with h₄ h₅,
exact h₄,
cases h₃ with h₄ h₅,
right,
exact h₅,
end


example (n: nat)  (h:x>0) : (1+x)^n ≥ 1 + x*n :=
begin
  induction n with d hd,
  norm_num,
  have h₁:d.succ = ↑d+1,
  norm_num,
  rw h₁,
  norm_num,
  rw mul_add,
  rw pow_succ,
  rw add_mul,
  rw ← add_assoc,
  rw one_mul,
  rw mul_one,
  norm_num at hd,
  apply add_le_add hd,
  nth_rewrite 0 ← mul_one x,
  apply mul_le_mul,
  clear hd,
  refl,
  clear hd,
  induction d with d hd,
  simp[pow_zero,pow_succ],
  nth_rewrite 0 ← mul_one (1:ℝ),
  apply mul_le_mul,
  linarith,
  finish,
  repeat{linarith},

end

example {x : ℝ} {n : ℕ} (h : 0 < x) : 1 + x * n ≤ (1 + x) ^ n :=
begin
  induction n with n hn,
  { norm_num },
  { change n.succ with n + 1, norm_num,
    simp [pow_succ, mul_add, ←add_assoc, add_mul],
    apply add_le_add hn, clear hn, nth_rewrite 0 ←mul_one x,
    apply mul_le_mul; try {linarith},
    induction n with n hn; simp [pow_zero, pow_succ],
    nth_rewrite 0 ←mul_one (1 : ℝ), apply mul_le_mul; linarith },
end


