import data.real.basic
variables (x y : ℝ)

theorem add_law (a b x y : ℝ) (h₁: x<y) (h₂:a<b): x+a < y + b :=
begin
have h₃: x + a < y + a,
exact add_lt_add_right h₁ a,
have h₄: y + a < y + b,
exact add_lt_add_left h₂ y,
exact lt_trans h₃ h₄,
end

lemma real_le_mul (a b c d :ℝ) (h₁:0<a) (h₂:0<b) (h₃:0<c) (h₄:0<d)
(h₅: a<b) (h₆:c<d): a * c < b * d:=
begin
have h₇: a * c < b * c, --We prove an auxiliary statement
exact (mul_lt_mul_right h₃).mpr h₅, --We use monotonicity of multiplication
have h₈: b*c < b*d, --We prove another auxiliary statement
rw mul_comm b c, --We use commutativity of multiplication so our goal is in the required form to use monotonicity 
rw mul_comm b d, --We use commutativity again
exact (mul_lt_mul_right h₂).mpr h₆, --Monotonicity shows our auxiliary statement
apply lt_trans h₇ h₈, --We use transitivity to close the goal 
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
  refl,
  clear hd,
  induction d with d hd,
  rw pow_zero,
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

