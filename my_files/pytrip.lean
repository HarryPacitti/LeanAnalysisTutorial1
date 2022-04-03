import number_theory.pythagorean_triples
import tactic.ring


lemma sq_ne_two_fin_zmod_three (z : zmod 3) : z * z ≠ 2 :=
begin
  change fin 3 at z,
  fin_cases z; norm_num [fin.ext_iff, fin.coe_bit0, fin.coe_bit1],
end

lemma int.sq_ne_two_mod_three (z : ℤ) : (z * z) % 3 ≠ 2 :=
suffices ¬ (z * z) % (3 : ℕ) = 2 % (3 : ℕ), by norm_num at this,
begin
  rw ← zmod.int_coe_eq_int_coe_iff',
  simpa using sq_ne_two_fin_zmod_three _,
end

variables {x y z : ℤ} 

lemma mod_three_eq_zero_or_one_or_two (n : ℤ) : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 :=
have h : n % 3 < 3 := abs_of_nonneg (show 0 ≤ (3 : ℤ), from dec_trivial) ▸ int.mod_lt _ dec_trivial,
have h₁ : 0 ≤ n % 3 := int.mod_nonneg _ dec_trivial,
match (n % 3), h, h₁ with
| (0:ℕ) := λ _ _, or.inl rfl
| (1 : ℕ) := λ _ _, or.inr (or.inl rfl)
| (2 : ℕ) := λ _ _, or.inr (or.inr rfl)
| (k + 3 : ℕ) := λ h _, absurd h dec_trivial
| -[1+ a] := λ _ h₁, absurd h₁ dec_trivial
end

variables (h : pythagorean_triple x y z)

include h

lemma exact_one_div_three (hc : int.gcd x y = 1) :
  (x % 3 = 0 ∧ y % 3 = 1) ∨ (x % 3 = 0 ∧ y % 3 = 2) ∨ (x % 3 = 1 ∧ y % 3 = 0) ∨ (x % 3 = 2 ∧ y % 3 = 0) :=
begin
  rcases mod_three_eq_zero_or_one_or_two x with hx | hx | hx ;
    rcases mod_three_eq_zero_or_one_or_two y with hy | hy | hy,
  {-- x % 3 = 0, y % 3 = 0
  exfalso,
  apply nat.not_coprime_of_dvd_of_dvd (dec_trivial : 1 < 3) _ _ hc,
  {apply int.dvd_nat_abs_of_of_nat_dvd, apply int.dvd_of_mod_eq_zero hx },
  {apply int.dvd_nat_abs_of_of_nat_dvd, apply int.dvd_of_mod_eq_zero hy}},
  {left, exact ⟨ hx, hy ⟩}, --x % 3 = 0, y % 3 = 1
  {right,left, exact ⟨ hx, hy ⟩}, --x % 3 = 0, y % 3 = 2
  {right, right, left, exact ⟨ hx, hy ⟩}, --x % 3 = 1, y % 3 = 1
  {-- x % 3 = 1, y % 3 = 1
    exfalso,
    obtain ⟨x0, y0, rfl, rfl⟩ : ∃ x0 y0, x = x0* 3 + 1 ∧ y = y0 * 3 + 1,
    { cases exists_eq_mul_left_of_dvd (int.dvd_sub_of_mod_eq hx) with x0 hx2,
      cases exists_eq_mul_left_of_dvd (int.dvd_sub_of_mod_eq hy) with y0 hy2,
      rw sub_eq_iff_eq_add at hx2 hy2, exact ⟨x0, y0, hx2, hy2⟩ },
    apply int.sq_ne_two_mod_three z,
    rw show z * z = 3 * (3 * x0 * x0 + 2 * x0 + 2 * y0 + 3 * y0 * y0 ) + 2, by { rw ← h.eq, ring },
    rw [int.add_mod, int.mul_mod_right, zero_add, int.mod_mod], norm_num,},
  {--x % 3 = 1, y % 3 = 2
    exfalso,
    obtain ⟨x0, y0, rfl, rfl⟩ : ∃ x0 y0, x = x0* 3 + 1 ∧ y = y0 * 3 + 2,
    { cases exists_eq_mul_left_of_dvd (int.dvd_sub_of_mod_eq hx) with x0 hx2,
      cases exists_eq_mul_left_of_dvd (int.dvd_sub_of_mod_eq hy) with y0 hy2,
      rw sub_eq_iff_eq_add at hx2 hy2, exact ⟨x0, y0, hx2, hy2⟩ },
    apply int.sq_ne_two_mod_three z,
     rw show z * z = 3 * (3 * x0 * x0 + 2 * x0 + 4 * y0 + 3 * y0 * y0 ) + 5, by { rw ← h.eq, ring },  
    rw [int.add_mod, int.mul_mod_right, zero_add, int.mod_mod], norm_num,},
  {right ,right ,right ,exact ⟨hx, hy⟩ },
  {--x % 3 = 2, y % 3 = 1
    exfalso,
    obtain ⟨x0, y0, rfl, rfl⟩ : ∃ x0 y0, x = x0* 3 + 2 ∧ y = y0 * 3 + 1,
    { cases exists_eq_mul_left_of_dvd (int.dvd_sub_of_mod_eq hx) with x0 hx2,
      cases exists_eq_mul_left_of_dvd (int.dvd_sub_of_mod_eq hy) with y0 hy2,
      rw sub_eq_iff_eq_add at hx2 hy2, exact ⟨x0, y0, hx2, hy2⟩ },
    apply int.sq_ne_two_mod_three z,
     rw show z * z = 3 * (3 * x0 * x0 + 4 * x0 + 2 * y0 + 3 * y0 * y0 ) + 5, by { rw ← h.eq, ring },  
    rw [int.add_mod, int.mul_mod_right, zero_add, int.mod_mod], 
    norm_num,},
  {--x % 3 = 2, y % 3 = 1
    exfalso,
    obtain ⟨x0, y0, rfl, rfl⟩ : ∃ x0 y0, x = x0* 3 + 2 ∧ y = y0 * 3 + 2,
    { cases exists_eq_mul_left_of_dvd (int.dvd_sub_of_mod_eq hx) with x0 hx2,
      cases exists_eq_mul_left_of_dvd (int.dvd_sub_of_mod_eq hy) with y0 hy2,
      rw sub_eq_iff_eq_add at hx2 hy2, exact ⟨x0, y0, hx2, hy2⟩ },
    apply int.sq_ne_two_mod_three z,
     rw show z * z = 3 * (3 * x0 * x0 + 4 * x0 + 4 * y0 + 3 * y0 * y0 ) + 8, by { rw ← h.eq, ring },  
    rw [int.add_mod, int.mul_mod_right, zero_add, int.mod_mod], 
    norm_num,},
end