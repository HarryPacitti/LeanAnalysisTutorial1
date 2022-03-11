import algebra.ordered_ring

variables {R : Type*} [ordered_ring R]
variables a b c : R

example : a ≤ b → 0 ≤ b - a := 
begin
  intro hyp,
  have h₁: a + (- a)  ≤ b + (-a) ,
  exact add_le_add_right hyp (-a),
  have h₂: a + (-a) = 0,
  apply add_neg_self a,
  rw h₂ at h₁,
  have h₃: b + (-a) = b-a,
  apply (sub_eq_add_neg b a).symm,
  rw h₃ at h₁,
  exact h₁,
end



