import data.real.basic

import data.real.basic

/-Lean is a programming language used for proof formalisation,
meaning the program checks that a given proof is actually correct.
Here, we will give a brief summary of how to use Lean. We will then 
move onto proving some results requiring the uses of axioms for the real 
numbers -/

/-We defined the axioms of addition for the real numbers as follows
(A.1) Commutativity : a + b = b + a, ∀ a,b ∈ ℝ
The associated theorem in Lean is add_comm
(A.2) Associativity : (a + b) + c = a + (b + c), ∀ a, b, c ∈ ℝ 
In Lean, this is known as add_assoc
(A.3) Existence of 0 : ∃ (0∈ℝ) such that 0 + a = a
In Lean, this is known as zero_add
(A.4) Existence of the negative : ∀ a∈ℝ, ∃x∈ℝ such that a + x = 0-/

/-Our axioms of multiplication for the real numbers are the following
(M.1) Commutativity : a*b = b*a for all a, b ∈ ℝ.
In Lean, this is known as mul_comm
(M.2) Associativity : (a * b) * c = a * (b * c) for all a, b, c ∈ ℝ.
In Lean, this is known as mul_assoc
(M.3) Existence of 1 : There is a real number 1 ̸= 0 with 1 * a = a for all a ∈ ℝ.
In Lean, this is known as one_mul
(M.4) Existence of the inverse : ∀ a ∈ R \ {0} there is a unique x ∈ ℝ with a * x = 1.

-/

/-We also have distributivity
(D.1) Distributivity : a * (b + c) = (a * b) + (a * c) for all a, b, c ∈ ℝ.
In Lean, this is known as left_distrib
-/

/-When using Lean, if we want to use a theorem involving an equals sign,
we use the rw tactic to tell Lean our intention. This will apply the said
theorem at all locations it can. If you only want to use it at a certain 
location, you can use nth_rewrite x, where x is a non-negative integer
and specifies the location to apply the theorem
When we want to use a theorem with an implication, you should use the apply
tactic


We now provide a few examples on how to use Lean
-/

example (a : ℝ) : 0 + a + 0 = a:=
begin
rw add_zero,
rw zero_add
end

/-In thenext example we use a backward arrow ← to use the backward version 
of the equality
-/ 

example (a b c : ℝ): a+c+b = a + b + c:=
begin
rw add_assoc,
rw add_comm c b,
rw ← add_assoc,
end

/-When we specify where to change a statement with nth_rewrite, the first
position starts from 0-/

example (a b : ℝ):  a*1 + 1*a   =  a*1 + a*1 :=
begin
nth_rewrite 3 mul_comm,
end


example (a b : ℝ):  a*1 + 1*a   =  a*1 + a*1 :=
begin
nth_rewrite 1 ← mul_comm,
end




theorem neg_sub_pos_self1 : (-1 : ℝ) + 1 = 0 :=
begin
exact neg_add_self 1,
end



example:  2 * 2 = 4 :=
begin
nth_rewrite 0 ← one_add_one_eq_two,
nth_rewrite 0 ← one_add_one_eq_two,
rw left_distrib,
rw mul_comm,
rw left_distrib,
rw one_mul,
end


theorem neg_one_a_inv (a b:ℝ): -a = (-1)*a:=
begin
suffices: (-1)*a +a = 0,
{apply eq.symm at this,
exact eq_neg_iff_add_eq_zero.mpr this,},
nth_rewrite 1 ←one_mul a,
rw mul_comm,
rw mul_comm 1 a,
rw ← left_distrib, 
rw neg_sub_pos_self1,
rw mul_zero,


end



example (a:ℝ): (-a)^2 = a^2:=
begin
rw pow_two,
rw neg_one_a_inv,
rw mul_assoc,
rw ← mul_assoc a,
rw mul_comm a (-1),
rw  mul_assoc (-1) a a,
rw ←pow_two,
rw ← mul_assoc,
rw neg_one_mul,
rw neg_neg,
rw one_mul,
apply a,
end
