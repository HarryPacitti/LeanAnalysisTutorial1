import data.real.basic

/-Lean is a programming language used for proof formalisation,
meaning the program checks that a given proof is actually correct.
Here, we will give a brief summary of how to use Lean. We will then 
move onto proving some results requiring the uses of axioms for the real 
numbers -/

/-We defined the axioms of addition for the real numbers as follows
(A.1) Commutativity : a + b = b + a, ∀ a,b ∈ ℝ
(A.2) Associativity : (a + b) + c = a + (b + c), ∀ a, b, c ∈ ℝ 
(A.3) Existence of 0 : ∃ (0∈ℝ) such that 0 + a = a
(A.4) Existence of the negative : ∀ a∈ℝ, ∃x∈ℝ such that a + x = 0-/

/-Our axioms of multiplication for the real numbers are the following
(M.1) Commutativity : a*b = b*a for all a, b ∈ ℝ.
(M.2) Associativity : (a * b) * c = a * (b * c) for all a, b, c ∈ ℝ.
(M.3) Existence of 1 : There is a real number 1 ̸= 0 with 1 * a = a for all a ∈ ℝ.
(M.4) Existence of the inverse : ∀ a ∈ R \ {0} there is a unique x ∈ ℝ with a * x = 1.

-/

/-We also have distributivity
(D.1) Distributivity : a * (b + c) = (a * b) + (a * c) for all a, b, c ∈ ℝ.
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

/-In thenext example we use a backward arrow ← (type \l )to use the 
backward version of the equality
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

/-Now we've seen some examples, here are some theorems that can be
used to solve the next problem. Remove the 'sorry' to continue the 
proof. Only rw with the following theorems is needed to close the goal.
-/

#check (left_distrib : ∀ (a b c : ℝ), a * (b + c) = (a * b) + (a * c))
#check (mul_comm : ∀ (a b : ℝ) , a * b = b * a)
#check (one_mul : ∀ a : ℝ , 1 * a = a)

example:  2 * 2 = 4 :=
begin
nth_rewrite 0 ← one_add_one_eq_two,
nth_rewrite 0 ← one_add_one_eq_two,
sorry
end

/-A list of additional theorems needed for the next question are listed below. 
You may have to use ←left_distrib at some point-/

#check (neg_sub_pos_self1 : -1 + 1 = 0)
#check (mul_zero : ∀ a :ℝ, a * 0 = 0)

theorem neg_one_a_inv (a b:ℝ): -a = (-1)*a:=
begin
suffices: (-1)*a +a = 0,
{apply eq.symm at this,
exact eq_neg_iff_add_eq_zero.mpr this,},
nth_rewrite 1 ←one_mul a,
sorry
end

/-For the final problem, you will have an additional goal after the 
first of ℝ. This can be shown with exact a. Furthermore, after we specify 
a theorem, we can specify the specific place we what it to occur. An example
can be seen in line 137. Another example would be if our goal read as
⊢ a * 1 + 1 * a = a * 1 + a * 1
then we could type 
rw mul_comm 1 a, 
to specify we want to use commutativity at 1*a
 We now list some additional
theorems. -/

#check (mul_assoc : ∀ (a b c:ℝ), a * b * c = a * (b * c))
#check (pow_two : ∀ a :ℝ, a ^ 2 = a * a)
#check (neg_one_mul : ∀ a :ℝ, (-1) * a = -a)
#check (neg_neg : ∀ a : ℝ, - - a = a)

example (a:ℝ): (-a)^2 = a^2:=
begin
rw pow_two,
rw neg_one_a_inv,
rw mul_assoc,
rw ← mul_assoc a,
rw mul_comm a (-1),
sorry
end
