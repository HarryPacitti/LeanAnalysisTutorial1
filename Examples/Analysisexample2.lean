import data.real.basic

/-In this Lean tutorial, we aim to get to grips with using convergent
sequences in Lean. We start by defining convergence in a similar manner to
the analysis 1 course.-/

def converges_to (s : ℕ → ℝ) (a : ℝ) :=
∀ ε > 0, ∃ N, ∀ n ≥ N, abs (s n - a) < ε

/-We will firstly look at the tactics which we will use in this section
to help us close our proofs and provide some examples.-/

/-We have already seen the rw, nth_rewrite and exact tactics being used, so we 
now move onto using intros, specialize, apply, use and cases-/

/-The intro tactic can be used when, for propositions A and B, our goal is of the
form 
⊢ A → B 
or
⊢∀( a : A ),B.
This allows us to introduce the left hand side of the goal as a hypothesis for us
to use. For example, if you were to write 
intro h, 
for both the previous examples, the goal states would change to

h:A
⊢B

Some further examples of intro and shown below-/

example (A: Prop) : A → A:=
begin
intro h, --We introduce our hypothesis h: A
exact h, --Our goal is exactly the same as our hypothesis h
end

variables {a b c : ℝ}

#check (mul_pos : 0 < a → 0 < b → 0 < a * b)

example ( x : ℝ) (h₁: 0 < x) : ∀ ( a : ℝ), 0 < a →  0 < a*x:=
begin
intros a apos, --We introduce the hypotheses a : ℝ and apos: 0 < a
exact mul_pos apos h₁, --We use the theorem that multiplying two non-negative reals together gives a non-negative real 
end

/-The use tactic can be deployed whenever our goal is of the form 
⊢ ∃ (N : ℕ), statement
Then by writing 
use x, 
where x is a previous hypothesis, such as x : ℝ, meaning x is a real number, then our goal would progress to 
⊢ statement
where the statement now depends on x. An example is given below-/

#check (zero_lt_one : (0 : ℝ) < (1 : ℝ) )

example: ∃ (x : ℝ), x < 1:=
begin
use 0,
exact zero_lt_one,
end

/-The specialize tactic can be used whenever we have a hypothesis of the form 
hypothesis: ∀ ( a : A), statement 
and another hypothesis say 
h : A. 
Then by writing 
specialize @hypothesis h,
our hypothesis will become 
hypothesis: statement depending on h

Furthermore if our we have the following hypotheses 
h₁ : A → B
h₂ : A
then we could write 
specialize @h₁ h₂ 
in order to simplify h₁ to 
h₁: B 
An example of using specialize is shown below with the question being from mathematics in Lean-/

variables {α : Type*} (P : α → Prop)

example (h : ∀ x, ¬ P x) : ¬ ∃ x, P x :=
begin
  intros h₁, --This changes our goal to false h₁ : ∃ (x : α), P x
  cases h₁ with x hx, --We unfold our hypothesis h₁ giving us x:α and hx : P x
  specialize @h x, --We act at h: ∀ (x : α), ¬P x giving h: ¬P x
  specialize @h hx, --We know P x so acting on h: ¬P x leaves us with h: false
  exact h,--Our goal is exactly the same as the hypothesis h
end

/-The apply tactic for cases similar to the following
h : A → B
⊢ B
where by writing 
apply h,
our goal will turn to 
⊢ A
Furthermore, you can use apply when you have a theorem of the form A→B
A few examples of using apply can be found below-/

example (h₁ : a < b) (h₂: b < c): a < c :=
begin
apply lt_trans h₁ h₂, --We use transitivity with our two hypotheses to show a < c
end

example (A B C : Prop) (h₁: A → B) (h₂: B → C) (h₃:A): C :=
begin
apply h₂, --This turns our goal from ⊢C to ⊢B
apply h₁, --This changes the goal from ⊢B to ⊢A
exact h₃, --Our goal is the same as our hypothesis h₃
end

/-We lastly look at the cases tactic which can be used to unfold hypotheses of the form 
hypothesis: A ↔ B
in addition to 
hypothesis: ∃(a:A), statement
By writing 
cases hypothesis with h₁ h₂
We would introduce the new hypotheses
h₁ : A
h₂ : B 
and 
h₁ : A
h₂ : statement involving h₁
respectively
An example of using cases can be found above in the specialize section.-/

/-Now we've outlined our the tactics we will use, lets outline some proofs involving convergence-/

--Lets firstly look at a proof that if a function s converges absolutely to zero, then s converges to zero

variables {s t : ℕ → ℝ} 

#check (sub_zero : ∀ a : ℝ , a - 0 = a)
#check (lt_of_abs_lt : | a |< b →  a < b)


theorem converges_to_ze
  (cs : converges_to (abs s) 0): converges_to (λ n, s n ) (0) :=
begin
intros ε εpos, --Introduce the hypotheses ε:ℝ and εpos:ε>0 
dsimp,--This removes the λ in our goal and makes it easier to read
cases cs ε εpos with h₁ h₂, /-We unravel our hypothesis cs: converges_to |s| 0
using the fact ε: ℝ and εpos: ε > 0 giving our two new hypotheses h₁ and h₂-/
use h₁, --We progress our goal by using the natural number h₁
intros n h₃,--We progress our goal by introducing n: ℕ and h₃: n ≥ h₁
specialize @h₂ n h₃,--We simplify h₂ using n : ℕ and h₃: n ≥ h₁ leaving us with h₂: ||s| n - 0| < ε
rw sub_zero, --We use the theorem that a - 0 = a to simplify our goal to ⊢ |s n| < ε
rw sub_zero at h₂,--We use the same theorem to simplify h₂ to ||s| n| < ε
apply lt_of_abs_lt h₂,--We solve our goal by using the fact |a| < b → a < b on h₂ giving the goal ⊢ |s n| < ε
end


--Now we move onto a proof that convergent sequences are bounded

#check (le_abs_self : ∀ (a :ℝ) , a ≤ |a|)
#check (sub_lt_iff_lt_add' : a - b < c ↔ a < b + c)
#check (lt_of_le_of_lt : a ≤ b → b < c → a < c)

theorem exists_le_of_converges_to (cs : converges_to s a) :
  ∃ N b, ∀ n, N ≤ n → s n < b :=
begin
cases cs 1 zero_lt_one with N h, /-Since s is convergent we let ε=1 and introduce N : ℕ and
h: ∀ (n : ℕ), n ≥ N → |s n - a| < 1 -/ 
use [N , a + 1], /-We will use n such that N ≤ n and prove all terms beyond this
are bounded by a+1 -/
intros n h₁, -- Introduce n : ℕ and h₁: N ≤ n
specialize @h n h₁, --We use n and h₁ to transform h from ∀ (n : ℕ), n ≥ N → |s n - a| < 1 to |s n - a| < 1
have h₂: s n - a ≤ abs(s n - a),-- We prove an auxiliary statement 
apply le_abs_self, --This statement follows from the definition of the absolute value 
suffices h₃: s n - a < 1, --We we show the goal ⊢ s n - a < 1 instead
exact sub_lt_iff_lt_add'.mp h₃, --(s n) - a < 1 implies (s n) < a + 1
apply lt_of_le_of_lt h₂ h, --We close our goal using transitivity with |s n - a| < 1 and s n - a ≤ |s n - a|
end


--Now lets tackle the proof of the squeezing theorem with the following new theorems.

#check (le_abs_self : ∀ (a :ℝ) , a ≤ |a|)
#check (lt_trans : a < b → b < c → a < c)
#check (lt_of_lt_of_le : a < b → b ≤ c → a < c )

theorem squeeze (cs :converges_to s 0) 
(h₁: ∀ (e:ℕ), (abs t e) < s e ): converges_to (λ n, t n) (0):=
begin
intros ε εpos, --Introduce the hypotheses ε:ℝ and εpos:ε>0 
dsimp,-- This removes the λ in our goal and makes it easier to read
cases cs ε εpos with h₂ h₃, /-We unravel our hypothesis cs: converges_to |s| 0
using the fact ε: ℝ and εpos: ε > 0 giving our two new hypotheses h₁ and h₂-/
use h₂, --We progress our goal by using the natural number h₂
intros n h₄, --We progress our goal by introducing n: ℕ and h₄: n ≥ h₁
specialize @h₃ n h₄, --We simplify h₃ using n : ℕ and h₄: n ≥ h₁ leaving us with h₃: |s n - 0| < ε
rw sub_zero,-- We remove the zero in our goal since t n - 0 = t n
rw sub_zero at h₃,--We remove the zero at h₃ leaving s n
specialize @h₁ n, --We simplify h₁ from ∀ (e : ℕ), |t| e < s e to |t| n < s n
have h₅: s n ≤  |s n|, --We use have in order to prove an auxiliary result, which will be helpful in our proof
exact le_abs_self (s n),--We prove s n ≤ |s n| using le_abs_self
apply lt_trans (lt_of_lt_of_le h₁ h₅) h₃, /-We close our goal using transitivity 
with |t| n < s n, s n ≤ |s n| and |s n| < ε.-/
end

/-We now move on to proving that the sum of two convergent sequences is also convergent,
but we firstly mention the use of linarith and congr.
Linarith can be used when we have a goal that can be closed just using linear arithmetic and
Lean will figure out what theorems to use to close the goal.
Congr can be used to get rid of something that affects both sides of an equation allowing
us to show that each side of an equality takes the same values. In the following proof
it's used to get rid of the absolute sign when we prove an auxiliary hypothesis.-/

#check (le_of_max_le_left : max a b ≤ c → a ≤ c )
#check (le_of_max_le_right : max a b ≤ c → b ≤ c )
#check (abs_add : ∀ (a b : ℝ), |a+b| ≤ |a| + |b| )
#check (lt_of_le_of_lt : a ≤ b → b < c → a < c )


theorem converges_to_add
  (cs : converges_to s a) (ct : converges_to t b):
converges_to (λ n, s n + t n) (a + b) :=
begin
intros ε εpos, --Introduce ε: ℝ and εpos: ε > 0
dsimp, --dsimp gets rid of the λ in our goal and makes it easier to read
have ε2pos : 0 < ε / 2, --Let's prove an additional statement that 0 < ε/2
linarith , --Linarith uses linear arithmetic to show 0<ε/2
cases cs (ε / 2) ε2pos with Ns hs, --Convergence of s implies Ns: ℕ and hs: ∀ (n : ℕ), n ≥ Ns → abs (s n - a) < ε / 2
cases ct (ε / 2) ε2pos with Nt ht, --Convergence of t implies Nt: ℕ and ht: ∀ (n : ℕ), n ≥ Nt → abs (t n - b) < ε / 2
use max Ns Nt, -- We will show ⊢ ∀ (n : ℕ), n ≥ max Ns Nt → abs (s n + t n - (a + b)) < ε
intros c cN, -- Introduce c: ℕ and cN: c ≥ max Ns Nt
specialize @hs c,--hs becomes hs: c ≥ Ns → abs (s c - a) < ε / 2
specialize @ht c,--ht becomes ht: c ≥ Nt → abs (t c - b) < ε / 2
specialize @hs (le_of_max_le_left cN),-- hs becomes hs: abs (s c - a) < ε / 2
specialize @ht (le_of_max_le_right cN), --ht becomes ht: abs (t c - b) < ε / 2
have h₃: abs (s c + t c - (a + b)) = abs ((s c - a) + (t c - b)),
congr,-- We will show ⊢ s c + t c - (a + b) = s c - a + (t c - b)
linarith, --The above can be solved with linear arithmetic
rw h₃, --Change the goal to ⊢ abs (s c - a + (t c - b)) < ε
have h₅: abs (s c - a) + abs (t c - b) < ε,
linarith, --ε/2 + ε /2 = ε
have h₆: abs((s c - a) + ( t c - b)) ≤  abs (s c - a) + abs ( t c -b),
apply abs_add (s c - a) (t c - b), --We use the triangle inequality to prove h₆
apply lt_of_le_of_lt h₆ h₅, -- We complete our goal using transitivity
end







/-Mathematics in Lean by Jeremy Avigad has been used heavily in this tutorial with
the definition of convergence and first few lines of the proof showing the sum
of convergent sequences is also convergent as well as a few of the examples for 
the tactics.-/