/-In this tutorial, we aim to introduce using logic in Lean. We will firstly look at 
defining logical quantifiers.#check

The symbol '∧', which can be written by \and means and. Therefore, for logical
statements A and B, A ∧ B means A and B.

Furthermore, the symbol '∨' means or, which can be typed out using \or .

When using Lean, we also need to use tactics. These are commands that Lean interprets
which help us to progress towards closing the goal.

Firstly, if we have a hypothesis which is identical to our goal, say h, then we can
use the 'exact h,' tactic to close our goal.

Secondly, the 'intro' tactic can be used whenever we have an '↔' if implication 
in our goal. For example, if our goal is of the form
⊢ A → B 
then by typing 'intro h,' we introduce a new hypothesis h:A with our goal
changing to ⊢ B.

The 'left,' and 'right,' tactics can be used when we have a goal containing an
∨ symbol. 'left,' will change a goal of the form ⊢A ∨ B to ⊢ A. 
On the other hand, by typing 'right,' a goal of the form ⊢ A ∨ B will change
to ⊢ B.#check

Furthermore, the 'split' tactic can be used when our goal contains an '∧' symbol.
'split' will change a goal of the form ⊢ A ∧ B to two separate goals, ⊢ A and ⊢ B
which we prove separately. We can also use 'split,' whenever we have an '↔' iff 
statement in the goal.

We may also have an instance where we want to consider the cases when A is true
and false separately. This can be done by deploying the 'by_cases' tactic. By writing
something similar to 'by_cases h:A,' we will introduce two identical goals, one with
a hypothesis h:A and the other with the hypothesis h:¬A.#check

Finally, if one of our hypotheses contain an '∧' or a '∨' statement, we can use the
cases tactic. If our hypothesis is of the form h: A ∧ B, by typing 
'cases h with h₁ h₂,'
we will transform the hypothesis h into two simpler hypotheses h₁:A and h₂:B 
which are more easily handled.
Furthermore, if we have a hypothesis of the form h: A ∨ B, and one goal, then by typing 
'cases h with h₁ h₂,' 
we will change our hypothesis h into two separate hypotheses h₁ : A and h₂ : B
which are each placed separately in two different goals. This means that we consider
when A and B are true separately.

We will now provide a few examples of logic in Lean. The statement we wish to prove
will follow after the word 'example' and our proof goes between the 'begin' and 'end'
commands. For any incomplete exercise, remove the sorry to begin the proof. 
-/

example (A : Prop) (h:A) : A:=
begin
exact h,
end

example (A B : Prop) (h : B) : A ∨ B :=
begin
right,
exact h,
end

example (A B : Prop) (h₁: A) (h₂: B) : A ∧ B :=
begin
split,
exact h₁,
exact h₂,
end

example (A : Prop) : A ∨ ¬ A :=
begin
by_cases h : A,
left,
exact h,
right, 
exact h,
end

example (A B : Prop) (h: A ∧ ¬ B) : ¬ B ∧ A :=
begin
cases h with h₁ h₂,
split, 
exact h₂,
exact h₁,
end

example (A B C : Prop) (h : (A ∧ B) ∨ C) : B ∨ C :=
begin
cases h with h₁ h₂,
cases h₁ with h₂ h₃,
left,
exact h₃,
right, 
exact h₂,
end

example (A B : Prop) : A ∧ B → A ∨ B :=
begin
intro h,
cases h with h₁ h₂,
left,
exact h₁,
end

example (A B : Prop): (A ∨ ¬ A) ∧ (B ∨ ¬B) :=
begin
split, 
by_cases h:A,
left,
exact h,
right,
exact h,
by_cases h:B,
left,
exact h,
right,
exact h,
end

theorem lawofcomm (A B : Prop) : A∧B ↔ B∧A:=
begin
split, --We consider the separate implications ⊢ A ∧ B → B ∧ A and ⊢B ∧ A → A ∧ B
intro h₁, --This lets us consider the hypothesis h₁: A ∧ B
cases h₁ with h₂ h₃, -- h₁:A ∧ B changes to h₂:A and h₃:B
split,--Instead of showing B ∧ A we show B and A separately
exact h₃, --Our goal, ⊢B is the same as our hypothesis h₃
exact h₂, --Our goal, ⊢A is the same as our hypothesis h₂ 
intro h₁, --Due to the symmetric nature of the proof, we just repeat what we've written above
cases h₁ with h₂ h₃,
split,
exact h₃,
exact h₂,
end

--Now it's time for you to have a go. Delete the sorry and continue the proofs.

example (A B : Prop) : A ∨ B ∨ ¬ A ∨ B :=
begin
sorry,
end

theorem lawofassoc (A B C : Prop) : A∧(B∧C) ↔ (A∧B)∧C:=
begin
sorry,
end

theorem lawofdist (A B C : Prop) : A∧(B∨C) ↔ (A∧B)∨(A∧C):=
begin
sorry,
end

theorem de_morgan1 (A B : Prop) : ¬ (A∨B) ↔ (¬A) ∧ (¬B) :=
begin
sorry,
end

theorem de_morgan2 (A B : Prop) : ¬(A∧B) ↔ (¬A)∨(¬B):=
begin
sorry,
end
