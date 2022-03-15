example (A B : Prop) : A ∨ B ∨ ¬ A ∨ B :=
begin
by_cases h:A,
left,
exact h,
right,
right,
left,
exact h,
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