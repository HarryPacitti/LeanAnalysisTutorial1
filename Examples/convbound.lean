import data.real.basic
import data.list.range


def converges_to (s : ℕ → ℝ) (a : ℝ) :=
∀ ε > 0, ∃ N, ∀ n ≥ N, abs (s n - a) < ε

variables {s : ℕ → ℝ} {a : ℝ}

theorem exists_le_of_converges_to_ev (cs : converges_to s a) :
  ∃ N b, ∀ n, N ≤ n → s n < b :=
begin
cases cs 1 zero_lt_one with N h,
use [N , a + 1],
intros n h₁,
specialize @h n h₁,
have h₂: s n - a ≤ abs(s n - a),
apply le_abs_self,
suffices h₃: s n - a < 1,
exact sub_lt_iff_lt_add'.mp h₃,
apply lt_of_le_of_lt h₂ h,
end

theorem exists_le_of_converges (cs : converges_to s a) :
  ∃ b, ∀ n, s n < b :=
begin
cases cs 1 zero_lt_one with N h,
let l := list.map (λ n, s ↑n) (list.range N.succ),
have : l.maximum ≠ ⊥,
{ intro hl, rw [← with_bot.none_eq_bot, list.maximum_eq_none] at hl,
  refine (list.ne_nil_of_length_eq_succ _) hl,
    exact N,
    { rw list.length_map, exact list.length_range (nat.succ N) },
 },
let lm : ℝ := with_bot.unbot l.maximum this,
have : l.maximum = ↑lm,
  exact ((list.maximum l).coe_unbot this).symm,

use max lm a + 1,
intro n,
cases nat.lt_or_ge n N with hn hn,
{ apply lt_of_le_of_lt _ (lt_add_one (max lm a)),
  apply le_trans _ (le_max_left _ _),
  apply list.le_maximum_of_mem _ this,
  rw list.mem_map,
  use n, split,
    rw list.mem_range,
    exact lt_of_lt_of_le hn (nat.le_succ N),
    simp only [nat.cast_id], },
{ have : a + 1 ≤ max lm a + 1,
    simp only [add_le_add_iff_right, le_max_iff, le_refl, or_true],
  refine lt_of_lt_of_le _ this,
  let hn := (abs_lt.mp (h n hn)).right,
  apply lt_add_of_neg_add_lt_left ,
  rw [add_comm, ← sub_eq_add_neg],
  exact hn }
end
