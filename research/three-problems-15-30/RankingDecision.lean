import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace RankingDecision
open scoped BigOperators

/-- The selected orientation contains an optimal ranking if it has more
probability mass than the expected integer loss of the ranking. -/
theorem orientation_contains_optimum {A : Type*} [DecidableEq A]
    (allRanks selected : Finset A) (hs : selected ⊆ allRanks)
    (mass : A → ℚ) (hm : ∀ a ∈ allRanks, 0 ≤ mass a)
    (score : A → ℕ) (best : ℕ) (hb : ∀ a ∈ allRanks, score a ≤ best)
    (hgap : (∑ a ∈ allRanks, mass a * (best - score a : ℕ)) <
              ∑ a ∈ selected, mass a) :
    ∃ a ∈ selected, score a = best := by
  by_contra! h
  have one (a : A) (ha : a ∈ selected) : (1 : ℚ) ≤ (best - score a : ℕ) := by
    have hslt := lt_of_le_of_ne (hb a (hs ha)) (h a ha)
    exact_mod_cast (show 1 ≤ best - score a by omega)
  have hle : (∑ a ∈ selected, mass a) ≤ ∑ a ∈ selected, mass a * (best - score a : ℕ) := by
    apply Finset.sum_le_sum
    intro a ha
    exact le_mul_of_one_le_right (hm a (hs ha)) (one a ha)
  have hle' : (∑ a ∈ selected, mass a * (best - score a : ℕ)) ≤
                ∑ a ∈ allRanks, mass a * (best - score a : ℕ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hs (fun a ha _ => mul_nonneg (hm a ha) (by positivity))
  exact (not_lt_of_ge (hle.trans hle')) hgap

/-- A ±1/4 estimate selects a comparison event of probability ≥1/4. -/
theorem quarter_oracle_branch (actual estimate : ℚ)
    (herr : |actual - estimate| ≤ 1/4) :
    1/4 ≤ (if 1/2 ≤ estimate then actual else 1-actual) := by
  rw [abs_le] at herr
  split <;> linarith

end RankingDecision

#print axioms RankingDecision.orientation_contains_optimum
#print axioms RankingDecision.quarter_oracle_branch
