import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace GibbsRanking
open scoped BigOperators

/-- The expected regret of a finite Gibbs distribution with weights proportional
to b^score, times log b, is at most log(number of states). Multiplication
by the partition function avoids division. -/
theorem gibbs_regret {A : Type*} [DecidableEq A] (s : Finset A) (score : A → ℕ)
    (winner : A) (hw : winner ∈ s) (b : ℝ) (hb : 0 < b) :
    (∑ a ∈ s, b ^ score a * ((score winner : ℝ) - score a)) * Real.log b ≤
    (∑ a ∈ s, b ^ score a) * Real.log s.card := by
  let Z : ℝ := ∑ a ∈ s, b ^ score a
  let N : ℝ := s.card
  have npos : 0 < N := by
    dsimp [N]
    exact_mod_cast Finset.card_pos.mpr ⟨winner, hw⟩
  have winle : b ^ score winner ≤ Z :=
    Finset.single_le_sum (f := fun a => b ^ score a) (fun _ _ => by positivity) hw
  have zpos : 0 < Z := lt_of_lt_of_le (pow_pos hb _) winle
  have winlog : (score winner : ℝ) * Real.log b ≤ Real.log Z := by
    simpa [Real.log_pow] using Real.log_le_log (pow_pos hb _) winle
  have term (a : A) (ha : a ∈ s) :
      b ^ score a * ((score winner : ℝ) - score a) * Real.log b ≤
      b ^ score a * Real.log N + (Z / N - b ^ score a) := by
    let w := b ^ score a
    have wpos : 0 < w := pow_pos hb _
    have wlog : Real.log w = (score a : ℝ) * Real.log b := Real.log_pow _ _
    have hlog := Real.log_le_sub_one_of_pos (x := Z / (N * w)) (by positivity)
    rw [Real.log_div zpos.ne' (mul_pos npos wpos).ne', Real.log_mul npos.ne' wpos.ne'] at hlog
    have h := mul_le_mul_of_nonneg_left hlog wpos.le
    have halg : w * (Z / (N*w) - 1) = Z/N - w := by
      field_simp
    rw [halg, wlog] at h
    have hwin := mul_le_mul_of_nonneg_left winlog wpos.le
    change w * ((score winner : ℝ) - score a) * Real.log b ≤ _
    change _ ≤ w * Real.log N + (Z / N - w)
    nlinarith only [h, hwin]
  have hmass : (∑ _a ∈ s, Z/N) = Z := by
    simp [N, ← Nat.cast_smul_eq_nsmul ℝ, smul_eq_mul]
    field_simp [show (s.card : ℝ) ≠ 0 from npos.ne']
  have summed := Finset.sum_le_sum term
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
      ← Finset.sum_mul, hmass] at summed
  change _ ≤ _ * Real.log N
  simpa [Z] using summed

end GibbsRanking

#print axioms GibbsRanking.gibbs_regret
