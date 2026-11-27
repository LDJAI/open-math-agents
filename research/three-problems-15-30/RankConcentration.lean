import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Tactic.ByContra

namespace RankConcentration
open scoped BigOperators

/-- Concentration for an integer-valued score over a finite set of rankings.
The cutoff is explicit, so the inverse temperature has polynomial encoding size. -/
theorem expected_regret_bound {A : Type*} [DecidableEq A]
    (s : Finset A) (value : A → ℕ) (winner : A) (hw : winner ∈ s)
    (hm : ∀ a ∈ s, value a ≤ value winner) (base : ℕ) (hpositive : 1 ≤ base)
    (hbase : 4 * s.card * value winner ≤ base) :
    4 * (∑ a ∈ s, (value winner - value a) * base ^ value a) ≤
      ∑ a ∈ s, base ^ value a := by
  let top := value winner
  change 4 * (∑ a ∈ s, (top - value a) * base ^ value a) ≤ _
  by_cases ht : top = 0
  · simp [ht]
  have reg (a : A) (ha : a ∈ s) :
      (top - value a) * base ^ value a ≤ top * base ^ (top - 1) := by
    have hal : value a ≤ top := hm a ha
    by_cases he : value a = top
    · simp [he]
    · have he' : value a ≤ top - 1 := by omega
      exact Nat.mul_le_mul (Nat.sub_le ..) (Nat.pow_le_pow_right hpositive he')
  calc
    4 * (∑ a ∈ s, (top - value a) * base ^ value a)
        ≤ 4 * (∑ _a ∈ s, top * base ^ (top - 1)) :=
          Nat.mul_le_mul_left _ (Finset.sum_le_sum reg)
    _ = (4 * s.card * top) * base ^ (top - 1) := by simp [mul_assoc]
    _ ≤ base * base ^ (top - 1) := Nat.mul_le_mul_right _ hbase
    _ = base ^ top := by
      have ht' : top - 1 + 1 = top := by omega
      rw [mul_comm, ← pow_succ, ht']
    _ ≤ ∑ a ∈ s, base ^ value a :=
      Finset.single_le_sum (f := fun a => base ^ value a) (fun _ _ => Nat.zero_le _) hw

/-- For equally weighted comparisons the expected number of forward arcs equals
the sum of their marginal probabilities, expressed without division. -/
theorem sum_marginals {A E : Type*} (ranks : Finset A) (edges : Finset E)
    (indicator : A → E → ℕ) (w : A → ℕ) :
    (∑ e ∈ edges, ∑ a ∈ ranks, indicator a e * w a) =
    ∑ a ∈ ranks, (∑ e ∈ edges, indicator a e) * w a := by
  rw [Finset.sum_comm]
  simp only [Finset.sum_mul]

/-- Any event containing at least one quarter of the Gibbs mass contains
a maximizing ranking. The event is the comparison direction selected by
the additive-1/4 marginal oracle. -/
theorem selected_event_has_optimizer {A : Type*} [DecidableEq A]
    (s e : Finset A) (hs : e ⊆ s) (value : A → ℕ) (winner : A) (hw : winner ∈ s)
    (hm : ∀ a ∈ s, value a ≤ value winner)
    (base : ℕ) (hb : 4 * s.card < base)
    (hlarge : (∑ a ∈ s, base ^ value a) ≤ 4 * (∑ a ∈ e, base ^ value a)) :
    ∃ a ∈ e, value a = value winner := by
  classical
  by_contra! hn
  have hbase : 1 ≤ base := by omega
  have hstrict : ∀ a ∈ e, value a < value winner := by
    intro a ha
    exact lt_of_le_of_ne (hm a (hs ha)) (hn a ha)
  have hpos : 0 < base ^ value winner := pow_pos (by omega) _
  have hwt : base ^ value winner ≤ ∑ a ∈ s, base ^ value a :=
    Finset.single_le_sum (f := fun a => base ^ value a) (fun _ _ => Nat.zero_le _) hw
  have hne : e.Nonempty := by
    by_contra h
    have hzero : (∑ a ∈ e, base ^ value a) = 0 := by
      simp [Finset.not_nonempty_iff_eq_empty.mp h]
    rw [hzero, Nat.mul_zero] at hlarge
    omega
  obtain ⟨a, ha⟩ := hne
  have htop : 0 < value winner := Nat.zero_lt_of_lt (hstrict a ha)
  have below : (∑ a ∈ e, base ^ value a) ≤ e.card * base ^ (value winner - 1) := by
    calc
      _ ≤ ∑ _a ∈ e, base ^ (value winner - 1) := by
        apply Finset.sum_le_sum
        intro a ha
        exact Nat.pow_le_pow_right hbase (by have := hstrict a ha; omega)
      _ = _ := by simp
  have hcard := Finset.card_le_card hs
  have hlt : 4 * e.card < base := by omega
  have hp : 0 < base ^ (value winner - 1) := pow_pos (by omega) _
  have hslt : (4 * e.card) * base ^ (value winner - 1) <
      base * base ^ (value winner - 1) := Nat.mul_lt_mul_of_pos_right hlt hp
  have hpow : base * base ^ (value winner - 1) = base ^ value winner := by
    have h : value winner - 1 + 1 = value winner := by omega
    rw [mul_comm, ← pow_succ, h]
  rw [hpow, mul_assoc] at hslt
  omega

/-- When an original maximizer obeys every decision, optimality for the sum
of score and number of decisions obeyed forces both separate maxima. -/
theorem bonus_maximizer {k score best kept : ℕ}
    (hbest : score ≤ best) (hkept : kept ≤ k)
    (h : best + k ≤ score + kept) :
    score = best ∧ kept = k := by omega

end RankConcentration

#print axioms RankConcentration.expected_regret_bound
#print axioms RankConcentration.sum_marginals

#print axioms RankConcentration.selected_event_has_optimizer
#print axioms RankConcentration.bonus_maximizer
