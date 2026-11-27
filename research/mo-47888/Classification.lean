import Binary
import OMAProofs.Multinomial

/-! # Classification by the number of categories

Introducing a new category with probability zero embeds every failure of
monotonicity, and every monotone lattice field, in the larger simplex.
Combined with the binary argument and the three-category witness, this gives
the exact classification for the original range of trial and category counts.
-/

namespace MultinomialClassification

open OMA.S_mo_47888
open OMA.MultinomialWitness

/-- Universal monotonicity preservation at fixed trial and category counts. -/
def preserves (n k : ℕ) : Prop :=
  ∀ f : (Fin k → ℤ) → Fin k → ℝ, fieldMonotone f →
    ∀ p q : Fin k → ℝ, onSimplex p → onSimplex q →
    0 ≤ ∑ j, (p j - q j) * (smooth n f p j - smooth n f q j)

private def tailCounts {k : ℕ} (x : Fin (k+1) → ℤ) : Fin k → ℤ := fun i => x i.succ

private def pad {k : ℕ} (p : Fin k → ℝ) : Fin (k+1) → ℝ := Fin.cons 0 p

private def padField {k : ℕ} (f : (Fin k → ℤ) → Fin k → ℝ) :
    (Fin (k+1) → ℤ) → Fin (k+1) → ℝ :=
  fun x => pad (f (tailCounts x))

private lemma pad_simplex {k : ℕ} {p : Fin k → ℝ} (hp : onSimplex p) : onSimplex (pad p) := by
  constructor
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [pad]
    · simpa [pad] using hp.1 j
  · simpa [pad, Fin.sum_univ_succ] using hp.2

private lemma pad_monotone {k : ℕ} {f : (Fin k → ℤ) → Fin k → ℝ}
    (hf : fieldMonotone f) : fieldMonotone (padField f) := by
  intro x y
  rw [Fin.sum_univ_succ]
  simpa [padField, pad, tailCounts] using hf (tailCounts x) (tailCounts y)

private lemma tail_bump {k : ℕ} (x : Fin (k+1) → ℤ) (j : Fin k) :
    tailCounts (bump x j.succ) = bump (tailCounts x) j := by
  funext i
  simp [tailCounts, bump]

private lemma average_padded {k : ℕ} (p : Fin k → ℝ) (h : (Fin k → ℤ) → ℝ)
    (n : ℕ) (x : Fin (k+1) → ℤ) :
    average (pad p) (fun y => h (tailCounts y)) n x = average p h n (tailCounts x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    simp only [average, Fin.sum_univ_succ, pad, Fin.cons_zero, Fin.cons_succ, zero_mul, zero_add]
    exact Finset.sum_congr rfl fun j _ => by rw [← tail_bump, ← ih]; rfl

private lemma smooth_padded {k : ℕ} (f : (Fin k → ℤ) → Fin k → ℝ)
    (p : Fin k → ℝ) (n : ℕ) (j : Fin k) :
    smooth n (padField f) (pad p) j.succ = smooth n f p j := by
  change average (pad p) (fun x => f (tailCounts x) j) n 0 =
    average p (fun x => f x j) n 0
  have hzero : tailCounts (0 : Fin (k+1) → ℤ) = 0 := by funext i; rfl
  simpa only [hzero] using average_padded p (fun x => f x j) n 0

/-- Preservation for a larger alphabet implies preservation for the smaller one. -/
theorem preserves_of_succ {n k : ℕ} (h : preserves n (k+1)) : preserves n k := by
  intro f hf p q hp hq
  have H := h (padField f) (pad_monotone hf) (pad p) (pad q) (pad_simplex hp) (pad_simplex hq)
  rw [Fin.sum_univ_succ] at H
  simp_rw [smooth_padded] at H
  simpa only [pad, Fin.cons_zero, Fin.cons_succ, sub_self, zero_mul, zero_add] using H

theorem three_fails (m : ℕ) : ¬preserves (m+1) 3 := by
  intro H
  exact (not_le_of_gt (monotonicity_fails_every_trial_count m))
    (H ridge ridge_monotone central outer central_simplex outer_simplex)

/-- For any positive number of trials and categories, universal preservation
holds exactly when the number of categories is at most two. -/
theorem classification {n k : ℕ} (hn : 0 < n) (hk : 0 < k) :
    preserves n k ↔ k ≤ 2 := by
  constructor
  · intro H
    by_contra hlarge
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    have hbad (t : ℕ) : ¬ preserves (m+1) (3+t) := by
      induction t with
      | zero => exact three_fails m
      | succ t ih => exact fun hs => ih (preserves_of_succ hs)
    exact hbad (k-3) (by simpa only [show 3 + (k-3) = k by omega] using H)
  · intro small
    interval_cases k
    · exact fun f _ p q hp hq => MultinomialBinary.one_category n f p q hp hq
    · exact MultinomialBinary.two_categories n

end MultinomialClassification

#print axioms MultinomialClassification.classification
