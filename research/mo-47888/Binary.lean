import OMAStatements.S_mo_47888
import Mathlib.Tactic

/-! # Universal preservation for two categories

The scalar difference of the two field values can only increase when one count
is moved from category 1 to category 0. Independent sampling preserves this
directional order, both in the starting state and in the probability parameter.
-/

namespace MultinomialBinary

open OMA.S_mo_47888

private abbrev Counts := Fin 2 → ℤ
private def orderedContrast (h : Counts → ℝ) : Prop :=
  ∀ x, h (bump x 1) ≤ h (bump x 0)

private lemma bumps_commute {k : ℕ} (x : Fin k → ℤ) (i j : Fin k) :
    bump (bump x i) j = bump (bump x j) i := by
  funext t
  simp only [bump]
  ring

private lemma ordered_of_field {f : Counts → Fin 2 → ℝ} (hf : fieldMonotone f) :
    orderedContrast (fun x => f x 0 - f x 1) := by
  intro x
  have h := hf (bump x 0) (bump x 1)
  have h0 : ((bump x 0 0 : ℤ) : ℝ) - (bump x 1 0 : ℤ) = 1 := by simp [bump]
  have h1 : ((bump x 0 1 : ℤ) : ℝ) - (bump x 1 1 : ℤ) = -1 := by simp [bump]
  rw [Fin.sum_univ_two, h0, h1] at h
  dsimp
  linarith only [h]

private lemma average_ordered {h : Counts → ℝ} (ho : orderedContrast h)
    {p : Fin 2 → ℝ} (hp : ∀ j, 0 ≤ p j) (n : ℕ) :
    orderedContrast (average p h n) := by
  induction n with
  | zero => exact ho
  | succ n ih =>
    intro x
    simp only [average]
    apply Finset.sum_le_sum
    intro j _
    apply mul_le_mul_of_nonneg_left _ (hp j)
    rw [bumps_commute x 1 j, bumps_commute x 0 j]
    exact ih (bump x j)

private lemma increase_probability {h : Counts → ℝ} (ho : orderedContrast h)
    {p q : Fin 2 → ℝ} (hp : onSimplex p) (hq : onSimplex q) (hle : p 0 ≤ q 0)
    (n : ℕ) (x : Counts) : average p h n x ≤ average q h n x := by
  induction n generalizing x with
  | zero => exact le_rfl
  | succ n ih =>
    simp only [average]
    calc
      _ ≤ ∑ j, p j * average q h n (bump x j) := Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_left (ih (bump x j)) (hp.1 j)
      _ ≤ _ := by
        have s := average_ordered ho hq.1 n x
        have pSum := hp.2
        have qSum := hq.2
        rw [Fin.sum_univ_two] at pSum qSum
        rw [Fin.sum_univ_two, Fin.sum_univ_two, show p 1 = 1 - p 0 by linarith,
          show q 1 = 1 - q 0 by linarith]
        nlinarith only [mul_nonneg (sub_nonneg.mpr hle) (sub_nonneg.mpr s)]

private lemma average_sub {k : ℕ} (p : Fin k → ℝ) (h g : (Fin k → ℤ) → ℝ) (n : ℕ)
    (x : Fin k → ℤ) : average p (fun y => h y - g y) n x =
    average p h n x - average p g n x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => simp only [average, ih, mul_sub, Finset.sum_sub_distrib]

/-- The full monotonicity inequality holds for every number of trials when k = 2. -/
theorem two_categories (n : ℕ) (f : (Fin 2 → ℤ) → Fin 2 → ℝ)
    (hf : fieldMonotone f) (p q : Fin 2 → ℝ) (hp : onSimplex p) (hq : onSimplex q) :
    0 ≤ ∑ j, (p j - q j) * (smooth n f p j - smooth n f q j) := by
  have mono (a b : Fin 2 → ℝ) (ha : onSimplex a) (hb : onSimplex b) (h : a 0 ≤ b 0) :
      smooth n f a 0 - smooth n f a 1 ≤ smooth n f b 0 - smooth n f b 1 := by
    have t := increase_probability (ordered_of_field hf) ha hb h n 0
    simpa only [average_sub, smooth] using t
  have pSum := hp.2
  have qSum := hq.2
  rw [Fin.sum_univ_two] at pSum qSum
  rw [Fin.sum_univ_two, show p 1 - q 1 = -(p 0 - q 0) by linarith]
  rcases le_total (p 0) (q 0) with h | h
  · nlinarith only [mul_nonneg (sub_nonneg.mpr h) (sub_nonneg.mpr (mono p q hp hq h))]
  · nlinarith only [mul_nonneg (sub_nonneg.mpr h) (sub_nonneg.mpr (mono q p hq hp h))]

/-- There is only one probability vector with one category. -/
theorem one_category (n : ℕ) (f : (Fin 1 → ℤ) → Fin 1 → ℝ)
    (p q : Fin 1 → ℝ) (hp : onSimplex p) (hq : onSimplex q) :
    0 ≤ ∑ j, (p j - q j) * (smooth n f p j - smooth n f q j) := by
  have peq : p = q := by
    funext j
    fin_cases j
    simpa using hp.2.trans hq.2.symm
  simp [peq]

end MultinomialBinary

#print axioms MultinomialBinary.two_categories
#print axioms MultinomialBinary.one_category
