import OMAStatements.S_mo_47888
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic

/-!
# A monotone ridge field whose multinomial smoothing is not monotone

A single field and a single pair of probabilities witness failure for every
positive trial count. Credit: @LDJAI with OpenAI Codex.
-/

namespace OMA.MultinomialWitness

open OMA.S_mo_47888

def score (x : Fin 3 → ℤ) : ℝ := (x 2 : ℝ) - (x 0 : ℝ)

def hinge (x : Fin 3 → ℤ) : ℝ := max (score x) 0

def ridge (x : Fin 3 → ℤ) : Fin 3 → ℝ := ![-hinge x, 0, hinge x]

def central : Fin 3 → ℝ := ![0, 1, 0]

noncomputable def outer : Fin 3 → ℝ := ![3 / 4, 0, 1 / 4]

theorem central_simplex : onSimplex central := by
  constructor
  · intro j
    fin_cases j <;> norm_num [central]
  · norm_num [central, Fin.sum_univ_succ]

theorem outer_simplex : onSimplex outer := by
  constructor
  · intro j
    fin_cases j <;> norm_num [outer]
  · norm_num [outer, Fin.sum_univ_succ]

theorem ridge_monotone : fieldMonotone ridge := by
  intro x y
  have identity : (∑ j, ((x j : ℝ) - (y j : ℝ)) * (ridge x j - ridge y j)) =
      (score x - score y) * (hinge x - hinge y) := by
    simp [Fin.sum_univ_succ, ridge, score]
    ring
  rw [identity]
  rcases le_total (score x) (score y) with h | h
  · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr h) (sub_nonpos.mpr (max_le_max h le_rfl))
  · exact mul_nonneg (sub_nonneg.mpr h) (sub_nonneg.mpr (max_le_max h le_rfl))

theorem average_neg {k : ℕ} (p : Fin k → ℝ) (h : (Fin k → ℤ) → ℝ) (n : ℕ) (x : Fin k → ℤ) :
    average p (fun z => -(h z)) n x = -(average p h n x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    simp only [average, ih, mul_neg, Finset.sum_neg_distrib]

theorem average_central (n : ℕ) (x : Fin 3 → ℤ) : average central hinge n x = hinge x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    simp only [average, ih]
    simp [Fin.sum_univ_succ, central, hinge, score, bump]

theorem average_outer_nonneg (n : ℕ) (x : Fin 3 → ℤ) : 0 ≤ average outer hinge n x := by
  induction n generalizing x with
  | zero => exact le_max_right _ _
  | succ n ih => exact Finset.sum_nonneg fun j _ => mul_nonneg (outer_simplex.1 j) (ih _)

theorem score_last (x : Fin 3 → ℤ) : score (bump x 2) = score x + 1 := by
  simp [score, bump]
  ring

theorem outer_step (n : ℕ) (x : Fin 3 → ℤ) :
    average outer hinge (n+1) x =
      3/4 * average outer hinge n (bump x 0) + 1/4 * average outer hinge n (bump x 2) := by
  rw [average, Fin.sum_univ_three]
  simp [outer]

theorem positive_continuation (n : ℕ) (x : Fin 3 → ℤ) (hx : 0 < score x) :
    0 < average outer hinge n x := by
  induction n generalizing x with
  | zero => exact lt_of_lt_of_le hx (le_max_left _ _)
  | succ n ih =>
    have hp := ih (bump x 2) (by rw [score_last]; linarith)
    have hn := average_outer_nonneg n (bump x 0)
    rw [outer_step]
    linarith

theorem average_outer_strict (n : ℕ) : 0 < average outer hinge (n+1) 0 := by
  have hp := positive_continuation n (bump 0 2) (by rw [score_last]; norm_num [score])
  have hn := average_outer_nonneg n (bump 0 0)
  rw [outer_step]
  linarith

theorem average_zero {k : ℕ} (p : Fin k → ℝ) (n : ℕ) (x : Fin k → ℤ) :
    average p (fun _ => 0) n x = 0 := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => simp [average, ih]

theorem monotonicity_fails_every_trial_count (n : ℕ) :
    (∑ j, (central j - outer j) * (smooth (n+1) ridge central j - smooth (n+1) ridge outer j)) < 0 := by
  have hp := average_outer_strict n
  have hz : hinge 0 = 0 := by simp [hinge,score]
  have c0 (r : Fin 3 → ℝ) : smooth (n+1) ridge r 0 = -average r hinge (n+1) 0 := average_neg _ _ _ _
  have c1 (r : Fin 3 → ℝ) : smooth (n+1) ridge r 1 = 0 := average_zero _ _ _
  have c2 (r : Fin 3 → ℝ) : smooth (n+1) ridge r 2 = average r hinge (n+1) 0 := rfl
  rw [Fin.sum_univ_three, c0, c0, c1, c1, c2, c2, average_central, hz]
  change (0 - 3/4) * (-0 - -average outer hinge (n+1) 0) + (1-0) * (0-0) +
    (0 - 1/4) * (0-average outer hinge (n+1) 0) < 0
  linarith

end OMA.MultinomialWitness

open OMA.MultinomialWitness

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_47888.main) := by
  intro conjecture
  exact (not_le_of_gt (monotonicity_fails_every_trial_count 0))
    (conjecture 1 3 (by decide) (by decide) ridge ridge_monotone central outer central_simplex outer_simplex)
