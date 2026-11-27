import OMAStatements.S_mo_47888
import Mathlib.Tactic

/-! # Multinomial smoothing of additive routing costs

For each link choose the set of routes using it. Its load changes by either
zero or one on each draw, so its law depends only on the total route mass
using that link. Summation over links then preserves the monotonicity inequality.
-/

namespace MultinomialRouting

open OMA.S_mo_47888

/-- Total probability of those routes which use one link. -/
noncomputable def mass {k : ℕ} (S : Finset (Fin k)) (p : Fin k → ℝ) : ℝ :=
  ∑ j, if j ∈ S then p j else 0

/-- Number of sampled routes using this link, with integer starting counts. -/
def load {k : ℕ} (S : Finset (Fin k)) (x : Fin k → ℤ) : ℤ := ∑ j ∈ S, x j

/-- Expected scalar cost after n independent Bernoulli(t) increments. -/
noncomputable def binomialCost (t : ℝ) (c : ℤ → ℝ) : ℕ → ℤ → ℝ
  | 0, z => c z
  | n+1, z => t * binomialCost t c n (z+1) + (1-t) * binomialCost t c n z

private theorem load_bump {k : ℕ} (S : Finset (Fin k)) (x : Fin k → ℤ) (j : Fin k) :
    load S (bump x j) = load S x + if j ∈ S then 1 else 0 := by
  simp [load, bump, Finset.sum_add_distrib]

private theorem mass_bounds {k : ℕ} (S : Finset (Fin k)) {p : Fin k → ℝ}
    (hp : onSimplex p) : 0 ≤ mass S p ∧ mass S p ≤ 1 := by
  constructor
  · exact Finset.sum_nonneg fun j _ => by split_ifs <;> simp [hp.1 j]
  · rw [← hp.2]
    exact Finset.sum_le_sum fun j _ => by split_ifs <;> simp [hp.1 j]

private theorem weighted_split {k : ℕ} (S : Finset (Fin k)) {p : Fin k → ℝ}
    (hp : onSimplex p) (a b : ℝ) :
    (∑ j, p j * (if j ∈ S then a else b)) = mass S p * a + (1-mass S p) * b := by
  calc
    _ = ∑ j, ((if j ∈ S then p j else 0) * (a-b) + p j * b) := by
      apply Finset.sum_congr rfl
      intro j _
      split_ifs <;> ring
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, hp.2]
      unfold mass
      ring

/-- The multinomial link-load expectation is a scalar binomial expectation. -/
theorem average_load {k : ℕ} (S : Finset (Fin k)) (c : ℤ → ℝ) {p : Fin k → ℝ}
    (hp : onSimplex p) (n : ℕ) (x : Fin k → ℤ) :
    average p (fun y => c (load S y)) n x = binomialCost (mass S p) c n (load S x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    simp only [average, ih, load_bump, binomialCost]
    convert weighted_split S hp (binomialCost (mass S p) c n (load S x+1))
      (binomialCost (mass S p) c n (load S x)) using 1
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> simp

private theorem increasing_load {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1) {c : ℤ → ℝ}
    (hc : Monotone c) (n : ℕ) : Monotone (binomialCost t c n) := by
  induction n with
  | zero => exact hc
  | succ n ih =>
    intro z w hzw
    exact add_le_add (mul_le_mul_of_nonneg_left (ih (by omega : z+1 ≤ w+1)) ht)
      (mul_le_mul_of_nonneg_left (ih hzw) (by linarith))

private theorem increasing_mass {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ 1)
    {c : ℤ → ℝ} (hc : Monotone c) (n : ℕ) (z : ℤ) :
    binomialCost s c n z ≤ binomialCost t c n z := by
  induction n generalizing z with
  | zero => exact le_rfl
  | succ n ih =>
    simp only [binomialCost]
    calc
      _ ≤ s * binomialCost t c n (z+1) + (1-s) * binomialCost t c n z :=
        add_le_add (mul_le_mul_of_nonneg_left (ih (z+1)) hs)
          (mul_le_mul_of_nonneg_left (ih z) (by linarith))
      _ ≤ _ := by
        have hz := increasing_load (hs.trans hst) ht hc n (by omega : z ≤ z+1)
        nlinarith only [mul_nonneg (sub_nonneg.mpr hst) (sub_nonneg.mpr hz)]

/-- Increasing the total probability of the routes using a link increases its
expected nondecreasing cost, for any number of draws and initial counts. -/
theorem link_cost_monotone {k : ℕ} (S : Finset (Fin k)) {c : ℤ → ℝ} (hc : Monotone c)
    {p q : Fin k → ℝ} (hp : onSimplex p) (hq : onSimplex q) (hle : mass S p ≤ mass S q)
    (n : ℕ) (x : Fin k → ℤ) :
    average p (fun y => c (load S y)) n x ≤ average q (fun y => c (load S y)) n x := by
  rw [average_load S c hp, average_load S c hq]
  exact increasing_mass (mass_bounds S hp).1 hle (mass_bounds S hq).2 hc n _


/-- A finite sum of observables can be averaged one summand at a time. -/
theorem average_finset_sum {k : ℕ} {ι : Type*} (p : Fin k → ℝ) (s : Finset ι)
    (F : ι → (Fin k → ℤ) → ℝ) (n : ℕ) (x : Fin k → ℤ) :
    average p (fun y => ∑ a ∈ s, F a y) n x = ∑ a ∈ s, average p (F a) n x := by
  induction n generalizing x with
  | zero => simp [average]
  | succ n ih =>
    simp only [average, ih, Finset.mul_sum]
    exact Finset.sum_comm

/-- Constants can be pulled out of a conditional average. -/
theorem average_const_mul {k : ℕ} (p : Fin k → ℝ) (c : ℝ)
    (h : (Fin k → ℤ) → ℝ) (n : ℕ) (x : Fin k → ℤ) :
    average p (fun y => c * h y) n x = c * average p h n x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    simp only [average, ih, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring

/-- Route costs built additively from resource terms can be averaged resource by resource. -/
theorem smooth_resource_sum {k : ℕ} {ι : Type*} (s : Finset ι)
    (w : ι → Fin k → ℝ) (h : ι → (Fin k → ℤ) → ℝ)
    (n : ℕ) (p : Fin k → ℝ) (j : Fin k) :
    smooth n (fun x j => ∑ a ∈ s, w a j * h a x) p j =
      ∑ a ∈ s, w a j * average p (h a) n 0 := by
  unfold smooth
  rw [average_finset_sum]
  exact Finset.sum_congr rfl fun a _ => average_const_mul p (w a j) (h a) n 0

/-- Route cost is the sum of the costs of all links on the route. -/
noncomputable def pullCost {k : ℕ} {L : Type*} [Fintype L] (S : L → Finset (Fin k))
    (u : L → ℝ) (j : Fin k) : ℝ := ∑ e, if j ∈ S e then u e else 0

/-- The original lattice vector field of route costs. -/
noncomputable def routingField {k : ℕ} {L : Type*} [Fintype L] (S : L → Finset (Fin k))
    (c : L → ℤ → ℝ) (x : Fin k → ℤ) : Fin k → ℝ :=
  pullCost S (fun e => c e (load (S e) x))

private theorem average_zero {k : ℕ} (p : Fin k → ℝ) (n : ℕ) (x : Fin k → ℤ) :
    average p (fun _ => 0) n x = 0 := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => simp [average, ih]

/-- Under multinomial sampling, route costs are the sums of binomially
averaged link costs. -/
theorem smooth_routing {k : ℕ} {L : Type*} [Fintype L] (S : L → Finset (Fin k))
    (c : L → ℤ → ℝ) {p : Fin k → ℝ} (hp : onSimplex p) (n : ℕ) (j : Fin k) :
    smooth n (routingField S c) p j =
      pullCost S (fun e => binomialCost (mass (S e) p) (c e) n 0) j := by
  unfold smooth routingField pullCost
  rw [average_finset_sum p Finset.univ
    (fun e x => if j ∈ S e then c e (load (S e) x) else 0)]
  apply Finset.sum_congr rfl
  intro e _
  by_cases he : j ∈ S e
  · simp only [he, if_true, average_load (S e) (c e) hp]
    simp [load]
  · simp only [he, if_false, average_zero]

private theorem dot_pull {k : ℕ} {L : Type*} [Fintype L] (S : L → Finset (Fin k))
    (p q : Fin k → ℝ) (u v : L → ℝ) :
    ∑ j, (p j-q j) * (pullCost S u j - pullCost S v j) =
      ∑ e, (mass (S e) p - mass (S e) q) * (u e - v e) := by
  calc
    _ = ∑ j, ∑ e, (p j-q j) *
          ((if j ∈ S e then u e else 0) - (if j ∈ S e then v e else 0)) := by
      simp only [pullCost, ← Finset.sum_sub_distrib, Finset.mul_sum]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e _
      rw [mass, mass, ← Finset.sum_sub_distrib, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      by_cases h : j ∈ S e <;> simp [h]

/-- In every dimension, the multinomial expectation of additive routing costs
with nondecreasing link costs is a monotone map on the probability simplex. -/
theorem routing_monotone {k : ℕ} {L : Type*} [Fintype L] (S : L → Finset (Fin k))
    (c : L → ℤ → ℝ) (hc : ∀ e, Monotone (c e)) (n : ℕ)
    {p q : Fin k → ℝ} (hp : onSimplex p) (hq : onSimplex q) :
    0 ≤ ∑ j, (p j-q j) * (smooth n (routingField S c) p j - smooth n (routingField S c) q j) := by
  simp_rw [smooth_routing S c hp, smooth_routing S c hq]
  rw [dot_pull]
  apply Finset.sum_nonneg
  intro e _
  rcases le_total (mass (S e) p) (mass (S e) q) with h | h
  · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr h) (sub_nonpos.mpr
      (increasing_mass (mass_bounds (S e) hp).1 h (mass_bounds (S e) hq).2 (hc e) n 0))
  · exact mul_nonneg (sub_nonneg.mpr h) (sub_nonneg.mpr
      (increasing_mass (mass_bounds (S e) hq).1 h (mass_bounds (S e) hp).2 (hc e) n 0))

end MultinomialRouting

#print axioms MultinomialRouting.average_load
#print axioms MultinomialRouting.link_cost_monotone
#print axioms MultinomialRouting.routing_monotone
