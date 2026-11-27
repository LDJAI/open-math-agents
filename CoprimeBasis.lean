import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic

/-!
# Coprime-base support test

A factor label need not be prime. Distinct labels must be coprime, and a
label that occurs must exceed one. Exponents and subset signs are kept
separate, so this lemma applies directly to composite factors in a coprime
base and does not use the arithmetic Möbius function on those factors.
-/

namespace CoprimeTriangles

open Finset
open scoped BigOperators

/-- Disjoint label supports exactly detect coprimality of the reconstructed weights. -/
theorem basis_support_test (s t : Finset ℕ) (a b : ℕ → ℕ)
    (hbase : ∀ i ∈ s, ∀ j ∈ t, i ≠ j → Nat.Coprime i j)
    (hlarge : ∀ i ∈ s, 1 < i)
    (ha : ∀ i ∈ s, 0 < a i) (hb : ∀ i ∈ t, 0 < b i) :
    (Nat.Coprime (∏ i ∈ s, i ^ a i) (∏ j ∈ t, j ^ b j)) ↔ Disjoint s t := by
  rw [Nat.coprime_prod_left_iff, Finset.disjoint_left]
  constructor
  · intro hc i his hit
    have h := (Nat.coprime_prod_right_iff.mp (hc i his)) i hit
    rw [Nat.coprime_pow_left_iff (ha i his), Nat.coprime_pow_right_iff (hb i hit)] at h
    have h1 : i = 1 := by simpa [Nat.Coprime] using h
    exact (hlarge i his).ne' h1
  · intro hd i his
    apply Nat.coprime_prod_right_iff.mpr
    intro j hjt
    rw [Nat.coprime_pow_left_iff (ha i his), Nat.coprime_pow_right_iff (hb j hjt)]
    exact hbase i his j hjt (fun h => hd his (h ▸ hjt))

/-- An endpoint's signed sum for general coprime-basis factors. -/
theorem basis_endpoint_sum (s t : Finset ℕ) (a b : ℕ → ℕ)
    (hbase : ∀ i ∈ s, ∀ j ∈ t, i ≠ j → Nat.Coprime i j)
    (hlarge : ∀ i ∈ s, 1 < i)
    (ha : ∀ i ∈ s, 0 < a i) (hb : ∀ i ∈ t, 0 < b i) :
    (∑ u ∈ (s ∩ t).powerset, (-1 : ℤ) ^ u.card) =
      if Nat.Coprime (∏ i ∈ s, i ^ a i) (∏ j ∈ t, j ^ b j) then 1 else 0 := by
  simp only [Finset.sum_powerset_neg_one_pow_card, ← Finset.disjoint_iff_inter_eq_empty,
      basis_support_test s t a b hbase hlarge ha hb]

/-- The product of the selected factors is a collision-free identifier for a subset. -/
theorem subset_product_injective (base : Finset ℕ)
    (hcop : ∀ i ∈ base, ∀ j ∈ base, i ≠ j → Nat.Coprime i j)
    (hbig : ∀ i ∈ base, 1 < i) {s t : Finset ℕ} (hs : s ⊆ base) (ht : t ⊆ base)
    (hprod : (∏ i ∈ s, i) = ∏ i ∈ t, i) : s = t := by
  classical
  have mark (u : Finset ℕ) (hu : u ⊆ base) (p : ℕ) (hp : p ∈ base) :
      (∏ i ∈ u, i).Coprime p ↔ p ∉ u := by
    have h := basis_support_test u {p} (fun _ => 1) (fun _ => 1)
      (fun i hi j hj => hcop i (hu hi) j (by simpa [Finset.mem_singleton.mp hj] using hp))
      (fun i hi => hbig i (hu hi)) (by simp) (by simp)
    simpa using h
  ext p
  by_cases hp : p ∈ base
  · have h : p ∉ s ↔ p ∉ t := by rw [← mark s hs p hp, ← mark t ht p hp, hprod]
    tauto
  · exact iff_of_false (fun i => hp (hs i)) (fun j => hp (ht j))

end CoprimeTriangles
