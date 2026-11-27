import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Tactic

/-!
# Endpoint labels for triangles with pairwise coprime edge weights

A label at a vertex is a subset of the prime factors shared by its two
incident edge weights. Its sign is the parity of its cardinality. The
three endpoint labels vary independently. Summing their joint sign counts
each valid triangle once and cancels every invalid triangle.
-/

namespace CoprimeTriangles

open Finset
open scoped BigOperators

/-- The endpoint labels permitted by the two incident edge weights. -/
def labels (a b : ℕ) : Finset (Finset ℕ) :=
  (a.primeFactors ∩ b.primeFactors).powerset

theorem label_iff {a b : ℕ} {s : Finset ℕ} :
    s ∈ labels a b ↔ s ⊆ a.primeFactors ∧ s ⊆ b.primeFactors := by
  simp [labels, Finset.subset_inter_iff]

/-- A lifted edge carries a label at either endpoint. -/
def liftEdge (w : ℕ) (s t : Finset ℕ) : Prop :=
  s ⊆ w.primeFactors ∧ t ⊆ w.primeFactors

theorem lift_triangle_iff (a b c : ℕ) (s t u : Finset ℕ) :
    (liftEdge a u s ∧ liftEdge b s t ∧ liftEdge c t u) ↔
      (s ∈ labels a b ∧ t ∈ labels b c ∧ u ∈ labels c a) := by
  simp only [liftEdge, label_iff]
  tauto

def paritySign (s : Finset ℕ) : ℤ := (-1) ^ s.card

theorem endpoint_sum {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    ∑ s ∈ labels a b, paritySign s = if a.Coprime b then 1 else 0 := by
  simp only [labels, paritySign, Finset.sum_powerset_neg_one_pow_card,
    ← Finset.disjoint_iff_inter_eq_empty, Nat.disjoint_primeFactors ha.ne' hb.ne']

/-- The signed multiplicity in the expanded graph of a single original triangle. -/
def signedTriangle (a b c : ℕ) : ℤ :=
  ∑ s ∈ labels a b, ∑ t ∈ labels b c, ∑ u ∈ labels c a,
    paritySign s * paritySign t * paritySign u

theorem triangle_indicator {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    signedTriangle a b c =
      if a.Coprime b ∧ b.Coprime c ∧ c.Coprime a then 1 else 0 := by
  have expand : signedTriangle a b c = (∑ s ∈ labels a b, paritySign s) *
      (∑ t ∈ labels b c, paritySign t) * (∑ u ∈ labels c a, paritySign u) := by
    unfold signedTriangle
    simp_rw [← Finset.mul_sum, mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul]
  rw [expand]
  rw [endpoint_sum ha hb, endpoint_sum hb hc, endpoint_sum hc ha]
  split_ifs <;> simp_all

/-- Summing signed multiplicities over any triangle enumeration yields its exact valid count. -/
theorem count_valid {ι : Type*} (ts : Finset ι) (a b c : ι → ℕ)
    (hw : ∀ i ∈ ts, 0 < a i ∧ 0 < b i ∧ 0 < c i) :
    ∑ i ∈ ts, signedTriangle (a i) (b i) (c i) =
      ((ts.filter fun i => (a i).Coprime (b i) ∧ (b i).Coprime (c i) ∧
        (c i).Coprime (a i)).card : ℤ) := by
  calc
    _ = ∑ i ∈ ts, (if (a i).Coprime (b i) ∧ (b i).Coprime (c i) ∧
          (c i).Coprime (a i) then (1 : ℤ) else 0) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact triangle_indicator (hw i hi).1 (hw i hi).2.1 (hw i hi).2.2
    _ = _ := by simp

end CoprimeTriangles
