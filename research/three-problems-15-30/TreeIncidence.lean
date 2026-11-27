import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.CharP.Two
import Mathlib.Logic.Relation

namespace Bacher

open Matrix
open scoped Matrix

variable {n m : ℕ}

/-- Ground the vertex `none` and use the remaining vertex coordinates as labels. -/
def grounded (x : Fin n → ZMod 2) : Option (Fin n) → ZMod 2
  | none => 0
  | some i => x i

/-- The reduced incidence matrix counts the two endpoints modulo two. -/
def incidence (u v : Fin m → Option (Fin n)) : Matrix (Fin n) (Fin m) (ZMod 2) :=
  fun i j => (if u j = some i then 1 else 0) + (if v j = some i then 1 else 0)

lemma sum_endpoint (x : Fin n → ZMod 2) (p : Option (Fin n)) :
    (∑ i, x i * (if p = some i then (1 : ZMod 2) else 0)) = grounded x p := by
  cases p with
  | none => simp [grounded]
  | some j => simp [grounded, mul_ite]

theorem vecMul_incidence (u v : Fin m → Option (Fin n)) (x : Fin n → ZMod 2) (j : Fin m) :
    (x ᵥ* incidence u v) j = grounded x (u j) + grounded x (v j) := by
  simp only [Matrix.vecMul, dotProduct, incidence, mul_add, Finset.sum_add_distrib, sum_endpoint]

def Adjacent (u v : Fin m → Option (Fin n)) (p q : Option (Fin n)) : Prop :=
  ∃ j, u j = p ∧ v j = q

/-- Reachability along edges in either direction. -/
def Connected (u v : Fin m → Option (Fin n)) : Prop :=
  ∀ p, Relation.EqvGen (Adjacent u v) none p

lemma grounded_eq_of_reach {u v : Fin m → Option (Fin n)} {x : Fin n → ZMod 2}
    (h : ∀ j, grounded x (u j) = grounded x (v j)) {p q : Option (Fin n)}
    (hpq : Relation.EqvGen (Adjacent u v) p q) : grounded x p = grounded x q := by
  induction hpq with
  | rel _ _ hh => obtain ⟨j,rfl,rfl⟩ := hh; exact h j
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ hp hq => exact hp.trans hq

theorem det_ne_zero_iff_connected (u v : Fin n → Option (Fin n)) :
    (incidence u v).det ≠ 0 ↔ Connected u v := by
  classical
  constructor
  · intro hdet
    let R := Relation.EqvGen (Adjacent u v)
    let x : Fin n → ZMod 2 := fun i => if R none (some i) then 0 else 1
    have hroot : R none none := Relation.EqvGen.refl _
    have hval (p : Option (Fin n)) : grounded x p = if R none p then 0 else 1 := by
      cases p <;> simp [grounded, x, hroot]
    have hz : x ᵥ* incidence u v = 0 := by
      funext j
      have he : R (u j) (v j) := Relation.EqvGen.rel _ _ ⟨j, rfl, rfl⟩
      have same : R none (u j) ↔ R none (v j) :=
        ⟨fun h => Relation.EqvGen.trans _ _ _ h he,
         fun h => Relation.EqvGen.trans _ _ _ h (Relation.EqvGen.symm _ _ he)⟩
      rw [vecMul_incidence, hval, hval, if_congr same rfl rfl]
      exact CharTwo.add_self_eq_zero _
    have hzero : x = 0 := by
      by_contra hnon
      exact hdet (Matrix.exists_vecMul_eq_zero_iff.mp ⟨x,hnon,hz⟩)
    intro p
    cases p with
    | none => exact hroot
    | some i =>
      by_contra hbad
      have hxi := congrFun hzero i
      have hi : ¬R none (some i) := hbad
      simp [x, hi] at hxi
  · intro hc hdet
    obtain ⟨x,hx,hzero⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hdet
    have he (j : Fin n) : grounded x (u j) = grounded x (v j) := by
      have h := congrFun hzero j
      rw [vecMul_incidence] at h
      exact (eq_neg_of_add_eq_zero_left h).trans (ZMod.neg_eq_self_mod_two _)
    apply hx
    funext i
    exact (grounded_eq_of_reach he (hc (some i))).symm

end Bacher
