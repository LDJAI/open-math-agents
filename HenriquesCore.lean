import Transfer
import FixedPoints
import OrderReflection
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases

open scoped BigOperators

namespace HenriquesCore

/-- Consequences of irreducibility and the sector equation on a C*-algebra.
The transfer is twice the conditional expectation in the manuscript. -/
theorem transfer_consequences {R : Type*} [CStarAlgebra R] [PartialOrder R]
    [StarOrderedRing R] [IsOrderedAddMonoid R]
    (r : R →+* R) (hstar : ∀ y, r (star y) = star (r y))
    (hr : Function.Injective r) (horder : ∀ u v, r u ≤ r v ↔ u ≤ v)
    (w : Fin 2 → R) (hfull : ∑ i, w i * star (w i) = 1)
    (horth : ∀ i j, star (w i) * w j = if i = j then 1 else 0)
    (hsquare : ∀ x, r (r x) = ∑ i, w i * r x * star (w i))
    (hirred : ∀ z, (∀ x, z * r x = r x * z) → ∀ y, z * y = y * z)
    (x : R) :
    let T := SectorFixedPoints.transfer r (w 0) (w 1)
    T (T x) = T x + T x ∧
    (T x = x + x ↔ r x = ∑ i, w i * x * star (w i)) ∧
    (0 ≤ x → x ≤ T x + T x) := by
  have hi (i : Fin 2) : star (w i) * w i = 1 := by simp [horth]
  have Hinter (i : Fin 2) (y : R) : r (r y) * w i = w i * r y := by
    rw [hsquare, Fin.sum_univ_two, add_mul]
    fin_cases i <;> simp [mul_assoc, horth]
  have Hfull : w 0 * star (w 0) + w 1 * star (w 1) = 1 := by
    simpa only [Fin.sum_univ_two] using hfull
  have H (y : R) : SectorFixedPoints.transfer r (w 0) (w 1)
        (SectorFixedPoints.transfer r (w 0) (w 1) y) =
      SectorFixedPoints.transfer r (w 0) (w 1) y + SectorFixedPoints.transfer r (w 0) (w 1) y := by
    simpa only [Fin.sum_univ_two, Fintype.card_fin, two_nsmul, SectorFixedPoints.transfer] using
      SectorTransfer.transfer_square r hstar w y hfull hi Hinter hirred
  refine ⟨H x, ?_, ?_⟩
  · simpa only [Fin.sum_univ_two] using
      SectorFixedPoints.fixed_iff r (w 0) (w 1) x hstar hr (hi 0) (hi 1) Hfull H
  · exact SectorFixedPoints.transfer_bound r (w 0) (w 1) x hstar hr (hi 0) (hi 1) Hfull H horder

/-- The same core theorem, stated directly for a faithful complex star-endomorphism.
Its order-embedding property is deduced by continuous functional calculus. -/
theorem faithful_endomorphism_transfer {R : Type*} [CStarAlgebra R] [PartialOrder R]
    [StarOrderedRing R] [IsOrderedAddMonoid R]
    (r : R →⋆ₐ[ℂ] R) (hr : Function.Injective r)
    (w : Fin 2 → R) (hfull : ∑ i, w i * star (w i) = 1)
    (horth : ∀ i j, star (w i) * w j = if i = j then 1 else 0)
    (hsquare : ∀ x, r (r x) = ∑ i, w i * r x * star (w i))
    (hirred : ∀ z, (∀ x, z * r x = r x * z) → ∀ y, z * y = y * z)
    (x : R) :
    let T := SectorFixedPoints.transfer r.toRingHom (w 0) (w 1)
    T (T x) = T x + T x ∧
    (T x = x + x ↔ r x = ∑ i, w i * x * star (w i)) ∧
    (0 ≤ x → x ≤ T x + T x) :=
  transfer_consequences r.toRingHom (fun u => map_star r u) hr
    (faithfulStarAlgHom_le_iff r hr) w hfull horth hsquare hirred x

end HenriquesCore

#print axioms HenriquesCore.transfer_consequences

#print axioms HenriquesCore.faithful_endomorphism_transfer
