import HenriquesCore
import Mathlib.Tactic.NoncommRing

open scoped BigOperators

namespace HenriquesCore

/-- The composite finite-index bound, without division. If K(x)=Σwᵢ*xwᵢ
and T(y)=Σwᵢ*ρ(y)wᵢ, the normalized expectation F is ρ(T(K(x)))/4.
The displayed inequality therefore reads F(x) ≥ x/16. The last conjunct
locates its unnormalized value in the image of the fixed-point algebra. -/
theorem composite_index_bound {R : Type*} [CStarAlgebra R] [PartialOrder R]
    [StarOrderedRing R] [IsOrderedAddMonoid R]
    (r : R →⋆ₐ[ℂ] R) (hr : Function.Injective r)
    (w : Fin 2 → R) (hfull : ∑ i, w i * star (w i) = 1)
    (horth : ∀ i j, star (w i) * w j = if i = j then 1 else 0)
    (hsquare : ∀ x, r (r x) = ∑ i, w i * r x * star (w i))
    (hirred : ∀ z, (∀ x, z * r x = r x * z) → ∀ y, z * y = y * z)
    (x : R) (hx : 0 ≤ x) :
    let T := SectorFixedPoints.transfer r.toRingHom (w 0) (w 1)
    let k := star (w 0) * x * w 0 + star (w 1) * x * w 1
    let f := r (T k)
    x ≤ 4 • f ∧ ∃ d : R, T d = d + d ∧ f = r d := by
  let s := w 0
  let t := w 1
  let K := fun y : R => star s * y * s + star t * y * t
  let L := fun y : R => s * y * star s + t * y * star t
  let T := SectorFixedPoints.transfer r.toRingHom s t
  have H (y : R) := faithful_endomorphism_transfer r hr w hfull horth hsquare hirred y
  have hTk : T (T (K x)) = T (K x) + T (K x) := (H (K x)).1
  refine ⟨?_, T (K x), hTk, rfl⟩
  change x ≤ 4 • r (T (K x))
  have Heq : r (T (K x)) = L (T (K x)) := by
    simpa only [Fin.sum_univ_two, L, s, t] using ((H (T (K x))).2.1.mp hTk)
  rw [Heq]
  have hk : 0 ≤ K x := add_nonneg (star_left_conjugate_nonneg hx s) (star_left_conjugate_nonneg hx t)
  have hKle : K x ≤ T (K x) + T (K x) := (H (K x)).2.2 hk
  have hLle : L (K x) ≤ L (T (K x) + T (K x)) :=
    add_le_add (star_right_conjugate_le_conjugate hKle s) (star_right_conjugate_le_conjugate hKle t)
  have hLadd (a b : R) : L (a+b) = L a + L b := by dsimp [L]; noncomm_ring
  rw [hLadd (T (K x)) (T (K x))] at hLle
  have hrest : x = (s * star s + t * star t) * x * (s * star s + t * star t) := by
    have hf : s * star s + t * star t = 1 := by simpa only [Fin.sum_univ_two, s, t] using hfull
    rw [hf, one_mul, mul_one]
  let Z := s * star s - t * star t
  let X := s * star t + t * star s
  let Y := s * star t - t * star s
  have hsum : L (K x) + L (K x) - x =
      star Z * x * Z + star X * x * X + star Y * x * Y := by
    rw [sub_eq_add_neg, show -x = -((s * star s + t * star t) * x * (s * star s + t * star t)) from congrArg Neg.neg hrest]
    simp only [L,K,Z,X,Y,star_add,star_sub,star_mul,star_star]
    noncomm_ring
  have hL : x ≤ L (K x) + L (K x) := sub_nonneg.mp <| hsum ▸
    add_nonneg (add_nonneg (star_left_conjugate_nonneg hx Z) (star_left_conjugate_nonneg hx X))
      (star_left_conjugate_nonneg hx Y)
  apply hL.trans
  calc
    _ ≤ (L (T (K x)) + L (T (K x))) + (L (T (K x)) + L (T (K x))) := add_le_add hLle hLle
    _ = _ := by abel

end HenriquesCore

#print axioms HenriquesCore.composite_index_bound
