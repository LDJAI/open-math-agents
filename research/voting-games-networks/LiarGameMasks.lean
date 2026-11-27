import LiarGameExtension
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.SetTheory.Cardinal.Finite

/-! Any adaptive strategy has the same number of compatible transcripts
for a candidate with a given lie budget. Its transcript-to-error-mask
map is a permutation of the Boolean response strings. -/
namespace LiarGameMasks
open LiarGameExtension

def mask {h : ℕ} {I : Type*} (A : Strategy h I) (x : I) (w : Word h) :
    Word h := fun i => xor (A x i (wordPrefix w i)) (w i)

def realize {h : ℕ} {I : Type*} (A : Strategy h I) (x : I)
    (m : Word h) (i : Fin h) : Bool :=
  xor (A x i (fun j => realize A x m ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩)) (m i)
termination_by i.val

theorem mask_realize {h : ℕ} {I : Type*} (A : Strategy h I) (x : I)
    (m : Word h) : mask A x (realize A x m) = m := by
  funext i
  unfold mask
  conv_lhs => rhs; rw [realize]
  change xor (A x i (wordPrefix (realize A x m) i))
    (xor (A x i (wordPrefix (realize A x m) i)) (m i)) = m i
  cases A x i (wordPrefix (realize A x m) i) <;> cases m i <;> rfl

def maskEquiv {h : ℕ} {I : Type*} (A : Strategy h I) (x : I) :
    Word h ≃ Word h where
  toFun := mask A x
  invFun := realize A x
  right_inv := mask_realize A x
  left_inv := by
    have surj : Function.Surjective (mask A x) :=
      fun w => ⟨realize A x w, mask_realize A x w⟩
    have inj : Function.Injective (mask A x) := (Finite.injective_iff_surjective).mpr surj
    intro w
    exact inj (mask_realize A x (mask A x w))

def popcount {h : ℕ} (w : Word h) : ℕ :=
  (Finset.univ.filter (fun i => w i = true)).card

theorem errors_eq_popcount {h : ℕ} {I : Type*} (A : Strategy h I) (x : I)
    (w : Word h) : errors A x w = popcount (mask A x w) := by
  have eqp : (fun i => A x i (wordPrefix w i) ≠ w i) =
      (fun i => mask A x w i = true) := by
    funext i
    apply propext
    unfold mask
    cases A x i (wordPrefix w i) <;> cases w i <;> decide
  unfold errors popcount
  simp only [eqp]

def maskVolume (h r : ℕ) : ℕ :=
  Fintype.card {m : Word h // popcount m ≤ r}

theorem compatible_card {h : ℕ} {I : Type*} (A : Strategy h I) (b : I → ℕ) (x : I) :
    Nat.card {w : Word h // Compatible A b x w} = maskVolume h (b x) := by
  classical
  unfold maskVolume
  rw [← Nat.card_eq_fintype_card]
  apply Nat.card_congr
  apply (maskEquiv A x).subtypeEquiv
  intro w
  change errors A x w ≤ b x ↔ popcount (mask A x w) ≤ b x
  rw [errors_eq_popcount]

end LiarGameMasks
