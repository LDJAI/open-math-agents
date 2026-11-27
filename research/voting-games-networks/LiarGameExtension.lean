import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic

/-! Unused leaves in an adaptive binary liar game can hold exactly one
zero-lie candidate each. At time i a question can depend on the whole
length-i transcript. There are no restrictions on which subset is queried. -/
namespace LiarGameExtension

abbrev Word (h : ℕ) := Fin h → Bool
abbrev Strategy (h : ℕ) (H : Type*) :=
  H → (i : Fin h) → Word i.val → Bool

def wordPrefix {h : ℕ} (w : Word h) (i : Fin h) : Word i.val :=
  fun j => w ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩

def errors {h : ℕ} {H : Type*} (A : Strategy h H) (x : H) (w : Word h) : ℕ :=
  (Finset.univ.filter (fun i => A x i (wordPrefix w i) ≠ w i)).card

def Compatible {h : ℕ} {H : Type*} (A : Strategy h H) (b : H → ℕ)
    (x : H) (w : Word h) : Prop := errors A x w ≤ b x

def Decodes {h : ℕ} {H : Type*} (A : Strategy h H) (b : H → ℕ) : Prop :=
  ∀ w x y, Compatible A b x w → Compatible A b y w → x = y

def FreeLeaf {h : ℕ} {H : Type*} (A : Strategy h H) (b : H → ℕ) :=
  {w : Word h // ∀ x, ¬ Compatible A b x w}

def extend {h : ℕ} {H : Type*} (A : Strategy h H) (b : H → ℕ) :
    Strategy h (H ⊕ FreeLeaf A b)
  | .inl x, i, p => A x i p
  | .inr f, i, _ => f.val i

def extendBudget {H F : Type*} (b : H → ℕ) : H ⊕ F → ℕ
  | .inl x => b x
  | .inr _ => 0

private theorem no_errors_iff {h : ℕ} {H : Type*} (A : Strategy h H)
    (x : H) (w : Word h) :
    errors A x w = 0 ↔ ∀ i, A x i (wordPrefix w i) = w i := by
  simp [errors, Finset.card_eq_zero, Finset.filter_eq_empty_iff]

private theorem free_compatible_iff {h : ℕ} {H : Type*} (A : Strategy h H)
    (b : H → ℕ) (f : FreeLeaf A b) (w : Word h) :
    Compatible (extend A b) (extendBudget b) (.inr f) w ↔ f.val = w := by
  change errors (extend A b) (.inr f) w ≤ 0 ↔ _
  rw [Nat.le_zero, no_errors_iff]
  exact funext_iff.symm

/-- Assign every unused answer string to a separate zero-lie candidate. -/
theorem fill_unused_leaves {h : ℕ} {H : Type*} {A : Strategy h H} {b : H → ℕ}
    (hA : Decodes A b) : Decodes (extend A b) (extendBudget b) := by
  intro w x y hx hy
  rcases x with x | f <;> rcases y with y | g
  · exact congrArg Sum.inl (hA w x y hx hy)
  · have eqw := (free_compatible_iff _ _ g w).mp hy
    exact False.elim (g.property x (eqw.symm ▸ hx))
  · have eqw := (free_compatible_iff _ _ f w).mp hx
    exact False.elim (f.property y (eqw.symm ▸ hy))
  · apply congrArg Sum.inr
    exact Subtype.ext (((free_compatible_iff _ _ f w).mp hx).trans
      ((free_compatible_iff _ _ g w).mp hy).symm)

/-- Recursing on time defines the unique transcript with no lies from x. -/
def truthful {h : ℕ} {H : Type*} (A : Strategy h H) (x : H) (i : Fin h) : Bool :=
  A x i (fun j => truthful A x ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩)
termination_by i.val

theorem truthful_zero {h : ℕ} {H : Type*} (A : Strategy h H) (x : H) :
    errors A x (truthful A x) = 0 := by
  apply (no_errors_iff _ _ _).2
  intro i
  conv_rhs => rw [truthful]
  rfl

/-- Conversely, in any successful extension, the truthful transcripts of the
zero-lie candidates inject into the leaves unused by the hard candidates. -/
theorem any_extension_embeds {h : ℕ} {H F : Type*}
    (A : Strategy h (H ⊕ F)) (b : H → ℕ) (hA : Decodes A (extendBudget b)) :
    Nonempty (F ↪ FreeLeaf (fun x => A (.inl x)) b) := by
  have truth (f : F) : Compatible A (extendBudget b) (.inr f) (truthful A (.inr f)) := by
    exact Nat.le_of_eq (truthful_zero A (.inr f))
  refine ⟨⟨fun f => ⟨truthful A (.inr f), ?_⟩, ?_⟩⟩
  · intro x hx
    have h := hA _ (.inl x) (.inr f) hx (truth f)
    contradiction
  · intro f g h
    have heq := congrArg Subtype.val h
    change truthful A (.inr f) = truthful A (.inr g) at heq
    have same : Compatible A (extendBudget b) (.inr f) (truthful A (.inr g)) :=
      heq ▸ truth f
    exact Sum.inr.inj (hA _ (.inr f) (.inr g) same (truth g))

end LiarGameExtension
