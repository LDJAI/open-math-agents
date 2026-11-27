import Mathlib.Logic.Equiv.Option

/-!
Removing a pair who rank one another first preserves the entire set of stable
matchings. Writing the distinguished agents as `none` leaves the theorem
independent of market size and the choice of labels.
-/
namespace ForcedPair

variable {A B : Type*}

/-- Smaller ranks are preferred. A blocking pair strictly prefers each other. -/
def Stable (m : A → B → ℕ) (w : B → A → ℕ) (μ : A ≃ B) : Prop :=
  ∀ a b, ¬ (m a b < m a (μ a) ∧ w b a < w b (μ.symm b))

variable (m : Option A → Option B → ℕ) (w : Option B → Option A → ℕ)
variable (hm : ∀ b, m none none < m none (some b))
variable (hw : ∀ a, w none none < w none (some a))

include hm hw in
theorem fixed (μ : Option A ≃ Option B) (h : Stable m w μ) : μ none = none := by
  cases hb : μ none with
  | none => rfl
  | some b =>
    cases ha : μ.symm none with
    | none =>
      have hh := (μ.option_symm_apply_none_iff).mp ha
      simp [hh] at hb
    | some a =>
      exact False.elim (h none none ⟨hb ▸ hm b, ha ▸ hw a⟩)

private theorem extend_restriction (μ : Option A ≃ Option B) (h : μ none = none) :
    μ.removeNone.optionCongr = μ := by
  apply Equiv.ext
  intro x
  cases x with
  | none => exact h.symm
  | some a =>
    change some (μ.removeNone a) = μ (some a)
    cases e : μ (some a) with
    | none => exact False.elim (Option.some_ne_none a (μ.injective (e.trans h.symm)))
    | some b => exact (μ.removeNone_some ⟨b, e⟩).trans e

include hm hw in
theorem extension_stable_iff (μ : A ≃ B) :
    Stable m w μ.optionCongr ↔
      Stable (fun a b ↦ m (some a) (some b)) (fun b a ↦ w (some b) (some a)) μ := by
  constructor
  · intro h a b
    exact h (some a) (some b)
  · intro h a b hh
    cases a with
    | none =>
      cases b with
      | none => exact (Nat.lt_irrefl _) hh.1
      | some b => exact (Nat.lt_asymm (hm b)) hh.1
    | some a =>
      cases b with
      | none => exact (Nat.lt_asymm (hw a)) hh.2
      | some b => exact h a b hh

/-- Restriction and extension give inverse maps between stable matchings. -/
def deleteMutualFirst :
    {μ : Option A ≃ Option B // Stable m w μ} ≃
    {ν : A ≃ B // Stable (fun a b ↦ m (some a) (some b))
                          (fun b a ↦ w (some b) (some a)) ν} where
  toFun μ := ⟨μ.val.removeNone, (extension_stable_iff m w hm hw _).mp (by
    rw [extend_restriction μ.val (fixed m w hm hw μ.val μ.property)]
    exact μ.property)⟩
  invFun ν := ⟨ν.val.optionCongr, (extension_stable_iff m w hm hw _).mpr ν.property⟩
  left_inv μ := Subtype.ext (extend_restriction μ.val (fixed m w hm hw μ.val μ.property))
  right_inv ν := Subtype.ext (Equiv.removeNone_optionCongr ν.val)

#print axioms deleteMutualFirst
end ForcedPair
