import LiarGameMasks
import Mathlib.Data.Fintype.Sum

/-! Exact criterion for adding zero-lie candidates to any finite heterogeneous
state in an unrestricted adaptive liar game. -/
namespace LiarGameOccupancy
open LiarGameExtension LiarGameMasks

private abbrev Live {h : ℕ} {H : Type*} (A : Strategy h H) (b : H → ℕ) :=
  (x : H) × {w : Word h // Compatible A b x w}

private def leafMap {h : ℕ} {H : Type*} {A : Strategy h H} {b : H → ℕ} :
    FreeLeaf A b ⊕ Live A b → Word h
  | .inl f => f.val
  | .inr ⟨_,w⟩ => w.val

private theorem leaf_bijective {h : ℕ} {H : Type*} {A : Strategy h H}
    {b : H → ℕ} (hA : Decodes A b) :
    Function.Bijective (leafMap (A := A) (b := b)) := by
  classical
  constructor
  · intro u v he
    rcases u with f | ⟨x,s⟩ <;> rcases v with g | ⟨y,t⟩
    · exact congrArg Sum.inl (Subtype.ext he)
    · change f.val = t.val at he
      exact False.elim (f.property y (he.symm ▸ t.property))
    · change s.val = g.val at he
      exact False.elim (g.property x (he ▸ s.property))
    · change s.val = t.val at he
      have hxy := hA t.val x y (he ▸ s.property) t.property
      subst y
      have hst := Subtype.ext he
      subst t
      rfl
  · intro w
    by_cases hu : ∃ x, Compatible A b x w
    · obtain ⟨x,hx⟩ := hu
      exact ⟨.inr ⟨x, w,hx⟩,rfl⟩
    · exact ⟨.inl ⟨w,fun _ hc => hu ⟨_,hc⟩⟩,rfl⟩

theorem free_plus_used {h : ℕ} {H : Type*} [Fintype H]
    {A : Strategy h H} {b : H → ℕ} (hA : Decodes A b) :
    Nat.card (FreeLeaf A b) + (∑ x, maskVolume h (b x)) = 2^h := by
  classical
  let : Fintype (FreeLeaf A b) := by unfold FreeLeaf; infer_instance
  have e := Equiv.ofBijective _ (leaf_bijective hA)
  have h := Fintype.card_congr e
  simp only [Fintype.card_sum, Live, Fintype.card_sigma, Word, Fintype.card_fun,
    Fintype.card_bool, Fintype.card_fin] at h
  simp_rw [← Nat.card_eq_fintype_card, compatible_card] at h
  exact h

/-- Positive-lie candidates can be solved with m extra pennies if and only
if they can already be solved and their occupied volume leaves room for m. -/
theorem with_pennies_iff {h : ℕ} {H : Type*} [Fintype H] (b : H → ℕ) (m : ℕ) :
    (∃ A : Strategy h (H ⊕ Fin m), Decodes A (extendBudget b)) ↔
    (∃ A : Strategy h H, Decodes A b) ∧ (∑ x, maskVolume h (b x)) + m ≤ 2^h := by
  classical
  constructor
  · rintro ⟨A,hA⟩
    let B : Strategy h H := fun x => A (.inl x)
    have hB : Decodes B b := fun w x y hx hy =>
      Sum.inl.inj (hA w (.inl x) (.inl y) hx hy)
    refine ⟨⟨B,hB⟩,?_⟩
    obtain ⟨i⟩ := any_extension_embeds A b hA
    let : Fintype (FreeLeaf B b) := by unfold FreeLeaf; infer_instance
    have hc := free_plus_used hB
    have bound : m ≤ Nat.card (FreeLeaf B b) := by
      rw [Nat.card_eq_fintype_card]
      simpa using (Fintype.card_le_of_embedding (show Fin m ↪ FreeLeaf B b from i))
    omega
  · rintro ⟨⟨B,hB⟩, bound⟩
    let : Fintype (FreeLeaf B b) := by unfold FreeLeaf; infer_instance
    have hc := free_plus_used hB
    have hm : Fintype.card (Fin m) ≤ Fintype.card (FreeLeaf B b) := by
      rw [Fintype.card_fin, ← Nat.card_eq_fintype_card]
      omega
    obtain ⟨i⟩ := Function.Embedding.nonempty_of_card_le hm
    let e : (H ⊕ Fin m) ↪ (H ⊕ FreeLeaf B b) := Function.Embedding.sumMap (.refl H) i
    refine ⟨fun x => extend B b (e x), ?_⟩
    have hb (x : H ⊕ Fin m) : extendBudget b x = extendBudget b (e x) := by
      cases x <;> rfl
    intro w x y hx hy
    apply e.injective
    apply fill_unused_leaves hB w (e x) (e y)
    · change errors (extend B b) (e x) w ≤ extendBudget b x at hx
      change errors (extend B b) (e x) w ≤ extendBudget b (e x)
      rwa [← hb x]
    · change errors (extend B b) (e y) w ≤ extendBudget b y at hy
      change errors (extend B b) (e y) w ≤ extendBudget b (e y)
      rwa [← hb y]

end LiarGameOccupancy
