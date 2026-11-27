import OMAStatements.S_mo_124631

/-!
# Optimality of the synchronized scheduling algorithm

Simon Lentner, MathOverflow 124631. Proof: @LDJAI.
For each of the two recurrences we prove a lower bound against every legal
competitor and construct a witness for every finite budget the recurrence meets.
-/

namespace OMA.S_mo_124631

variable {J T : Type} [AddCommMonoid T] [LinearOrder T]

theorem duration_nonneg (w : J → T) (qs : List (Finset J)) : 0 ≤ duration w qs := by
  induction qs with
  | nil => exact le_rfl
  | cons Q qs ih => exact ih.trans (le_max_right _ _)

theorem elapsed_nonneg [IsOrderedAddMonoid T] (w : J → T) (plan : List (List (Finset J))) :
    0 ≤ elapsed w plan := by
  induction plan with
  | nil => exact le_rfl
  | cons qs rest ih => exact add_nonneg (duration_nonneg w qs) ih

variable [DecidableEq J]

theorem oneSession_lower (w : J → T) (S : Finset J) (qs : List (Finset J))
    (h : Packs S qs) : oneSession w qs.length S ≤ ((duration w qs : T) : WithTop T) := by
  induction qs generalizing S with
  | nil =>
    change S = ∅ at h
    subst S
    simp [oneSession, duration]
  | cons Q qs ih =>
    obtain ⟨hQ, hqs⟩ := h
    change S.powerset.inf _ ≤ _
    apply (Finset.inf_le (Finset.mem_powerset.mpr hQ)).trans
    change max _ _ ≤ ((max _ _ : T) : WithTop T)
    rw [WithTop.coe_max]
    exact max_le_max le_rfl (ih _ hqs)

theorem oneSession_witness (w : J → T) (p : ℕ) (S : Finset J) (b : T)
    (h : oneSession w p S ≤ (b : WithTop T)) :
    ∃ qs, Packs S qs ∧ qs.length = p ∧ duration w qs ≤ b := by
  induction p generalizing S b with
  | zero =>
    by_cases he : S = ∅
    · refine ⟨[], he, rfl, ?_⟩
      change (0 : T) ≤ b
      simpa [oneSession, he] using h
    · simp [oneSession, he] at h
  | succ p ih =>
    change S.powerset.inf _ ≤ _ at h
    obtain ⟨Q, hQ, hcost⟩ := (Finset.inf_le_iff (WithTop.coe_lt_top b)).mp h
    obtain ⟨hq, hrest⟩ := max_le_iff.mp hcost
    obtain ⟨qs, pack, size, span⟩ := ih _ _ hrest
    exact ⟨Q :: qs, ⟨Finset.mem_powerset.mp hQ, pack⟩, by simp [size],
      max_le (WithTop.coe_le_coe.mp hq) span⟩

variable [IsOrderedAddMonoid T]

theorem optimum_lower (w : J → T) (p : ℕ) (W : T) (S : Finset J)
    (plan : List (List (Finset J))) (h : Legal w p W S plan) :
    optimum w p W S ≤ ((elapsed w plan : T) : WithTop T) := by
  induction plan generalizing S with
  | nil =>
    change S = ∅ at h
    subst S
    rw [optimum, if_pos rfl]
    exact le_rfl
  | cons qs rest ih =>
    obtain ⟨R, hRS, pack, size, cap, later⟩ := h
    have htail := ih R later
    have hrow : oneSession w p (S \ R) ≤ ((duration w qs : T) : WithTop T) :=
      size ▸ oneSession_lower w _ qs pack
    by_cases heq : R = S
    · subst R
      exact htail.trans (WithTop.coe_le_coe.mpr (le_add_of_nonneg_left (duration_nonneg w qs)))
    by_cases hempty : S = ∅
    · rw [optimum, if_pos hempty]
      exact WithTop.coe_le_coe.mpr (elapsed_nonneg _ _)
    let r : {r // r ∈ S.ssubsets} :=
      ⟨R, Finset.mem_ssubsets.mpr (Finset.ssubset_iff_subset_ne.mpr ⟨hRS, heq⟩)⟩
    rw [optimum, if_neg hempty]
    apply (Finset.inf_le (Finset.mem_attach _ r)).trans
    change (if oneSession w p (S \ R) ≤ (W : WithTop T) then
      oneSession w p (S \ R) + optimum w p W R else ⊤) ≤ _
    rw [if_pos (hrow.trans (WithTop.coe_le_coe.mpr cap))]
    simpa only [elapsed, WithTop.coe_add] using add_le_add hrow htail

theorem optimum_witness (w : J → T) (p : ℕ) (W : T) (S : Finset J) (b : T)
    (h : optimum w p W S ≤ (b : WithTop T)) :
    ∃ plan, Legal w p W S plan ∧ elapsed w plan ≤ b := by
  rw [optimum] at h
  split at h
  next hempty => exact ⟨[], hempty, WithTop.coe_le_coe.mp h⟩
  next =>
    obtain ⟨R, _, he⟩ := (Finset.inf_le_iff (WithTop.coe_lt_top b)).mp h
    dsimp only at he
    split at he
    next hcap =>
      obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.mp
        (ne_top_of_le_ne_top WithTop.coe_ne_top hcap)
      have hfinite : optimum w p W R.val ≠ ⊤ := by
        intro ht
        simp [ht] at he
      obtain ⟨v, hv⟩ := WithTop.ne_top_iff_exists.mp hfinite
      have hab : a + v ≤ b := by
        apply WithTop.coe_le_coe.mp
        simpa only [WithTop.coe_add, ha, hv] using he
      obtain ⟨qs, pack, size, hq⟩ := oneSession_witness w p (S \ R.val) a ha.ge
      obtain ⟨rest, later, hr⟩ := optimum_witness w p W R.val v hv.ge
      have hsub := (Finset.mem_ssubsets.mp R.property).subset
      have hW : a ≤ W := WithTop.coe_le_coe.mp (ha.le.trans hcap)
      exact ⟨qs :: rest, ⟨R.val, hsub, pack, size, hq.trans hW, later⟩,
        (add_le_add hq hr).trans hab⟩
    next => simp at he
termination_by S.card
decreasing_by exact Finset.card_lt_card (Finset.mem_ssubsets.mp R.property)

end OMA.S_mo_124631

open OMA.S_mo_124631

theorem OMA.solution : type_of% @OMA.S_mo_124631.main := by
  intro J T _ _ _ _ S p _ w W _ _
  constructor
  · constructor
    · rintro ht ⟨plan, hp⟩
      have h := optimum_lower w p W S plan hp
      simp [ht] at h
    · intro impossible
      by_contra hfinite
      obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp hfinite
      obtain ⟨plan, hp, _⟩ := optimum_witness w p W S t ht.ge
      exact impossible ⟨plan, hp⟩
  · intro t ht
    obtain ⟨plan, hp, hcost⟩ := optimum_witness w p W S t ht.le
    have lower : ∀ other, Legal w p W S other → t ≤ elapsed w other := by
      intro other hother
      exact WithTop.coe_le_coe.mp (ht.ge.trans (optimum_lower _ _ _ _ _ hother))
    exact ⟨plan, hp, le_antisymm hcost (lower plan hp), lower⟩
