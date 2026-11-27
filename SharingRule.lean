import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# A truthful public selection from two sets of intervals
Source: https://mathoverflow.net/q/312603 (pi66, October 11, 2018).
Formalization by @LDJAI with OpenAI Codex.
-/

namespace OMA.S_mo_312603

open Set MeasureTheory

/-- Nonempty finite unions of nondegenerate closed subintervals of the unit interval. -/
inductive Piece : Set ℝ → Prop
  | interval {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) : Piece (Icc a b)
  | union {s t : Set ℝ} : Piece s → Piece t → Piece (s ∪ t)

abbrev Report := {s : Set ℝ // Piece s}

end OMA.S_mo_312603

namespace OMA.S_mo_312603

open Set MeasureTheory
open scoped ENNReal

abbrev Ballot := Fin 3 → Bool

/-- Select an approved starting point of an approved cyclic pair whenever one exists. -/
def nominee (a : Ballot) : Fin 3 :=
  if a 0 && a 1 then 0 else if a 1 && a 2 then 1 else if a 2 && a 0 then 2
  else if a 0 then 0 else if a 1 then 1 else if a 2 then 2 else 0

/-- Distinct nominations win. A repeated nomination brings its clockwise successor. -/
def elect (a b : Ballot) (i : Fin 3) : Bool :=
  decide (i = nominee a ∨ i = nominee b ∨ (nominee a = nominee b ∧ i = nominee a + 1))

def count (a : Ballot) : ℕ := ∑ i, (a i).toNat

def utility (a x b : Ballot) := count (fun i => a i && elect x b i)

theorem local_size : ∀ a b, count (elect a b) = 2 := by decide +kernel
theorem local_half : ∀ a b, count a ≤ 2 * utility a a b := by decide +kernel
theorem local_truth : ∀ a b x, utility a x b ≤ utility a a b := by decide +kernel
theorem local_symm : ∀ a b i, elect a b i = elect b a i := by decide +kernel

end OMA.S_mo_312603

namespace OMA.S_mo_312603

open Set MeasureTheory
open scoped ENNReal

/-- Working with (a,b] keeps the three translated pieces disjoint at endpoints. -/
inductive Elementary : Set ℝ → Prop
  | empty : Elementary ∅
  | segment (a b : ℝ) : Elementary (Ioc a b)
  | union {s t : Set ℝ} : Elementary s → Elementary t → Elementary (s ∪ t)

theorem Elementary.meas {s : Set ℝ} (hs : Elementary s) : MeasurableSet s := by
  induction hs with
  | empty => exact MeasurableSet.empty
  | segment => exact measurableSet_Ioc
  | union _ _ hs ht => exact hs.union ht

theorem Elementary.inter {s t : Set ℝ} (hs : Elementary s) (ht : Elementary t) :
    Elementary (s ∩ t) := by
  induction hs with
  | empty => simpa using Elementary.empty
  | segment a b =>
    induction ht with
    | empty => simpa using Elementary.empty
    | segment c d => rw [Ioc_inter_Ioc]; exact .segment _ _
    | union _ _ h₁ h₂ => rw [inter_union_distrib_left]; exact h₁.union h₂
  | union _ _ h₁ h₂ => rw [union_inter_distrib_right]; exact h₁.union h₂

theorem Elementary.diff {s t : Set ℝ} (hs : Elementary s) (ht : Elementary t) :
    Elementary (s \ t) := by
  induction ht generalizing s with
  | empty => simpa using hs
  | segment c d =>
    induction hs with
    | empty => simpa using Elementary.empty
    | segment a b =>
      have he : Ioc a b \ Ioc c d = Ioc a (min b c) ∪ Ioc (max a d) b := by
        ext x
        simp only [mem_sdiff, mem_Ioc, mem_union, le_min_iff, max_lt_iff]
        grind
      rw [he]
      exact (.segment _ _ : Elementary _).union (.segment _ _)
    | union _ _ h₁ h₂ => rw [union_sdiff_distrib]; exact h₁.union h₂
  | union _ _ h₁ h₂ => rw [← sdiff_sdiff]; exact h₂ (h₁ hs)

theorem Elementary.shift {s : Set ℝ} (hs : Elementary s) (c : ℝ) :
    Elementary ((fun t : ℝ => t + c) ⁻¹' s) := by
  induction hs with
  | empty => exact .empty
  | segment a b =>
    have he : (fun t : ℝ => t + c) ⁻¹' Ioc a b = Ioc (a-c) (b-c) := by
      ext x
      simp only [mem_preimage, mem_Ioc]
      constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith
    rw [he]; exact .segment _ _
  | union _ _ h₁ h₂ => exact h₁.union h₂

theorem Elementary.finite_union {ι : Type*} (I : Finset ι) (F : ι → Set ℝ)
    (h : ∀ i ∈ I, Elementary (F i)) : Elementary (⋃ i ∈ I, F i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simpa using Elementary.empty
  | insert i I hi ih =>
    rw [Finset.set_biUnion_insert]
    exact (h i (by simp)).union (ih fun j hj => h j (by simp [hj]))

theorem Piece.half_open {s : Set ℝ} (hs : Piece s) :
    ∃ t, Elementary t ∧ t ⊆ Ioc 0 1 ∧ t =ᵐ[volume] s := by
  induction hs with
  | interval ha hab hb =>
    exact ⟨_, .segment _ _, Ioc_subset_Ioc ha hb, Ioc_ae_eq_Icc⟩
  | union _ _ ih ik =>
    obtain ⟨a, ha, hsub, he⟩ := ih
    obtain ⟨b, hb, ksub, ke⟩ := ik
    exact ⟨_, ha.union hb, union_subset hsub ksub, he.union ke⟩

theorem Piece.pos {s : Set ℝ} (hs : Piece s) : 0 < volume s := by
  induction hs with
  | interval _ hab _ => simpa [Real.volume_Icc] using hab
  | union _ _ ih _ => exact ih.trans_le (measure_mono subset_union_left)

theorem Elementary.close_ae {s : Set ℝ} (hs : Elementary s) :
    closure s =ᵐ[volume] s := by
  induction hs with
  | empty => rw [closure_empty]; exact Filter.EventuallyEq.rfl
  | segment a b =>
    by_cases h : a < b
    · rw [closure_Ioc h.ne]; exact Ioc_ae_eq_Icc.symm
    · rw [Ioc_eq_empty (by linarith), closure_empty]; exact Filter.EventuallyEq.rfl
  | union _ _ ih ik => rw [closure_union]; exact ih.union ik

theorem Elementary.close_piece {s : Set ℝ} (hs : Elementary s) (hsub : s ⊆ Ioc 0 1) :
    s = ∅ ∨ Piece (closure s) := by
  induction hs with
  | empty => exact Or.inl rfl
  | segment a b =>
    by_cases h : a < b
    · right
      rw [closure_Ioc h.ne]
      obtain ⟨hb, ha⟩ := (Ioc_subset_Ioc_iff h).mp hsub
      exact .interval ha h hb
    · left; exact Ioc_eq_empty (by linarith)
  | union hs ht ih ik =>
    rcases ih (subset_union_left.trans hsub) with ha | ha
    · simpa [ha] using ik (subset_union_right.trans hsub)
    rcases ik (subset_union_right.trans hsub) with hb | hb
    · right; simpa [hb] using ha
    right; rw [closure_union]; exact ha.union hb

end OMA.S_mo_312603

namespace OMA.S_mo_312603

open Set MeasureTheory
open scoped ENNReal

noncomputable def width : ℝ := 1/3
noncomputable def offset (i : Fin 3) : ℝ := (i.val : ℝ) / 3
def base : Set ℝ := Ioc 0 width
def strip (i : Fin 3) : Set ℝ := Ioc (offset i) (offset i + width)

noncomputable def ballot (s : Set ℝ) (t : ℝ) : Ballot := by
  classical
  exact fun i => decide (t + offset i ∈ s)

theorem ballot_inter (s v : Set ℝ) (t : ℝ) :
    ballot (s ∩ v) t = fun i => ballot s t i && ballot v t i := by
  classical
  funext i; by_cases hs : t + offset i ∈ s <;> simp [ballot, hs]

theorem in_strip {t : ℝ} (i : Fin 3) : t + offset i ∈ strip i ↔ t ∈ base := by
  simp [strip, base, mem_Ioc, add_comm t (offset i)]

theorem strips_disjoint {i j : Fin 3} (h : i ≠ j) : Disjoint (strip i) (strip j) := by
  rw [Set.disjoint_left]
  intro x hx hy
  have hne : i.val ≠ j.val := fun e => h (Fin.ext e)
  change (i.val : ℝ)/3 < x ∧ x ≤ (i.val : ℝ)/3 + 1/3 at hx
  change (j.val : ℝ)/3 < x ∧ x ≤ (j.val : ℝ)/3 + 1/3 at hy
  rcases lt_or_gt_of_ne hne with hij | hji
  · have hstep : (i.val : ℝ) + 1 ≤ (j.val : ℝ) := by exact_mod_cast hij
    linarith
  · have hstep : (j.val : ℝ) + 1 ≤ (i.val : ℝ) := by exact_mod_cast hji
    linarith

theorem strips_cover : (⋃ i : Fin 3, strip i) = Ioc 0 1 := by
  ext x
  simp only [mem_iUnion, Fin.exists_fin_succ, Fin.exists_fin_zero, or_false]
  norm_num [strip, offset, width]
  constructor
  · rintro (h | h | h) <;> constructor <;> linarith
  · rintro ⟨hx, hx'⟩
    by_cases h : x ≤ 1/3
    · left; exact ⟨hx, h⟩
    by_cases hh : x ≤ 2/3
    · right; left; constructor <;> linarith
    · right; right; constructor <;> linarith

theorem strip_subset (i : Fin 3) : strip i ⊆ Ioc 0 1 :=
  strips_cover ▸ subset_iUnion strip i

def pattern (s : Set ℝ) (a : Ballot) : Set ℝ := {t | t ∈ base ∧ ballot s t = a}

theorem pattern_elem {s : Set ℝ} (hs : Elementary s) (a : Ballot) :
    Elementary (pattern s a) := by
  classical
  have hf (J : Finset (Fin 3)) :
      Elementary {t | t ∈ base ∧ ∀ i ∈ J, ballot s t i = a i} := by
    induction J using Finset.induction_on with
    | empty =>
      convert (Elementary.segment 0 width) using 1
      ext t; simp [base]
    | insert i J hi ih =>
      cases h : a i with
      | false =>
        convert ih.diff (hs.shift (offset i)) using 1
        ext t; simp [ballot, h]; tauto
      | true =>
        convert ih.inter (hs.shift (offset i)) using 1
        ext t; simp [ballot, h]; tauto
  simpa [pattern, funext_iff] using hf Finset.univ

def winning (s v : Set ℝ) (i : Fin 3) : Set ℝ :=
  {t | t ∈ base ∧ elect (ballot s t) (ballot v t) i = true}

theorem winning_elem {s v : Set ℝ} (hs : Elementary s) (hv : Elementary v) (i : Fin 3) :
    Elementary (winning s v i) := by
  classical
  let J := Finset.univ.filter fun p : Ballot × Ballot => elect p.1 p.2 i = true
  have eqn : winning s v i = ⋃ p ∈ J, pattern s p.1 ∩ pattern v p.2 := by
    ext t
    simp only [J, Finset.mem_filter, Finset.mem_univ, true_and, mem_iUnion, exists_prop,
      winning, pattern, mem_ofPred_eq, mem_inter_iff]
    constructor
    · rintro ⟨ht, hw⟩
      exact ⟨(ballot s t, ballot v t), hw, ⟨ht, rfl⟩, ⟨ht, rfl⟩⟩
    · rintro ⟨p, hw, ⟨ht,e₁⟩, _,e₂⟩
      exact ⟨ht, e₁ ▸ e₂ ▸ hw⟩
  rw [eqn]
  exact Elementary.finite_union J _ fun p _ => (pattern_elem hs p.1).inter (pattern_elem hv p.2)

/-- Translate the winning subsets of the short base interval back to their three strips. -/
def raw (s v : Set ℝ) : Set ℝ :=
  ⋃ i : Fin 3, (fun y : ℝ => y + -offset i) ⁻¹' winning s v i

theorem raw_elem {s v : Set ℝ} (hs : Elementary s) (hv : Elementary v) :
    Elementary (raw s v) := by
  simpa [raw] using Elementary.finite_union (Finset.univ : Finset (Fin 3))
    (fun i => (fun y : ℝ => y + -offset i) ⁻¹' winning s v i)
    (fun i _ => (winning_elem hs hv i).shift (-offset i))

theorem strip_of_shift {x : ℝ} {i : Fin 3} (h : x + -offset i ∈ base) : x ∈ strip i := by
  simpa using (in_strip i).2 h

theorem raw_sub (s v : Set ℝ) : raw s v ⊆ Ioc 0 1 := by
  intro x hx
  obtain ⟨i, hi⟩ := mem_iUnion.mp hx
  exact strip_subset i (strip_of_shift hi.1)

theorem raw_ballot (s v : Set ℝ) {t : ℝ} (ht : t ∈ base) :
    ballot (raw s v) t = elect (ballot s t) (ballot v t) := by
  classical
  funext i
  apply Bool.eq_iff_iff.mpr
  simp only [ballot, decide_eq_true_eq] at *
  constructor
  · intro hm
    obtain ⟨j, hj⟩ := mem_iUnion.mp hm
    have he : i = j := by
      by_contra hn
      exact Set.disjoint_left.mp (strips_disjoint hn) ((in_strip i).2 ht) (strip_of_shift hj.1)
    subst j
    simpa [ballot] using hj.2
  · intro he
    apply mem_iUnion.mpr
    exact ⟨i, by simpa [winning, ballot, ht] using he⟩

theorem raw_comm (s v : Set ℝ) : raw s v = raw v s := by
  unfold raw
  congr 1
  funext i
  have eqn : winning s v i = winning v s i := by
    ext t
    simp only [winning, mem_ofPred_eq, local_symm (ballot s t) (ballot v t) i]
  rw [eqn]

end OMA.S_mo_312603

namespace OMA.S_mo_312603

open Set MeasureTheory
open scoped ENNReal

/-- Length equals the integral of the number of approved points in each triple. -/
theorem volume_by_ballot {s : Set ℝ} (hs : MeasurableSet s) (hsub : s ⊆ Ioc 0 1) :
    volume s = ∫⁻ t in base, (count (ballot s t) : ℝ≥0∞) := by
  classical
  let P (i : Fin 3) := (fun t : ℝ => t + offset i) ⁻¹' s
  have hm (i : Fin 3) : MeasurableSet (P i) :=
    (measurable_id.add_const (offset i)) hs
  have spread (i : Fin 3) : P i ∩ base = (fun t : ℝ => t + offset i) ⁻¹' (s ∩ strip i) := by
    ext t
    simp only [P, mem_inter_iff, mem_preimage, in_strip]
  have integral (i : Fin 3) :
      (∫⁻ t in base, (P i).indicator (1 : ℝ → ℝ≥0∞) t) = volume (s ∩ strip i) := by
    rw [lintegral_indicator_one (hm i), Measure.restrict_apply (hm i), spread,
      measure_preimage_add_right]
  have expansion (t : ℝ) : (count (ballot s t) : ℝ≥0∞) =
      ∑ i : Fin 3, (P i).indicator (1 : ℝ → ℝ≥0∞) t := by
    simp only [count, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases ht : t + offset i ∈ s <;> simp [P, ballot, Set.indicator, ht]
  have union_eq : s = ⋃ i : Fin 3, s ∩ strip i := by
    rw [← inter_iUnion, strips_cover, inter_eq_left.mpr hsub]
  calc
    volume s = volume (⋃ i : Fin 3, s ∩ strip i) := congrArg volume union_eq
    _ = ∑ i : Fin 3, volume (s ∩ strip i) := by
      rw [measure_iUnion, tsum_fintype]
      · intro i j hij
        exact (strips_disjoint hij).mono inter_subset_right inter_subset_right
      · intro i; exact hs.inter measurableSet_Ioc
    _ = ∑ i : Fin 3, ∫⁻ t in base, (P i).indicator (1 : ℝ → ℝ≥0∞) t :=
      Finset.sum_congr rfl (fun i _ => (integral i).symm)
    _ = ∫⁻ t in base, (count (ballot s t) : ℝ≥0∞) := by
      simp_rw [expansion]
      exact (lintegral_finsetSum Finset.univ fun i _ => measurable_const.indicator (hm i)).symm

theorem raw_size {s v : Set ℝ} (hs : Elementary s) (hv : Elementary v) :
    volume (raw s v) = ENNReal.ofReal (2/3) := by
  rw [volume_by_ballot (raw_elem hs hv).meas (raw_sub s v)]
  calc
    _ = ∫⁻ _ : ℝ in base, (2 : ℝ≥0∞) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem (μ := volume) (show MeasurableSet base from measurableSet_Ioc)] with t ht
      simp only [raw_ballot s v ht, local_size, Nat.cast_ofNat]
    _ = _ := by
      rw [setLIntegral_const, base, Real.volume_Ioc, sub_zero, width]
      rw [← ENNReal.ofReal_ofNat (n := 2), ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
      congr 1; norm_num

theorem raw_half {s v : Set ℝ} (hs : Elementary s) (hv : Elementary v) (hsub : s ⊆ Ioc 0 1) :
    volume s ≤ 2 * volume (s ∩ raw s v) := by
  rw [volume_by_ballot hs.meas hsub,
    volume_by_ballot (hs.meas.inter (raw_elem hs hv).meas) (inter_subset_left.trans hsub),
    ← lintegral_const_mul' _ _ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]
  apply setLIntegral_mono' measurableSet_Ioc
  intro t ht
  rw [ballot_inter, raw_ballot s v ht]
  exact_mod_cast local_half (ballot s t) (ballot v t)

theorem raw_truth {s v x : Set ℝ} (hs : Elementary s) (hv : Elementary v) (hx : Elementary x)
    (hsub : s ⊆ Ioc 0 1) :
    volume (s ∩ raw x v) ≤ volume (s ∩ raw s v) := by
  rw [volume_by_ballot (hs.meas.inter (raw_elem hx hv).meas) (inter_subset_left.trans hsub),
    volume_by_ballot (hs.meas.inter (raw_elem hs hv).meas) (inter_subset_left.trans hsub)]
  apply setLIntegral_mono' measurableSet_Ioc
  intro t ht
  simp only [ballot_inter, raw_ballot _ _ ht]
  exact_mod_cast local_truth (ballot s t) (ballot v t) (ballot x t)

end OMA.S_mo_312603

namespace OMA.S_mo_312603

open Set MeasureTheory
open scoped ENNReal

noncomputable def input (A : Report) : Set ℝ := A.property.half_open.choose

theorem input_spec (A : Report) :
    Elementary (input A) ∧ input A ⊆ Ioc 0 1 ∧ input A =ᵐ[volume] A.1 :=
  A.property.half_open.choose_spec

noncomputable def schedule (A B : Report) : Report := by
  let s := raw (input A) (input B)
  have hs : Elementary s := raw_elem (input_spec A).1 (input_spec B).1
  have hsize : volume s = ENNReal.ofReal (2/3) := raw_size (input_spec A).1 (input_spec B).1
  have hne : s ≠ ∅ := by
    intro he
    rw [he, measure_empty] at hsize
    norm_num at hsize
  exact ⟨closure s, (hs.close_piece (raw_sub _ _)).resolve_left hne⟩

theorem schedule_ae (A B : Report) :
    (schedule A B).1 =ᵐ[volume] raw (input A) (input B) :=
  (raw_elem (input_spec A).1 (input_spec B).1).close_ae

theorem schedule_symm (A B : Report) : schedule A B = schedule B A := by
  apply Subtype.ext
  exact congrArg closure (raw_comm (input A) (input B))

theorem schedule_size (A B : Report) : volume (schedule A B).1 = ENNReal.ofReal (2/3) :=
  (measure_congr (schedule_ae A B)).trans (raw_size (input_spec A).1 (input_spec B).1)

theorem schedule_overlap (A X B : Report) :
    volume (A.1 ∩ (schedule X B).1) = volume (input A ∩ raw (input X) (input B)) :=
  measure_congr ((input_spec A).2.2.symm.inter (schedule_ae X B))

theorem schedule_half (A B : Report) : volume A.1 ≤ 2 * volume (A.1 ∩ (schedule A B).1) := by
  rw [schedule_overlap, ← measure_congr (input_spec A).2.2]
  exact raw_half (input_spec A).1 (input_spec B).1 (input_spec A).2.1

theorem schedule_truth (A B X : Report) :
    volume (A.1 ∩ (schedule X B).1) ≤ volume (A.1 ∩ (schedule A B).1) := by
  rw [schedule_overlap, schedule_overlap]
  exact raw_truth (input_spec A).1 (input_spec B).1 (input_spec X).1 (input_spec A).2.1

theorem schedule_positive (A B : Report) : 0 < volume (A.1 ∩ (schedule A B).1) := by
  by_contra! h
  have hz : volume (A.1 ∩ (schedule A B).1) = 0 := le_antisymm h bot_le
  have hp := schedule_half A B
  rw [hz, mul_zero] at hp
  exact (not_lt_of_ge hp) A.property.pos

end OMA.S_mo_312603

open OMA.S_mo_312603
open Set MeasureTheory

theorem OMA.solution :
    ∃ F : Report → Report → Report, ∀ A B : Report,
      (F A B).1 ≠ Icc 0 1 ∧
      0 < volume (A.1 ∩ (F A B).1) ∧ 0 < volume (B.1 ∩ (F A B).1) ∧
      ∀ X : Report, volume (A.1 ∩ (F X B).1) ≤ volume (A.1 ∩ (F A B).1) ∧
        volume (B.1 ∩ (F A X).1) ≤ volume (B.1 ∩ (F A B).1) := by
  refine ⟨schedule, fun A B => ⟨?_, schedule_positive A B, ?_, fun X => ⟨schedule_truth A B X, ?_⟩⟩⟩
  · intro he
    have h := schedule_size A B
    rw [he, Real.volume_Icc, sub_zero] at h
    have hr := congrArg ENNReal.toReal h
    norm_num at hr
  · rw [schedule_symm A B]
    exact schedule_positive B A
  · rw [schedule_symm A X, schedule_symm A B]
    exact schedule_truth B A X

#print axioms OMA.solution
#print axioms OMA.S_mo_312603.schedule_symm
#print axioms OMA.S_mo_312603.schedule_size
#print axioms OMA.S_mo_312603.schedule_half
#print axioms OMA.S_mo_312603.schedule_truth
