import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Max

/- Verified contribution for Erdős 774. Credit: @LDJAI. -/
namespace AnchorPartition
open Finset BigOperators

def Dissociated (D : Finset ℕ) : Prop :=
  ∀ U ⊆ D, ∀ V ⊆ D, (∑ x ∈ U, x) = (∑ x ∈ V, x) → U = V

def Represents (E : Finset ℕ) (t : ℕ) : Prop :=
  ∃ U ⊆ E, ∃ V ⊆ E, (∑ x ∈ U, x) = t + (∑ x ∈ V, x)

theorem no_disjoint_representations {D X Y : Finset ℕ} {t : ℕ}
    (hd : Dissociated D) (ht : 0 < t) (hx : X ⊆ D) (hy : Y ⊆ D)
    (hxy : Disjoint X Y) (hr : Represents X t) : ¬ Represents Y t := by
  obtain ⟨U, hU, V, hV, he⟩ := hr
  rintro ⟨P, hP, Q, hQ, hf⟩
  have huq : Disjoint U Q := hxy.mono hU hQ
  have hvp : Disjoint V P := hxy.mono hV hP
  have heq : U ∪ Q = V ∪ P := hd _ (Finset.union_subset (hU.trans hx) (hQ.trans hy))
    _ (Finset.union_subset (hV.trans hx) (hP.trans hy)) (by
      rw [Finset.sum_union huq, Finset.sum_union hvp]; omega)
  have huv : U = V := by
    ext x
    constructor
    · intro hu
      have hm : x ∈ V ∪ P := heq ▸ Finset.mem_union_left Q hu
      exact (Finset.mem_union.mp hm).resolve_right fun hp =>
        Finset.disjoint_left.mp hxy (hU hu) (hP hp)
    · intro hv
      have hm : x ∈ U ∪ Q := heq.symm ▸ Finset.mem_union_left P hv
      exact (Finset.mem_union.mp hm).resolve_right fun hq =>
        Finset.disjoint_left.mp hxy (hV hv) (hQ hq)
  subst V
  omega

private theorem singleton_safe {a t : ℕ} (ht : 0 < t) (ha : a ≠ t) :
    ¬ Represents {a} t := by
  rintro ⟨U,hU,V,hV,e⟩
  rcases Finset.subset_singleton_iff.mp hU with h | h <;>
    rcases Finset.subset_singleton_iff.mp hV with g | g <;> simp [h,g] at e <;> omega

/-- Each part avoids every signed representation of the specified outside point. -/
theorem three_parts_avoiding {D : Finset ℕ} {t : ℕ} (hd : Dissociated D)
    (ht : 0 < t) (hout : t ∉ D) :
    ∃ X Y Z : Finset ℕ, X ∪ Y ∪ Z = D ∧ Disjoint X Y ∧ Disjoint X Z ∧
      Disjoint Y Z ∧ ¬ Represents X t ∧ ¬ Represents Y t ∧ ¬ Represents Z t := by
  classical
  have empty_safe : ¬ Represents ∅ t := by simp [Represents]; omega
  by_cases has : Represents D t
  · let F := D.powerset.filter (fun E => Represents E t)
    have hf : F.Nonempty := ⟨D, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (by rfl),has⟩⟩
    obtain ⟨E, hE, hmin⟩ := F.exists_min_image Finset.card hf
    obtain ⟨hED, hr⟩ := Finset.mem_filter.mp hE
    have hsub := Finset.mem_powerset.mp hED
    have hn : E.Nonempty := Finset.nonempty_iff_ne_empty.mpr fun h => empty_safe (h ▸ hr)
    obtain ⟨a,ha⟩ := hn
    have houta : a ≠ t := fun h => hout (h ▸ hsub ha)
    have small : ¬ Represents (E.erase a) t := by
      intro he
      have hm : E.erase a ∈ F := Finset.mem_filter.mpr
        ⟨Finset.mem_powerset.mpr ((Finset.erase_subset _ _).trans hsub),he⟩
      have hle := hmin _ hm
      exact (Nat.not_le_of_gt (Finset.card_lt_card (Finset.erase_ssubset ha))) hle
    have d : Disjoint E (D \ E) := by
      exact Finset.disjoint_left.mpr fun _ hx hy => (Finset.mem_sdiff.mp hy).2 hx
    refine ⟨{a}, E.erase a, D \ E, ?_, ?_, d.mono_left (Finset.singleton_subset_iff.mpr ha),
      d.mono_left (Finset.erase_subset _ _), singleton_safe ht houta, small,
      no_disjoint_representations hd ht hsub Finset.sdiff_subset d hr⟩
    · ext b
      by_cases h : b = a
      · subst b; simp [ha,hsub ha]
      · by_cases hb : b ∈ E <;> simp [h,hb, Finset.mem_erase, fun h' : b ∈ E => hsub h']
    · simp
  · exact ⟨D,∅,∅,by simp,by simp,by simp,by simp,has,empty_safe,empty_safe⟩

#print axioms three_parts_avoiding
end AnchorPartition


namespace AnchorPartition
open Finset BigOperators

/-- Simultaneous avoidance of all outside targets, with a linear bound on the number of parts. -/
theorem many_parts_avoiding (D T : Finset ℕ) (hd : Dissociated D)
    (hp : ∀ t ∈ T, 0 < t) (hout : Disjoint D T) :
    ∃ parts : List (Finset ℕ), parts.length ≤ 2 * T.card + 1 ∧
      parts.Pairwise Disjoint ∧ (∀ a ∈ D, ∃ P ∈ parts, a ∈ P) ∧
      ∀ P ∈ parts, P ⊆ D ∧ ∀ t ∈ T, ¬ Represents P t := by
  classical
  induction hn : T.card using Nat.strong_induction_on generalizing D T with
  | h n ih =>
    by_cases no : ∀ t ∈ T, ¬ Represents D t
    · exact ⟨[D],by simp,by simp,fun a ha => ⟨D,by simp,ha⟩,
        by simpa using And.intro (Finset.Subset.refl D) no⟩
    push Not at no
    obtain ⟨t0,ht0,hr0⟩ := no
    let F := D.powerset.filter (fun S => ∃ t ∈ T, Represents S t)
    have hF : F.Nonempty := ⟨D,mem_filter.mpr ⟨mem_powerset.mpr (by rfl),t0,ht0,hr0⟩⟩
    obtain ⟨S,hS,minimal⟩ := F.exists_min_image Finset.card hF
    obtain ⟨sub, t, ht, rep⟩ := mem_filter.mp hS
    have subD := mem_powerset.mp sub
    have safe {Q : Finset ℕ} (hq : Q ⊂ S) (u : ℕ) (hu : u ∈ T) : ¬ Represents Q u := by
      intro hr
      have hm := minimal Q (mem_filter.mpr ⟨mem_powerset.mpr (hq.le.trans subD),u,hu,hr⟩)
      exact (Nat.not_le_of_gt (Finset.card_lt_card hq)) hm
    have sn : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr (by
      rintro rfl
      have := hp t ht
      simp [Represents] at rep
      omega)
    obtain ⟨a,ha⟩ := sn
    have ss : ¬ Represents {a} t := by
      have htpos := hp t ht
      have ha_ne : a ≠ t := fun e => Finset.disjoint_left.mp hout (subD ha) (e ▸ ht)
      rintro ⟨U,hU,V,hV,he⟩
      rcases Finset.subset_singleton_iff.mp hU with h|h <;>
        rcases Finset.subset_singleton_iff.mp hV with l|l <;> simp [h,l] at he <;> omega
    have single : ({a} : Finset ℕ) ⊂ S := lt_of_le_of_ne (singleton_subset_iff.mpr ha)
      (fun eq => ss (eq.symm ▸ rep))
    let R := D \ S
    have dSR : Disjoint S R := Finset.disjoint_left.mpr fun _ hs hr => (mem_sdiff.mp hr).2 hs
    have rsub : R ⊆ D := Finset.sdiff_subset
    have dr : Dissociated R := fun U hU V hV => hd U (hU.trans rsub) V (hV.trans rsub)
    have hlt : (T.erase t).card < n := hn ▸ Finset.card_lt_card (Finset.erase_ssubset ht)
    obtain ⟨ps,hlen,hpair,hcover,hparts⟩ := ih _ hlt R (T.erase t) dr
      (fun u hu => hp u (mem_erase.mp hu).2) (hout.mono rsub (erase_subset _ _)) rfl
    have avoid := no_disjoint_representations hd (hp t ht) subD rsub dSR rep
    refine ⟨{a} :: S.erase a :: ps,?_,?_,?_,?_⟩
    · have hc := Finset.card_erase_add_one ht
      simp only [List.length_cons]
      omega
    · simp only [List.pairwise_cons,List.mem_cons,forall_eq_or_imp]
      exact ⟨⟨by simp,fun P hP => dSR.mono single.le (hparts P hP).1⟩,
        fun P hP => dSR.mono (erase_subset _ _) (hparts P hP).1,hpair⟩
    · intro x hx
      by_cases eq : x = a
      · exact ⟨{a},by simp,by simp [eq]⟩
      by_cases mem : x ∈ S
      · exact ⟨S.erase a,by simp,mem_erase.mpr ⟨eq,mem⟩⟩
      obtain ⟨P,hP,hxP⟩ := hcover x (mem_sdiff.mpr ⟨hx,mem⟩)
      exact ⟨P,by simp [hP],hxP⟩
    · intro P hP
      rcases List.mem_cons.mp hP with rfl|hP
      · exact ⟨single.le.trans subD,safe single⟩
      rcases List.mem_cons.mp hP with rfl|hP
      · exact ⟨(erase_subset _ _).trans subD,safe (erase_ssubset ha)⟩
      obtain ⟨pR,small⟩ := hparts P hP
      refine ⟨pR.trans rsub, fun u hu => ?_⟩
      by_cases eq : u=t
      · subst u
        rintro ⟨U,hU,V,hV,he⟩
        exact avoid ⟨U,hU.trans pR,V,hV.trans pR,he⟩
      · exact small u (mem_erase.mpr ⟨eq,hu⟩)

#print axioms many_parts_avoiding
end AnchorPartition
