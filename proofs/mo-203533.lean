import OMAStatements.S_mo_203533
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Finset Configuration OMA.S_mo_203533

namespace ContainedPlaneLines

variable {P L : Type*} [Fintype P] [Fintype L] [Membership P L] [ProjectivePlane P L]

noncomputable def pts (l : L) : Finset P := by classical exact univ.filter fun p => p∈l

theorem pts_size (l : L) : (pts l : Finset P).card = ProjectivePlane.order P L+1 := by
  classical
  simpa [pts,Configuration.pointCount,Nat.card_eq_fintype_card,Fintype.card_subtype] using
    (ProjectivePlane.pointCount_eq P l)

theorem belongs (S : Finset P) (l : L) : l∈contained P L S ↔ ∀ p : P,p∈l → p∈S := by
  classical
  simp [contained]

theorem pencil_lower (m : ℕ) (hm : 1≤m) (hcap : m≤Fintype.card P) :
    let q := ProjectivePlane.order P L
    ∃ S : Finset P, S.card=m ∧ (m-1)/q ≤ (contained P L S).card := by
  classical
  let q := ProjectivePlane.order P L
  have hq : 1<q := ProjectivePlane.one_lt_order P L
  have hcard : Fintype.card P=q^2+q+1 := ProjectivePlane.card_points P L
  obtain ⟨p,_⟩ : ∃ p : P, True := by
    have : 0<Fintype.card P := by omega
    exact ⟨(Fintype.card_pos_iff.mp this).some,trivial⟩
  let pencil := (univ : Finset L).filter fun l => p∈l
  have hc : pencil.card=q+1 := by
    simpa [pencil,q,Configuration.lineCount,Nat.card_eq_fintype_card,Fintype.card_subtype] using
      (ProjectivePlane.lineCount_eq L p)
  let s := (m-1)/q
  have hs : s ≤ pencil.card := by
    rw [hc]; apply Nat.le_of_lt_succ
    apply (Nat.div_lt_iff_lt_mul (by omega : 0<q)).mpr
    have := Nat.sub_add_cancel hm
    nlinarith [hcap]
  obtain ⟨T,hT,ht⟩ := exists_subset_card_eq hs
  let U := insert p (T.biUnion fun l => (pts l : Finset P).erase p)
  have hsize (l) (hl : l∈T) : ((pts l : Finset P).erase p).card=q := by
    have hpl : p∈pts l := by simpa [pts] using (mem_filter.mp (hT hl)).2
    rw [card_erase_of_mem hpl,pts_size]; rfl
  have hu : U.card≤m := by
    have h1 := card_insert_le p (T.biUnion fun l => (pts l : Finset P).erase p)
    have h2 := card_biUnion_le (s:=T) (t:=fun l => (pts l : Finset P).erase p)
    rw [sum_congr rfl hsize,sum_const,nsmul_eq_mul,ht] at h2
    have h3 := Nat.div_mul_le_self (m-1) q
    change s*q≤m-1 at h3
    change (T.biUnion fun l => (pts l : Finset P).erase p).card ≤ s*q at h2
    dsimp only [U]; omega
  obtain ⟨S,hUS,_,hS⟩ := exists_subsuperset_card_eq (subset_univ U) hu (by simpa using hcap)
  refine ⟨S,hS,?_⟩
  change s ≤ _
  rw [←ht]
  apply card_le_card
  intro l hl
  apply (belongs S l).mpr
  intro x hx
  apply hUS
  by_cases e : x=p
  · exact mem_insert.mpr (Or.inl e)
  · exact mem_insert.mpr (Or.inr (mem_biUnion.mpr ⟨l,hl,mem_erase.mpr ⟨e,by simpa [pts] using hx⟩⟩))

theorem second_moment (S : Finset P) :
    let q := ProjectivePlane.order P L
    let t := (contained P L S).card
    t*(q+1)^2 ≤ S.card*(q+t) := by
  classical
  let q := ProjectivePlane.order P L
  let T := contained P L S
  let R := fun p : P => T.filter (fun l => p ∈ l)
  let d := fun p => (R p).card
  have hl (l) (hh : l∈T) : S.filter (fun p => p∈l) = pts l := by
    ext p
    have hc := (belongs S l).mp hh
    simp [pts]
    exact fun h => hc p h
  have hfirst : (∑ p∈S,d p)=T.card*(q+1) := by
    calc
      _ = ∑ p∈S, ∑ l∈T, if p∈l then 1 else 0 := by simp [d,R]
      _ = ∑ l∈T, (S.filter fun p => p∈l).card := by rw [sum_comm]; simp
      _ = ∑ _l∈T,(q+1) := sum_congr rfl fun l h => by rw [hl l h,pts_size]
      _ = _ := by simp
  have hdis : (↑S : Set P).PairwiseDisjoint (fun p => (R p).offDiag) := by
    intro p _ r _ hpr
    rw [Function.onFun,Finset.disjoint_left]
    intro x h1 h2
    obtain ⟨ha,hb,hne⟩ := mem_offDiag.mp h1
    obtain ⟨hc,hd,_⟩ := mem_offDiag.mp h2
    exact (Nondegenerate.eq_or_eq (mem_filter.mp ha).2 (mem_filter.mp hc).2
      (mem_filter.mp hb).2 (mem_filter.mp hd).2).elim hpr hne
  have hsub : S.biUnion (fun p => (R p).offDiag) ⊆ T.offDiag := by
    intro x hx
    obtain ⟨p,_,hp⟩ := mem_biUnion.mp hx
    exact offDiag_mono (filter_subset _ _) hp
  have hpair : (∑ p∈S,d p*(d p-1)) ≤ T.card*(T.card-1) := by
    calc
      _ = ∑ p∈S,((R p).offDiag).card := by simp [d,offDiag_card,Nat.mul_sub_left_distrib]
      _ = (S.biUnion (fun p => (R p).offDiag)).card := (card_biUnion hdis).symm
      _ ≤ T.offDiag.card := card_le_card hsub
      _ = _ := by simp [offDiag_card,Nat.mul_sub_left_distrib]
  have hsq (z : ℕ) : z*(z-1)+z=z^2 := by cases z <;> simp <;> ring
  have hsecond : (∑ p∈S,d p^2) ≤ T.card*(q+T.card) := by
    calc
      _ = (∑ p∈S,d p*(d p-1))+(∑ p∈S,d p) := by rw [←sum_add_distrib]; simp_rw [hsq]
      _ ≤ T.card*(T.card-1)+T.card*(q+1) := by rw [hfirst]; omega
      _ = _ := by have hh := hsq T.card; nlinarith only [hh]
  have hcs := sum_mul_sq_le_sq_mul_sq S (fun _ => (1:ℕ)) d
  simp only [one_mul,one_pow,sum_const,nsmul_eq_mul,mul_one,hfirst] at hcs
  change T.card*(q+1)^2 ≤ S.card*(q+T.card)
  by_cases hz : T.card=0
  · simp [hz]
  apply Nat.le_of_mul_le_mul_left _ (show 0<T.card by omega)
  have h := hcs.trans (Nat.mul_le_mul_left S.card hsecond)
  nlinarith only [h]

theorem relative {q m f T : ℕ} (hq : 1<q) (hm : 1≤m) (hl : (m-1)/q≤f)
    (hu : f*(q+1)^2 ≤ m*(q+f)) (hT : 2≤T) (ha : T*q≤m) (hb : T*m≤q^2) :
    (T-1)*m ≤ T*(q*f) ∧ (T-1)*(q*f) ≤ T*m := by
  have hqf : m ≤ q*f+q := by
    have h := Nat.mod_lt (m-1) (show 0<q by omega)
    have hs := Nat.mod_add_div (m-1) q
    have hd := Nat.mul_le_mul_left q hl
    omega
  have hs : T-1+1=T := by omega
  constructor
  · have k := Nat.mul_le_mul_left T hqf
    nlinarith only [k,ha,congrArg (fun x : ℕ => x*m) hs]
  · apply Nat.le_of_mul_le_mul_left _ (show 0<q by omega)
    have h1 := Nat.mul_le_mul_left T hu
    have h2 := Nat.mul_le_mul_right f hb
    nlinarith only [h1,h2,congrArg (fun x : ℕ => x*(q^2*f)) hs,Nat.zero_le (T*f*q),Nat.zero_le (T*f)]

end ContainedPlaneLines

theorem OMA.solution : type_of% @OMA.S_mo_203533.main := by
  classical
  intro P L _ _ _ _ q m hm hm'
  have hcap : m ≤ Fintype.card P := by rwa [ProjectivePlane.card_points P L]
  obtain ⟨S,hS,hs⟩ := ContainedPlaneLines.pencil_lower (L:=L) m hm hcap
  let V := (univ : Finset (Finset P)).filter (fun X => X.card=m)
  have hne : V.Nonempty := ⟨S,mem_filter.mpr ⟨mem_univ _,hS⟩⟩
  obtain ⟨X,hX,hmax⟩ := exists_max_image V (fun Y => (contained P L Y).card) hne
  have hx := (mem_filter.mp hX).2
  let f := (contained P L X).card
  have hlow : (m-1)/q ≤ f := hs.trans (hmax S (mem_filter.mpr ⟨mem_univ _,hS⟩))
  have hu := ContainedPlaneLines.second_moment (L:=L) X
  change f*(q+1)^2 ≤ X.card*(q+f) at hu
  rw [hx] at hu
  refine ⟨f,⟨⟨X,hx,rfl⟩,?_⟩,hlow,hu,?_⟩
  · rintro _ ⟨Y,hY,rfl⟩
    exact hmax Y (mem_filter.mpr ⟨mem_univ _,hY⟩)
  · exact fun T hT ha hb => ContainedPlaneLines.relative (ProjectivePlane.one_lt_order P L) hm hlow hu hT ha hb
