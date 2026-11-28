import OMAStatements.S_oeis_a191873
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.Push

open Finset OMA.S_oeis_a191873

namespace ZeroDiagonalBoards

theorem subset_free {n : ℕ} {A B : Board n} (hA : rectangleFree A) (h : B ⊆ A) :
    rectangleFree B := fun i k j l hi hj a b c d => hA i k j l hi hj (h a) (h b) (h c) (h d)

theorem transpose_free {n : ℕ} {A : Board n} (hA : rectangleFree A) :
    rectangleFree (A.map (Equiv.prodComm _ _).toEmbedding) := by
  intro i k j l hi hj a b c d
  simp only [Finset.mem_map_equiv, Equiv.prodComm_symm,
    Equiv.prodComm_apply, Prod.swap_prod_mk] at a b c d
  exact hA j l i k hj hi a c b d

theorem full_row_bound {n : ℕ} {A : Board n} (hA : rectangleFree A)
    (i : Fin n) (hi : ∀ j, (i,j) ∈ A) : A.card ≤ n+(n-1) := by
  classical
  let S := A.filter (fun p => p.1=i)
  have hs : S.card ≤ n := by
    have h : S ⊆ ({i}:Finset (Fin n)) ×ˢ univ := by
      intro p hp
      exact mem_product.mpr ⟨mem_singleton.mpr (mem_filter.mp hp).2,mem_univ _⟩
    simpa using card_le_card h
  let T := A.filter (fun p => p.1≠i)
  have ht : T.card ≤ (univ.erase i).card := by
    apply card_le_card_of_injOn Prod.fst
    · intro p hp
      exact mem_erase.mpr ⟨(mem_filter.mp hp).2, mem_univ _⟩
    · rintro ⟨u,v⟩ hp ⟨w,x⟩ hq he
      change u=w at he
      subst w
      congr 1
      by_contra hne
      exact hA u i v x (mem_filter.mp hp).2 hne (mem_filter.mp hp).1 (mem_filter.mp hq).1 (hi _) (hi _)
  have hh := card_filter_add_card_filter_not (s:=A) (p:=fun p=>p.1=i)
  change S.card+T.card=A.card at hh
  simp at ht
  omega

theorem fallback {n : ℕ} (hn : 3≤n) : ∃ B : Board n, rectangleFree B ∧
    (∀ i, (i,i) ∉ B) ∧ B.card=n+(n-1) := by
  classical
  let a : Fin n := ⟨0,by omega⟩
  let b : Fin n := ⟨1,by omega⟩
  let c : Fin n := ⟨2,by omega⟩
  have hab : a≠b := by intro h; have hh := congrArg Fin.val h; dsimp [a,b,c] at hh; omega
  have hac : a≠c := by intro h; have hh := congrArg Fin.val h; dsimp [a,b,c] at hh; omega
  have hbc : b≠c := by intro h; have hh := congrArg Fin.val h; dsimp [a,b,c] at hh; omega
  let U := (univ : Finset (Fin n)).erase a
  let P := ({a}:Finset (Fin n)) ×ˢ U
  let Q := U ×ˢ ({a}:Finset (Fin n))
  let B := insert (b,c) (P ∪ Q)
  have hm (i j : Fin n) : (i,j) ∈ B ↔
      (i=b ∧ j=c) ∨ (i=a ∧ j≠a) ∨ (i≠a ∧ j=a) := by
    simp only [B,P,Q,U,mem_insert,mem_union,mem_product,mem_singleton,mem_erase,mem_univ,and_true,Prod.mk.injEq]
  refine ⟨B,?_,?_,?_⟩
  · intro i k j l hi hj h1 h2 h3 h4
    rw [hm] at h1 h2 h3 h4
    grind
  · intro i h
    have := (hm i i).mp h
    grind
  · have hdis : Disjoint P Q := by
      rw [disjoint_left]
      rintro ⟨i,j⟩ hp hq
      simp [P,Q,U] at hp hq
      grind
    have hnew : (b,c) ∉ P ∪ Q := by simp [P,Q,U,hab,hac,Ne.symm hab,Ne.symm hac]
    rw [show B=insert (b,c) (P∪Q) from rfl,card_insert_of_notMem hnew,card_union_of_disjoint hdis]
    simp [P,Q,U]
    omega

theorem permute_columns {n : ℕ} {A : Board n} (hA : rectangleFree A)
    (hr : ∀ i,∃ j,(i,j) ∉ A) (hc : ∀ j,∃ i,(i,j) ∉ A) :
    ∃ B : Board n, rectangleFree B ∧ (∀ i,(i,i) ∉ B) ∧ B.card=A.card := by
  classical
  let N (i : Fin n) := univ.filter fun j => (i,j) ∉ A
  have hh (S : Finset (Fin n)) : S.card ≤ (S.biUnion N).card := by
    by_cases e : S=∅
    · simp [e]
    by_cases f : S=univ
    · have hu : S.biUnion N=univ := by
        ext j
        obtain ⟨i,hi⟩ := hc j
        simp [f,N,show ∃ k,(k,j) ∉ A from ⟨i,hi⟩]
      rw [hu,f]
    by_cases single : S.card=1
    · obtain ⟨i,hi⟩ := nonempty_iff_ne_empty.mpr e
      obtain ⟨j,hj⟩ := hr i
      have : j∈S.biUnion N := mem_biUnion.mpr ⟨i,hi,by simpa [N] using hj⟩
      rw [single]
      exact card_pos.mpr ⟨j,this⟩
    obtain ⟨i,hi,k,hk,hik⟩ := one_lt_card.mp (by have := card_pos.mpr (nonempty_iff_ne_empty.mpr e);omega : 1<S.card)
    let T := (S.biUnion N)ᶜ
    have hfilled {u v} (hu : u∈S) (hv : v∈T) : (u,v)∈A := by
      by_contra h
      exact (mem_compl.mp hv) (mem_biUnion.mpr ⟨u,hu,by simpa [N] using h⟩)
    have ht : T.card≤1 := by
      apply card_le_one.mpr
      intro j hj l hl
      by_contra hjl
      exact hA i k j l hik hjl (hfilled hi hj) (hfilled hi hl) (hfilled hk hj) (hfilled hk hl)
    have hs := card_lt_card (ssubset_univ_iff.mpr f)
    have hu := card_le_univ (S.biUnion N)
    simp [T,card_compl] at ht
    simp at hs hu
    omega
  obtain ⟨f,hf,hn⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' N).mp hh
  let p := Equiv.ofBijective f ⟨hf,Finite.surjective_of_injective hf⟩
  let e := Equiv.prodCongr (Equiv.refl (Fin n)) p.symm
  let B := A.map e.toEmbedding
  have hmem (i j) : (i,j) ∈ B ↔ (i,f j) ∈ A := by
    change _ ∈ A.map e.toEmbedding ↔ _
    rw [mem_map_equiv]
    rfl
  refine ⟨B,?_,?_,card_map _⟩
  · intro i k j l hi hj a b c d
    exact hA i k (f j) (f l) hi (hf.ne hj) ((hmem _ _).mp a) ((hmem _ _).mp b) ((hmem _ _).mp c) ((hmem _ _).mp d)
  · intro i h
    exact (mem_filter.mp (hn i)).2 ((hmem i i).mp h)

theorem dominate {n : ℕ} (hn : 3≤n) (A : Board n) (hA : rectangleFree A) :
    ∃ B : Board n, rectangleFree B ∧ (∀ i,(i,i) ∉ B) ∧ A.card≤B.card := by
  classical
  by_cases hr : ∀ i,∃ j,(i,j) ∉ A
  · by_cases hc : ∀ j,∃ i,(i,j) ∉ A
    · obtain ⟨B,hf,hd,hw⟩ := permute_columns hA hr hc
      exact ⟨B,hf,hd,hw.ge⟩
    · push Not at hc
      obtain ⟨j,hj⟩ := hc
      obtain ⟨B,hf,hd,hw⟩ := fallback hn
      refine ⟨B,hf,hd,?_⟩
      have h := full_row_bound (transpose_free hA) j (by intro i; simpa using hj i)
      simpa [hw] using h
  · push Not at hr
    obtain ⟨i,hi⟩ := hr
    obtain ⟨B,hf,hd,hw⟩ := fallback hn
    exact ⟨B,hf,hd,hw ▸ full_row_bound hA i hi⟩

end ZeroDiagonalBoards

theorem OMA.solution : type_of% @OMA.S_oeis_a191873.main := by
  classical
  intro n hn
  let V := (univ : Finset (Board n)).filter rectangleFree
  have hempty : rectangleFree (∅ : Board n) := by intro i k j l hi hj a; simp at a
  have hV : V.Nonempty := ⟨∅,mem_filter.mpr ⟨mem_univ _,hempty⟩⟩
  obtain ⟨A,hA,hm⟩ := exists_max_image V Finset.card hV
  have hf := (mem_filter.mp hA).2
  have hub (X : Board n) (hx : rectangleFree X) : X.card ≤ A.card :=
    hm X (mem_filter.mpr ⟨mem_univ _,hx⟩)
  obtain ⟨B,hB,hd,hb⟩ := ZeroDiagonalBoards.dominate hn A hf
  have heq := le_antisymm (hub B hB) hb
  have hnot : A ≠ univ := by
    intro eq
    let x : Fin n := ⟨0,by omega⟩
    let y : Fin n := ⟨1,by omega⟩
    have hxy : x≠y := by intro hh; have := congrArg Fin.val hh; contradiction
    apply hf x y x y hxy hxy <;> simp [eq]
  have hcap := card_lt_card (ssubset_univ_iff.mpr hnot)
  simp at hcap
  refine ⟨A.card,A.card,A.card+1,?_,?_,?_,rfl,by omega⟩
  · refine ⟨⟨B,hB,hd,heq⟩,?_⟩
    rintro _ ⟨X,hX,_,rfl⟩
    exact hub X hX
  · refine ⟨⟨A,hf,rfl⟩,?_⟩
    rintro _ ⟨X,hX,rfl⟩
    exact hub X hX
  · constructor
    · refine ⟨by omega,?_⟩
      intro X hX hF
      have := hub X hF
      omega
    · intro k hk
      by_contra! hsmall
      obtain ⟨X,hX,hkX⟩ := exists_subset_card_eq (s:=A) (show k≤A.card by omega)
      exact hk.2 X hkX (ZeroDiagonalBoards.subset_free hf hX)
