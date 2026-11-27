import Mathlib.Data.Finset.Card

/-!
Partial result for Left To Solve mo-177894. Write `beats u v` for a
strict pairwise win. Domination allows a selected candidate to cover itself.
The order-minimality hypothesis below only compares induced subtournaments.
-/

namespace TournamentResearch

variable {V : Type*} [DecidableEq V]

def Dominates (beats : V → V → Prop) (U D : Finset V) : Prop :=
  D ⊆ U ∧ ∀ v ∈ U, v ∈ D ∨ ∃ u ∈ D, beats u v

def HasDominationNumber (beats : V → V → Prop) (U : Finset V) (k : ℕ) : Prop :=
  (∃ D, Dominates beats U D ∧ D.card = k) ∧
    ∀ D, Dominates beats U D → k ≤ D.card

private theorem insert_dominates {beats : V → V → Prop} {U D : Finset V}
    (x : V) (h : Dominates beats U D) :
    Dominates beats (insert x U) (insert x D) := by
  constructor
  · exact Finset.insert_subset_insert x h.1
  · intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact Or.inl (Finset.mem_insert_self _ _)
    · rcases h.2 v hv with hmem | ⟨u, hu, hb⟩
      · exact Or.inl (Finset.mem_insert_of_mem hmem)
      · exact Or.inr ⟨u, Finset.mem_insert_of_mem hu, hb⟩

/-- Although deleting one vertex can increase domination number, a finite
digraph with no induced subgraph of order below `U.card` having domination
number exactly `k` has domination number below `k` on each proper subset. -/
theorem below_threshold_on_smaller {beats : V → V → Prop} {U : Finset V}
    {k : ℕ} (hk : 0 < k)
    (hmin : ∀ T ⊆ U, T.card < U.card → ¬ HasDominationNumber beats T k)
    (T : Finset V) (hTU : T ⊆ U) (hsize : T.card < U.card) :
    ∃ D, Dominates beats T D ∧ D.card < k := by
  induction T using Finset.induction_on with
  | empty =>
    exact ⟨∅, ⟨fun _ h => h, by simp⟩, by simpa using hk⟩
  | @insert x T hx ih =>
    obtain ⟨D, hD, hcard⟩ := ih
      (fun a ha => hTU (Finset.mem_insert_of_mem ha))
      (by rw [Finset.card_insert_of_notMem hx] at hsize; omega)
    have hd := insert_dominates x hD
    have hxD : x ∉ D := fun h => hx (hD.1 h)
    have hdc : (insert x D).card ≤ k := by
      rw [Finset.card_insert_of_notMem hxD]
      omega
    by_contra! hno
    have hlower : ∀ S, Dominates beats (insert x T) S → k ≤ S.card := hno
    exact hmin (insert x T) hTU hsize
      ⟨⟨insert x D, hd, Nat.le_antisymm hdc (hlower _ hd)⟩, hlower⟩

/-- Deleting any vertex of a smallest-order tournament of domination number
`k` leaves domination number exactly `k−1`. Every minimum dominating set
after deletion lies in the out-neighborhood of the deleted vertex. -/
theorem vertex_deletion {beats : V → V → Prop} {U : Finset V} {k : ℕ}
    (ht : ∀ u ∈ U, ∀ v ∈ U, u ≠ v → beats u v ∨ beats v u)
    (hk : 0 < k) (hU : HasDominationNumber beats U k)
    (hmin : ∀ T ⊆ U, T.card < U.card → ¬ HasDominationNumber beats T k)
    (x : V) (hx : x ∈ U) :
    HasDominationNumber beats (U.erase x) (k-1) ∧
      ∀ D, Dominates beats (U.erase x) D → D.card = k-1 →
        (∀ d ∈ D, beats x d ∧ ¬ beats d x) ∧
        Dominates beats U (insert x D) ∧ (insert x D).card = k := by
  have hrestore : insert x (U.erase x) = U := Finset.insert_erase hx
  have hlower (S : Finset V) (hS : Dominates beats (U.erase x) S) :
      k - 1 ≤ S.card := by
    have hdom := insert_dominates x hS
    rw [hrestore] at hdom
    have h := hU.2 _ hdom
    have hxs : x ∉ S := fun hm => (Finset.ne_of_mem_erase (hS.1 hm)) rfl
    rw [Finset.card_insert_of_notMem hxs] at h
    omega
  obtain ⟨D, hD, hc⟩ := below_threshold_on_smaller hk hmin
    (U.erase x) (Finset.erase_subset x U) (Finset.card_erase_lt_of_mem hx)
  constructor
  · exact ⟨⟨D, hD, by have := hlower D hD; omega⟩, hlower⟩
  · intro S hS hcard
    have hxs : x ∉ S := fun hm => (Finset.ne_of_mem_erase (hS.1 hm)) rfl
    have hrestoreDom := insert_dominates x hS
    rw [hrestore] at hrestoreDom
    refine ⟨?_, hrestoreDom, ?_⟩
    · intro d hd
      have hn : ¬ beats d x := by
        intro hb
        have hall : Dominates beats U S := by
          refine ⟨fun _ hm => Finset.mem_of_mem_erase (hS.1 hm), ?_⟩
          intro v hv
          by_cases hvx : v = x
          · subst v
            exact Or.inr ⟨d, hd, hb⟩
          · exact hS.2 v (Finset.mem_erase.mpr ⟨hvx, hv⟩)
        have := hU.2 _ hall
        omega
      exact ⟨(ht d (Finset.mem_of_mem_erase (hS.1 hd)) x hx
        (Finset.ne_of_mem_erase (hS.1 hd))).resolve_left hn, hn⟩
    · rw [Finset.card_insert_of_notMem hxs]
      omega

end TournamentResearch

namespace TournamentResearch

variable {V : Type*} [DecidableEq V]

/-- No loops, and precisely one direction wins each distinct pair. -/
def IsTournamentOn (beats : V → V → Prop) (U : Finset V) : Prop :=
  (∀ v ∈ U, ¬ beats v v) ∧
  ∀ u ∈ U, ∀ v ∈ U, u ≠ v → (beats u v ↔ ¬ beats v u)

/-- Merge the out-neighborhoods of x and y at x. The compressed tournament
will use only the vertices in U.erase y. -/
def contractAt (beats : V → V → Prop) (x y u v : V) : Prop :=
  if u = x then v ≠ x ∧ (beats x v ∨ beats y v)
  else if v = x then ¬ (beats x u ∨ beats y u) else beats u v

private theorem contract_tournament {beats : V → V → Prop} {U : Finset V}
    (ht : IsTournamentOn beats U) (x y : V) :
    IsTournamentOn (contractAt beats x y) U := by
  classical
  constructor
  · intro v hv
    by_cases h : v = x
    · subst v
      simp [contractAt]
    · simpa [contractAt, h] using ht.1 v hv
  · intro u hu v hv huv
    by_cases hux : u = x
    · subst u
      simp [contractAt, huv.symm]
      tauto
    · by_cases hvx : v = x
      · subst v
        simp [contractAt, hux]
      · simpa [contractAt, hux, hvx] using ht.2 u hu v hv huv

/-- In an order-minimal finite tournament of domination number k, *each
prescribed pair* belongs to a minimum dominating set. The global minimality
assumption compares all smaller tournaments, including the contracted one. -/
theorem every_pair_extends {beats : V → V → Prop} {U : Finset V} {k : ℕ}
    (ht : IsTournamentOn beats U) (hk : 0 < k)
    (hU : HasDominationNumber beats U k)
    (hmin : ∀ (r : V → V → Prop) (T : Finset V), T ⊆ U → T.card < U.card →
      IsTournamentOn r T → ¬ HasDominationNumber r T k)
    (x y : V) (hx : x ∈ U) (hy : y ∈ U) (hxy : x ≠ y) :
    ∃ S, Dominates beats U S ∧ S.card = k ∧ x ∈ S ∧ y ∈ S := by
  classical
  let r := contractAt beats x y
  have ht' : IsTournamentOn r U := contract_tournament ht x y
  have hmin' : ∀ T ⊆ U, T.card < U.card → ¬ HasDominationNumber r T k := by
    intro T hT hcard
    exact hmin r T hT hcard ⟨fun v hv => ht'.1 v (hT hv),
      fun u hu v hv => ht'.2 u (hT hu) v (hT hv)⟩
  obtain ⟨D, hD, hc⟩ := below_threshold_on_smaller hk hmin'
    (U.erase y) (Finset.erase_subset y U) (Finset.card_erase_lt_of_mem hy)
  have hyD : y ∉ D := fun hm => (Finset.ne_of_mem_erase (hD.1 hm)) rfl
  have hinU {v : V} (hv : v ∈ D) : v ∈ U := Finset.mem_of_mem_erase (hD.1 hv)
  have hxD : x ∈ D := by
    by_contra hmiss
    obtain ⟨w, hw, hbeat⟩ := (hD.2 x (Finset.mem_erase.mpr ⟨hxy,hx⟩)).resolve_left hmiss
    have hwx : w ≠ x := fun e => hmiss (e ▸ hw)
    have hwy : w ≠ y := fun e => hyD (e ▸ hw)
    have hneg : ¬ (beats x w ∨ beats y w) := by
      simpa [r, contractAt, hwx] using hbeat
    have hbx : beats w x := (ht.2 w (hinU hw) x hx hwx).2
      (fun h => hneg (Or.inl h))
    have hby : beats w y := (ht.2 w (hinU hw) y hy hwy).2
      (fun h => hneg (Or.inr h))
    have hall : Dominates beats U D := by
      refine ⟨fun _ hm => hinU hm, ?_⟩
      intro v hv
      by_cases hvy : v = y
      · subst v
        exact Or.inr ⟨w, hw, hby⟩
      by_cases hvx : v = x
      · subst v
        exact Or.inr ⟨w, hw, hbx⟩
      rcases hD.2 v (Finset.mem_erase.mpr ⟨hvy,hv⟩) with h | ⟨d,hd,hh⟩
      · exact Or.inl h
      · have hdx : d ≠ x := fun e => hmiss (e ▸ hd)
        exact Or.inr ⟨d, hd, by simpa [r, contractAt, hdx, hvx] using hh⟩
    have := hU.2 D hall
    omega
  have hlift : Dominates beats U (insert y D) := by
    refine ⟨Finset.insert_subset hy (fun _ hm => hinU hm), ?_⟩
    intro v hv
    by_cases hvy : v = y
    · subst v
      exact Or.inl (Finset.mem_insert_self _ _)
    by_cases hvx : v = x
    · subst v
      exact Or.inl (Finset.mem_insert_of_mem hxD)
    rcases hD.2 v (Finset.mem_erase.mpr ⟨hvy, hv⟩) with h | ⟨d, hd, hh⟩
    · exact Or.inl (Finset.mem_insert_of_mem h)
    · by_cases hdx : d = x
      · subst d
        have hwin : beats x v ∨ beats y v := by simpa [r, contractAt, hvx] using hh
        rcases hwin with h | h
        · exact Or.inr ⟨x, Finset.mem_insert_of_mem hxD, h⟩
        · exact Or.inr ⟨y, Finset.mem_insert_self _ _, h⟩
      · exact Or.inr ⟨d, Finset.mem_insert_of_mem hd, by
            simpa [r, contractAt, hdx, hvx] using hh⟩
  refine ⟨insert y D, hlift, ?_, Finset.mem_insert_of_mem hxD, Finset.mem_insert_self _ _⟩
  have hl := hU.2 _ hlift
  rw [Finset.card_insert_of_notMem hyD] at hl ⊢
  omega

end TournamentResearch

namespace TournamentResearch

variable {V : Type*} [DecidableEq V]

/-- Every directed edge in such a tournament belongs to a directed triangle. -/
theorem triangle_through_edge {beats : V → V → Prop} {U : Finset V} {k : ℕ}
    (ht : IsTournamentOn beats U) (hk : 0 < k)
    (hU : HasDominationNumber beats U k)
    (hmin : ∀ (r : V → V → Prop) (T : Finset V), T ⊆ U → T.card < U.card →
      IsTournamentOn r T → ¬ HasDominationNumber r T k)
    (x y : V) (hx : x ∈ U) (hy : y ∈ U) (hxy : beats x y) :
    ∃ w ∈ U, w ≠ x ∧ w ≠ y ∧ beats y w ∧ beats w x := by
  classical
  have hne : x ≠ y := by
    rintro rfl
    exact ht.1 x hx hxy
  obtain ⟨S, hS, hcard, hxS, hyS⟩ := every_pair_extends ht hk hU hmin x y hx hy hne
  have hn : ¬ Dominates beats U (S.erase y) := by
    intro hd
    have h := hU.2 _ hd
    have hlt := Finset.card_erase_lt_of_mem hyS
    omega
  have hsub : S.erase y ⊆ U := (Finset.erase_subset y S).trans hS.1
  have hmiss : ¬ ∀ w ∈ U, w ∈ S.erase y ∨ ∃ d ∈ S.erase y, beats d w :=
    fun h => hn ⟨hsub,h⟩
  push Not at hmiss
  obtain ⟨w, hwU, hwS, hnowin⟩ := hmiss
  have hxE : x ∈ S.erase y := Finset.mem_erase.mpr ⟨hne,hxS⟩
  have hwx : w ≠ x := fun e => hwS (e ▸ hxE)
  have hwy : w ≠ y := fun e => hnowin x hxE (e ▸ hxy)
  have hbwx : beats w x := (ht.2 w hwU x hx hwx).2 (hnowin _ hxE)
  refine ⟨w,hwU,hwx,hwy,?_,hbwx⟩
  rcases hS.2 w hwU with hmem | ⟨d,hd,hdw⟩
  · exact False.elim (hwS (Finset.mem_erase.mpr ⟨hwy,hmem⟩))
  · by_cases he : d = y
    · exact he ▸ hdw
    · exact False.elim (hnowin d (Finset.mem_erase.mpr ⟨he,hd⟩) hdw)

end TournamentResearch
