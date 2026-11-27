import GridCore
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Powerset

namespace GridCounter

theorem choices_nodup (n k : Nat) : (choices n k).Nodup :=
  List.nodup_sublistsLen _ List.nodup_range

/-- The list enumeration has exactly one representative of every size-k edge subset. -/
def choicesEquiv (n k : Nat) :
    {l : List Nat // l ∈ choices n k} ≃
    {s : Finset Nat // s ∈ (Finset.range (n*(n+1))).powersetCard k} where
  toFun l := by
    refine ⟨l.val.toFinset,?_⟩
    obtain ⟨hl,hk⟩ := List.mem_sublistsLen.mp l.2
    have hn := hl.nodup List.nodup_range
    refine Finset.mem_powersetCard.mpr ⟨?_,?_⟩
    · intro i hi
      exact Finset.mem_range.mpr (List.mem_range.mp (hl.subset (List.mem_toFinset.mp hi)))
    · simpa [List.toFinset_card_of_nodup hn] using hk
  invFun s := by
    refine ⟨s.val.sort,?_⟩
    obtain ⟨hs,hk⟩ := Finset.mem_powersetCard.mp s.2
    refine List.mem_sublistsLen.mpr ⟨?_,by simpa using hk⟩
    apply List.sublist_of_subperm_of_sortedLE
    · apply List.subperm_of_subset (Finset.sort_nodup _ _)
      intro i hi
      exact List.mem_range.mpr (Finset.mem_range.mp (hs (by simpa using hi)))
    · exact (Finset.pairwise_sort _ _).sortedLE
    · exact (List.sortedLT_range _).sortedLE
  left_inv l := by
    apply Subtype.ext
    have hl := (List.mem_sublistsLen.mp l.2).1
    exact (List.toFinset_sort _ (hl.nodup List.nodup_range)).mpr
      (List.Pairwise.sublist hl (List.sortedLT_range _).sortedLE.pairwise)
  right_inv s := by
    apply Subtype.ext
    exact Finset.sort_toFinset _ _

end GridCounter
