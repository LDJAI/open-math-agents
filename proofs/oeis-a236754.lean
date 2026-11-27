import OMAStatements.S_oeis_a236754

/-!
# Semicircle spirals (OEIS A236754)

Source: Kival Ngaokrajang, https://oeis.org/A236754
Credit: @LDJAI

One reflection negates the difference of two entering endpoints. Thus any
odd-length lap is a reflection and two such laps return to the start.
On each block of four consecutive centers, the increasing order translates
by four, and swapping the final two centers makes the displacement zero.
-/

namespace OMA.S_oeis_a236754

lemma traverse_difference (cs : List ℕ) (x y : ℤ) :
    traverse cs x - traverse cs y =
      if cs.length % 2 = 0 then x - y else y - x := by
  induction cs generalizing x y with
  | nil => simp [traverse]
  | cons c cs ih =>
    simp only [traverse, List.length_cons]
    rw [ih]
    split <;> split <;> omega

lemma loop_of_odd_length {cs : List ℕ} (h : cs.length % 2 = 1) : IsLoop cs := by
  have hpar : cs.length % 2 ≠ 0 := by omega
  let x := start cs
  have hd := traverse_difference cs (traverse cs x) x
  rw [if_neg hpar] at hd
  refine ⟨2, by decide, by omega, ?_⟩
  change traverse cs (traverse cs x) = x
  omega

lemma odd_orders (n : ℕ) (hn : n % 2 = 1) :
    (∀ cs : List ℕ, cs.Perm (List.range n) → IsLoop cs) ∧ loopCount n = n.factorial := by
  classical
  have allLoop (cs : List ℕ) (hc : cs.Perm (List.range n)) : IsLoop cs := by
    apply loop_of_odd_length
    simpa only [hc.length_eq, List.length_range] using hn
  refine ⟨allLoop, ?_⟩
  unfold loopCount
  rw [List.filter_eq_self.mpr, List.length_permutations, List.length_range]
  intro cs hc
  exact decide_eq_true (allLoop cs (List.mem_permutations.mp hc))

lemma traverse_append (as bs : List ℕ) (x : ℤ) :
    traverse (as ++ bs) x = traverse bs (traverse as x) := by
  induction as generalizing x with
  | nil => rfl
  | cons a as ih => exact ih (2 * (a : ℤ) - x)

lemma range_four_blocks (k : ℕ) :
    List.range (4 * (k + 1)) =
      List.range (4 * k) ++ [4 * k, 4 * k + 1, 4 * k + 2, 4 * k + 3] := by
  rw [Nat.mul_succ, List.range_add]
  rfl

/-- Visit the last two centers of each consecutive block of four in reverse order. -/
def balancedOrder : ℕ → List ℕ
  | 0 => []
  | k + 1 => balancedOrder k ++ [4 * k, 4 * k + 1, 4 * k + 3, 4 * k + 2]

lemma balanced_perm (k : ℕ) : (balancedOrder k).Perm (List.range (4 * k)) := by
  induction k with
  | zero => exact List.Perm.refl []
  | succ k ih =>
    rw [balancedOrder, range_four_blocks]
    exact ih.append (.cons _ (.cons _ (.swap _ _ [])))

lemma balanced_pass (k : ℕ) (x : ℤ) : traverse (balancedOrder k) x = x := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [balancedOrder, traverse_append, ih]
    simp only [traverse, Int.natCast_add]
    omega

lemma increasing_pass (k : ℕ) (x : ℤ) :
    traverse (List.range (4 * k)) x = x + 4 * (k : ℤ) := by
  induction k with
  | zero => simp [traverse]
  | succ k ih =>
    rw [range_four_blocks, traverse_append, ih]
    simp only [traverse, Int.natCast_succ]
    omega

lemma afterLaps_translation {cs : List ℕ} {d : ℤ}
    (h : ∀ x, traverse cs x = x + d) (x : ℤ) (k : ℕ) :
    afterLaps cs x k = x + (k : ℤ) * d := by
  induction k with
  | zero => simp [afterLaps]
  | succ k ih =>
    rw [afterLaps, h, ih, Int.natCast_succ, Int.add_mul, Int.one_mul, Int.add_assoc]

lemma expanded_of_translation {cs : List ℕ} {d : ℤ} (hne : cs ≠ [])
    (hd : 0 < d) (h : ∀ x, traverse cs x = x + d) : IsExpanded cs := by
  cases cs with
  | nil => exact (hne rfl).elim
  | cons c cs =>
    intro B
    refine ⟨B + 2, ⟨0, by simp⟩, ?_⟩
    change B < (afterLaps (c :: cs) ((c : ℤ) - 1) (B + 2) - (c : ℤ)).natAbs
    rw [afterLaps_translation h]
    have habs := @Int.le_natAbs ((c : ℤ) - 1 + ((B + 2 : ℕ) : ℤ) * d - (c : ℤ))
    have hmul := Int.mul_le_mul_of_nonneg_left (show 1 ≤ d by omega)
      (show 0 ≤ ((B + 2 : ℕ) : ℤ) by omega)
    omega

lemma both_orders (k : ℕ) (hk : 0 < k) :
    (∃ cs : List ℕ, cs.Perm (List.range (4 * k)) ∧ IsLoop cs) ∧
    (∃ cs : List ℕ, cs.Perm (List.range (4 * k)) ∧ IsExpanded cs) := by
  have hlen : (balancedOrder k).length = 4 * k := by
    simpa only [List.length_range] using (balanced_perm k).length_eq
  constructor
  · refine ⟨balancedOrder k, balanced_perm k, 1, by decide, ?_, ?_⟩
    · omega
    · exact balanced_pass k _
  · refine ⟨List.range (4 * k), List.Perm.refl _, expanded_of_translation ?_ ?_ (increasing_pass k)⟩
    · intro he
      have hh := congrArg List.length he
      simp only [List.length_range, List.length_nil] at hh
      omega
    · omega

end OMA.S_oeis_a236754

open OMA.S_oeis_a236754

theorem OMA.solution : type_of% @OMA.S_oeis_a236754.main := by
  refine ⟨odd_orders, ?_⟩
  intro n hn hmod
  have he : 4 * (n / 4) = n := by omega
  simpa only [he] using both_orders (n / 4) (by omega)
