import OMAStatements.S_oeis_a217447

namespace OMA.S_oeis_a217447

open scoped BigOperators

private def T (m : ℕ) : ℤ :=
  ∑ i ∈ Finset.range m, (i.factorial : ℤ)

private def F (m : ℕ) : ℤ := (m.factorial : ℤ)

private theorem T_succ (m : ℕ) : T (m + 1) = T m + F m := by
  simp only [T, F, Finset.sum_range_succ]

private theorem F_succ (m : ℕ) : F (m + 1) = ((m : ℤ) + 1) * F m := by
  simp [F, Nat.factorial_succ]

private theorem shifted_sum (m : ℕ) :
    (∑ i ∈ Finset.range m, ((i+1).factorial : ℤ)) = T (m+1) - 1 := by
  induction m with
  | zero => simp [T]
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    change T (m+1) - 1 + F (m+1) = T (m+1+1) - 1
    rw [T_succ (m+1)]
    ring

private theorem a_shift (m : ℕ) :
    a (m+3) = 4 * T (m+2) - 2 * ((m : ℤ) + 1) * T m +
      2 * T (m+1) - 4 := by
  unfold a
  rw [show m+3-2 = m+1 by omega, show m+3-3=m by omega]
  simp only [shifted_sum, Nat.cast_add, Nat.cast_ofNat]
  change 4 * (T (m+2) - 1) - 2 * ((m : ℤ) + 3 - 2) * T m +
    2 * (T (m+1) - 1) + 2 = _
  ring

end OMA.S_oeis_a217447

open OMA.S_oeis_a217447 in
theorem OMA.solution : type_of% @OMA.S_oeis_a217447.main := by
  intro n hn
  obtain rfl | hn' : n = 7 ∨ 8 ≤ n := by omega
  · norm_num [a, Finset.sum_range_succ, Nat.factorial_succ]
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m + 8 := ⟨n - 8, by omega⟩
  rw [show m+8-1=m+7 by omega, show m+8-2=m+6 by omega,
    show m+8-3=m+5 by omega, show m+8-4=m+4 by omega,
    show m+8-5=m+3 by omega]
  have ha (j : ℕ) : a (m+j+3) =
      4 * T (m+j+2) - 2 * ((m+j : ℕ) + (1 : ℤ)) * T (m+j) +
        2 * T (m+j+1) - 4 := by
    exact a_shift (m+j)
  have h0 := a_shift m
  have h1 : a (m+4) = _ := ha 1
  have h2 : a (m+5) = _ := ha 2
  have h3 : a (m+6) = _ := ha 3
  have h4 : a (m+7) = _ := ha 4
  have h5 : a (m+8) = _ := ha 5
  rw [h0, h1, h2, h3, h4, h5]
  have ht1 : T (m+1) = T m + F m := T_succ m
  have ht2 : T (m+2) = T (m+1) + F (m+1) := T_succ (m+1)
  have ht3 : T (m+3) = T (m+2) + F (m+2) := T_succ (m+2)
  have ht4 : T (m+4) = T (m+3) + F (m+3) := T_succ (m+3)
  have ht5 : T (m+5) = T (m+4) + F (m+4) := T_succ (m+4)
  have ht6 : T (m+6) = T (m+5) + F (m+5) := T_succ (m+5)
  have ht7 : T (m+7) = T (m+6) + F (m+6) := T_succ (m+6)
  have hf1 : F (m+1) = ((m : ℤ)+1) * F m := F_succ m
  have hf2 : F (m+2) = (((m+1 : ℕ) : ℤ)+1) * F (m+1) := F_succ (m+1)
  have hf3 : F (m+3) = (((m+2 : ℕ) : ℤ)+1) * F (m+2) := F_succ (m+2)
  have hf4 : F (m+4) = (((m+3 : ℕ) : ℤ)+1) * F (m+3) := F_succ (m+3)
  have hf5 : F (m+5) = (((m+4 : ℕ) : ℤ)+1) * F (m+4) := F_succ (m+4)
  have hf6 : F (m+6) = (((m+5 : ℕ) : ℤ)+1) * F (m+5) := F_succ (m+5)
  simp only [ht7, ht6, ht5, ht4, ht3, ht2, ht1,
    hf6, hf5, hf4, hf3, hf2, hf1, Nat.cast_add, Nat.cast_ofNat]
  ring


