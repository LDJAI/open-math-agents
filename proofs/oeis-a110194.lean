import OMAStatements.S_oeis_a110194

namespace OMA
open OMA.S_oeis_a110194

theorem primeBool_spec (n : Nat) :
    primeBool n = true ↔ 2 ≤ n ∧ ∀ d : Nat, 2 ≤ d → d < n → n % d ≠ 0 := by
  simp only [primeBool, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range]
  constructor
  · intro ⟨hn,h⟩
    refine ⟨hn, ?_⟩
    intro d hd hd'
    rcases h d hd' with h' | h'
    · omega
    · exact h'
  · intro ⟨hn,h⟩
    refine ⟨hn, ?_⟩
    intro d hd
    by_cases hh : d < 2
    · exact Or.inl hh
    · exact Or.inr (h d (by omega) hd)

-- Verify the executable test agrees with mathlib's standard primality.
theorem primeBool_iff_prime (n : Nat) : primeBool n = true ↔ Nat.Prime n := by
  rw [primeBool_spec, Nat.prime_def]
  constructor
  · rintro ⟨hn, h⟩
    refine ⟨hn, ?_⟩
    intro d hd
    by_cases h1 : d = 1
    · exact Or.inl h1
    by_cases h2 : d = n
    · exact Or.inr h2
    have hle : d ≤ n := Nat.le_of_dvd (by omega) hd
    have h0 : d ≠ 0 := by
      intro h0
      subst d
      simp at hd
      omega
    exact False.elim (h d (by omega) (by omega) (Nat.dvd_iff_mod_eq_zero.mp hd))
  · rintro ⟨hn, h⟩
    refine ⟨hn, ?_⟩
    intro d hd hlt he
    have hh := h d (Nat.dvd_of_mod_eq_zero he)
    omega

theorem even_nonprime (n : Nat) (hn : 2 < n) (he : n % 2 = 0) : primeBool n = false := by
  cases h : primeBool n with
  | false => rfl
  | true =>
    exact False.elim (((primeBool_spec n).mp h).2 2 (by decide) hn he)

theorem exists_valid (x : Nat) : ∃ d : Nat, d < 9 ∧ valid x d = true := by
  by_cases hx0 : x = 0
  · subst x
    exact ⟨1, by decide, by decide⟩
  by_cases hx1 : x = 1
  · subst x
    exact ⟨8, by decide, by decide⟩
  by_cases he : x % 2 = 0
  · refine ⟨4, by decide, ?_⟩
    have hc := even_nonprime (x+4) (by omega) (by omega)
    simp [valid, show primeBool 4 = false by decide, hc]
  · refine ⟨1, by decide, ?_⟩
    have hc := even_nonprime (x+1) (by omega) (by omega)
    simp [valid, show primeBool 1 = false by decide, hc]

theorem gap_spec (x : Nat) :
    valid x (gap x) = true ∧ ∀ d : Nat, d < gap x → valid x d = false := by
  unfold gap
  cases h : (List.range 9).find? (valid x) with
  | none =>
    obtain ⟨d,hd,hv⟩ := exists_valid x
    exact False.elim ((List.find?_eq_none.mp h) d (List.mem_range.mpr hd) hv)
  | some v =>
    obtain ⟨hv,i,hi,he,hm⟩ := List.find?_eq_some_iff_getElem.mp h
    have e : i = v := by simpa only [List.getElem_range] using he
    subst v
    refine ⟨hv, ?_⟩
    intro d hd
    have hd' : d < i := by simpa using hd
    have hf := hm d hd'
    simpa using hf

theorem valid_iff (x d : Nat) :
    valid x d = true ↔ 0 < d ∧ ¬ Nat.Prime d ∧ ¬ Nat.Prime (x+d) := by
  simp [valid, Bool.and_eq_true, ← Bool.not_eq_true,
    ← primeBool_iff_prime, and_assoc]

theorem exact_greedy (x : Nat) :
    (0 < gap x ∧ ¬ Nat.Prime (gap x) ∧ ¬ Nat.Prime (x + gap x)) ∧
    ∀ d : Nat, d < gap x → ¬ (0 < d ∧ ¬ Nat.Prime d ∧ ¬ Nat.Prime (x+d)) := by
  obtain ⟨h, hm⟩ := gap_spec x
  refine ⟨(valid_iff x (gap x)).mp h, ?_⟩
  intro d hd hv
  have h1 := (valid_iff x d).mpr hv
  have h2 := hm d hd
  rw [h1] at h2
  contradiction

-- Every step below is checked by kernel reduction on small explicit integers.
theorem five_ones : a 56 = 1 ∧ a 57 = 1 ∧ a 58 = 1 ∧ a 59 = 1 ∧ a 60 = 1 := by
  have h0 : s 0 = 0 := rfl
  have g1 : gap 0 = 1 := by decide
  have h1 : s 1 = 1 := by rw [s, h0, g1]
  have g2 : gap 1 = 8 := by decide
  have h2 : s 2 = 9 := by rw [s, h1, g2]
  have g3 : gap 9 = 1 := by decide
  have h3 : s 3 = 10 := by rw [s, h2, g3]
  have g4 : gap 10 = 4 := by decide
  have h4 : s 4 = 14 := by rw [s, h3, g4]
  have g5 : gap 14 = 1 := by decide
  have h5 : s 5 = 15 := by rw [s, h4, g5]
  have g6 : gap 15 = 1 := by decide
  have h6 : s 6 = 16 := by rw [s, h5, g6]
  have g7 : gap 16 = 4 := by decide
  have h7 : s 7 = 20 := by rw [s, h6, g7]
  have g8 : gap 20 = 1 := by decide
  have h8 : s 8 = 21 := by rw [s, h7, g8]
  have g9 : gap 21 = 1 := by decide
  have h9 : s 9 = 22 := by rw [s, h8, g9]
  have g10 : gap 22 = 4 := by decide
  have h10 : s 10 = 26 := by rw [s, h9, g10]
  have g11 : gap 26 = 1 := by decide
  have h11 : s 11 = 27 := by rw [s, h10, g11]
  have g12 : gap 27 = 1 := by decide
  have h12 : s 12 = 28 := by rw [s, h11, g12]
  have g13 : gap 28 = 4 := by decide
  have h13 : s 13 = 32 := by rw [s, h12, g13]
  have g14 : gap 32 = 1 := by decide
  have h14 : s 14 = 33 := by rw [s, h13, g14]
  have g15 : gap 33 = 1 := by decide
  have h15 : s 15 = 34 := by rw [s, h14, g15]
  have g16 : gap 34 = 1 := by decide
  have h16 : s 16 = 35 := by rw [s, h15, g16]
  have g17 : gap 35 = 1 := by decide
  have h17 : s 17 = 36 := by rw [s, h16, g17]
  have g18 : gap 36 = 4 := by decide
  have h18 : s 18 = 40 := by rw [s, h17, g18]
  have g19 : gap 40 = 4 := by decide
  have h19 : s 19 = 44 := by rw [s, h18, g19]
  have g20 : gap 44 = 1 := by decide
  have h20 : s 20 = 45 := by rw [s, h19, g20]
  have g21 : gap 45 = 1 := by decide
  have h21 : s 21 = 46 := by rw [s, h20, g21]
  have g22 : gap 46 = 4 := by decide
  have h22 : s 22 = 50 := by rw [s, h21, g22]
  have g23 : gap 50 = 1 := by decide
  have h23 : s 23 = 51 := by rw [s, h22, g23]
  have g24 : gap 51 = 1 := by decide
  have h24 : s 24 = 52 := by rw [s, h23, g24]
  have g25 : gap 52 = 4 := by decide
  have h25 : s 25 = 56 := by rw [s, h24, g25]
  have g26 : gap 56 = 1 := by decide
  have h26 : s 26 = 57 := by rw [s, h25, g26]
  have g27 : gap 57 = 1 := by decide
  have h27 : s 27 = 58 := by rw [s, h26, g27]
  have g28 : gap 58 = 4 := by decide
  have h28 : s 28 = 62 := by rw [s, h27, g28]
  have g29 : gap 62 = 1 := by decide
  have h29 : s 29 = 63 := by rw [s, h28, g29]
  have g30 : gap 63 = 1 := by decide
  have h30 : s 30 = 64 := by rw [s, h29, g30]
  have g31 : gap 64 = 1 := by decide
  have h31 : s 31 = 65 := by rw [s, h30, g31]
  have g32 : gap 65 = 1 := by decide
  have h32 : s 32 = 66 := by rw [s, h31, g32]
  have g33 : gap 66 = 4 := by decide
  have h33 : s 33 = 70 := by rw [s, h32, g33]
  have g34 : gap 70 = 4 := by decide
  have h34 : s 34 = 74 := by rw [s, h33, g34]
  have g35 : gap 74 = 1 := by decide
  have h35 : s 35 = 75 := by rw [s, h34, g35]
  have g36 : gap 75 = 1 := by decide
  have h36 : s 36 = 76 := by rw [s, h35, g36]
  have g37 : gap 76 = 1 := by decide
  have h37 : s 37 = 77 := by rw [s, h36, g37]
  have g38 : gap 77 = 1 := by decide
  have h38 : s 38 = 78 := by rw [s, h37, g38]
  have g39 : gap 78 = 4 := by decide
  have h39 : s 39 = 82 := by rw [s, h38, g39]
  have g40 : gap 82 = 4 := by decide
  have h40 : s 40 = 86 := by rw [s, h39, g40]
  have g41 : gap 86 = 1 := by decide
  have h41 : s 41 = 87 := by rw [s, h40, g41]
  have g42 : gap 87 = 1 := by decide
  have h42 : s 42 = 88 := by rw [s, h41, g42]
  have g43 : gap 88 = 4 := by decide
  have h43 : s 43 = 92 := by rw [s, h42, g43]
  have g44 : gap 92 = 1 := by decide
  have h44 : s 44 = 93 := by rw [s, h43, g44]
  have g45 : gap 93 = 1 := by decide
  have h45 : s 45 = 94 := by rw [s, h44, g45]
  have g46 : gap 94 = 1 := by decide
  have h46 : s 46 = 95 := by rw [s, h45, g46]
  have g47 : gap 95 = 1 := by decide
  have h47 : s 47 = 96 := by rw [s, h46, g47]
  have g48 : gap 96 = 4 := by decide
  have h48 : s 48 = 100 := by rw [s, h47, g48]
  have g49 : gap 100 = 4 := by decide
  have h49 : s 49 = 104 := by rw [s, h48, g49]
  have g50 : gap 104 = 1 := by decide
  have h50 : s 50 = 105 := by rw [s, h49, g50]
  have g51 : gap 105 = 1 := by decide
  have h51 : s 51 = 106 := by rw [s, h50, g51]
  have g52 : gap 106 = 4 := by decide
  have h52 : s 52 = 110 := by rw [s, h51, g52]
  have g53 : gap 110 = 1 := by decide
  have h53 : s 53 = 111 := by rw [s, h52, g53]
  have g54 : gap 111 = 1 := by decide
  have h54 : s 54 = 112 := by rw [s, h53, g54]
  have g55 : gap 112 = 4 := by decide
  have h55 : s 55 = 116 := by rw [s, h54, g55]
  have g56 : gap 116 = 1 := by decide
  have h56 : s 56 = 117 := by rw [s, h55, g56]
  have g57 : gap 117 = 1 := by decide
  have h57 : s 57 = 118 := by rw [s, h56, g57]
  have g58 : gap 118 = 1 := by decide
  have h58 : s 58 = 119 := by rw [s, h57, g58]
  have g59 : gap 119 = 1 := by decide
  have h59 : s 59 = 120 := by rw [s, h58, g59]
  have g60 : gap 120 = 1 := by decide
  exact ⟨by simpa only [a, show 56-1=55 by decide, h55] using g56,
    by simpa only [a, show 57-1=56 by decide, h56] using g57,
    by simpa only [a, show 58-1=57 by decide, h57] using g58,
    by simpa only [a, show 59-1=58 by decide, h58] using g59,
    by simpa only [a, show 60-1=59 by decide, h59] using g60⟩

theorem cover (b : Nat → Nat) (hb : b 0 = 5)
    (h : ∀ n, Block (b n) (b (n+1))) :
    ∀ k : Nat, 5 ≤ k → ∃ n, b n ≤ k ∧ k < b (n+1) := by
  have inc (n : Nat) : b n < b (n+1) := by
    rcases h n with ha | ha <;> omega
  intro k
  induction k with
  | zero => omega
  | succ k ih =>
    intro hk
    by_cases hk' : 5 ≤ k
    · obtain ⟨n, hn, hn'⟩ := ih hk'
      by_cases ht : k+1 < b (n+1)
      · exact ⟨n, by omega, ht⟩
      · exact ⟨n+1, by omega, by have := inc (n+1); omega⟩
    · refine ⟨0, by omega, ?_⟩
      have := inc 0
      omega

theorem four_within (h : GapLanguage) (k : Nat) (hk : 5 ≤ k) :
    ∃ i : Nat, k ≤ i ∧ i ≤ k+4 ∧ a i = 4 := by
  obtain ⟨b, hb, ht⟩ := h
  obtain ⟨n, hn, hn'⟩ := cover b hb ht k hk
  rcases ht n with ⟨he, _, _, h4⟩ | ⟨he, _, _, _, _, h4, h5⟩
  · exact ⟨b n+2, by omega, by omega, h4⟩
  · by_cases hh : k ≤ b n+4
    · exact ⟨b n+4, hh, by omega, h4⟩
    · exact ⟨b n+5, by omega, by omega, h5⟩

end OMA

open OMA OMA.S_oeis_a110194

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a110194.main) := by
  intro h
  obtain ⟨i, hi, hi', h4⟩ := four_within h 56 (by decide)
  obtain ⟨h56,h57,h58,h59,h60⟩ := five_ones
  have hiCases : i = 56 ∨ i = 57 ∨ i = 58 ∨ i = 59 ∨ i = 60 := by omega
  rcases hiCases with rfl | rfl | rfl | rfl | rfl <;> omega

