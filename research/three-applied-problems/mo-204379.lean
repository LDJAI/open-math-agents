import OMAStatements.S_mo_204379
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

open Set
open scoped BigOperators

namespace OMA.S_mo_204379

private noncomputable def component (k t : ℝ) := t - t / (1 + k*t)
private noncomputable def score (k t : ℝ) := k * (2+k*t) / (1+k*t)^2
private noncomputable def slope (k t : ℝ) := -(k^2 * (3+k*t)) / (1+k*t)^3

private theorem denominator {k t : ℝ} (hk : -1 < k) (ht : t ∈ Icc 0 1) :
    0 < 1+k*t := by
  rcases ht.1.eq_or_lt with ht0 | htpos
  · rw [← ht0]
    norm_num
  · have h := mul_pos (show 0 < k+1 by linarith) htpos
    nlinarith [ht.2]

private theorem component_deriv {k t : ℝ} (hx : 0 < 1+k*t) :
    HasDerivAt (component k) (t * score k t) t := by
  have hv : HasDerivAt (fun u : ℝ => 1 + k*u) k t := by
    simpa using ((hasDerivAt_id t).const_mul k).const_add 1
  have hh := (hasDerivAt_id t).sub ((hasDerivAt_id t).div hv hx.ne')
  apply hh.congr_deriv
  change 1 - (1*(1+k*t)-t*k)/(1+k*t)^2 = t * score k t
  unfold score
  field_simp [hx.ne']
  <;> ring

private theorem score_deriv {k t : ℝ} (hx : 0 < 1+k*t) :
    HasDerivAt (score k) (slope k t) t := by
  have hv : HasDerivAt (fun u : ℝ => 1 + k*u) k t := by
    simpa using ((hasDerivAt_id t).const_mul k).const_add 1
  have hw : HasDerivAt (fun u : ℝ => 2 + k*u) k t := by
    simpa using ((hasDerivAt_id t).const_mul k).const_add 2
  have hh := (hw.const_mul k).div (hv.pow 2) (pow_ne_zero 2 hx.ne')
  apply hh.congr_deriv
  change (k*k*(1+k*t)^2 - k*(2+k*t)*(2*(1+k*t)^1*k)) / ((1+k*t)^2)^2 = slope k t
  unfold slope
  field_simp [hx.ne']
  <;> ring

private noncomputable def F {n : ℕ} (k : Fin n → ℝ) (t : ℝ) := ∑ i, component (k i) t
private noncomputable def G {n : ℕ} (k : Fin n → ℝ) (t : ℝ) := ∑ i, score (k i) t

private theorem dF {n : ℕ} (k : Fin n → ℝ) (hk : ∀ i, -1 < k i) {t : ℝ}
    (ht : t ∈ Icc 0 1) : HasDerivAt (F k) (t*G k t) t := by
  unfold F G
  rw [Finset.mul_sum]
  exact HasDerivAt.fun_sum fun i _ => component_deriv (denominator (hk i) ht)

private theorem dG {n : ℕ} (k : Fin n → ℝ) (hk : ∀ i, -1 < k i) {t : ℝ}
    (ht : t ∈ Icc 0 1) : HasDerivAt (G k) (∑ i, slope (k i) t) t :=
  HasDerivAt.fun_sum fun i _ => score_deriv (denominator (hk i) ht)

private theorem shape {n : ℕ} (k : Fin n → ℝ) (hk : ∀ i, -1 < k i)
    (hnon : ∃ i, k i ≠ 0) (hend : F k 0 = F k 1) :
    ∃ c ∈ Ioo (0:ℝ) 1, ∀ t ∈ Ioo (0:ℝ) 1, t ≠ c → F k t < F k c := by
  have hcont : ContinuousOn (F k) (Icc 0 1) := fun t ht =>
    (dF k hk ht).continuousAt.continuousWithinAt
  obtain ⟨c, hc, hcrit⟩ := exists_hasDerivAt_eq_zero zero_lt_one hcont hend
    (fun t ht => dF k hk ⟨ht.1.le, ht.2.le⟩)
  have hGc : G k c = 0 := (mul_eq_zero.mp hcrit).resolve_left hc.1.ne'
  have hanti : StrictAntiOn (G k) (Icc 0 1) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc ..)
      (fun t ht => (dG k hk ht).continuousAt.continuousWithinAt)
    rw [interior_Icc]
    intro t ht
    have hm : t ∈ Icc (0:ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
    rw [(dG k hk hm).deriv]
    obtain ⟨i, hi⟩ := hnon
    apply Finset.sum_neg'
    · intro j _
      have hx := denominator (hk j) hm
      have hy : 0 < 3 + k j*t := by linarith
      exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (mul_nonneg (sq_nonneg _) hy.le)) (pow_nonneg hx.le 3)
    · refine ⟨i, Finset.mem_univ _, ?_⟩
      have hx := denominator (hk i) hm
      have hy : 0 < 3 + k i*t := by linarith
      have hz := sq_pos_of_ne_zero hi
      exact div_neg_of_neg_of_pos (neg_neg_of_pos (mul_pos hz hy)) (pow_pos hx 3)
  refine ⟨c, hc, ?_⟩
  intro t ht hne
  have hcm : c ∈ Icc (0:ℝ) 1 := ⟨hc.1.le, hc.2.le⟩
  rcases lt_or_gt_of_ne hne with htc | hct
  · have hinc : StrictMonoOn (F k) (Icc 0 c) := by
      apply strictMonoOn_of_deriv_pos (convex_Icc ..) (hcont.mono (Icc_subset_Icc le_rfl hc.2.le))
      rw [interior_Icc]
      intro x hx
      have hxm : x ∈ Icc (0:ℝ) 1 := ⟨hx.1.le, (hx.2.trans hc.2).le⟩
      rw [(dF k hk hxm).deriv]
      exact mul_pos hx.1 (hGc ▸ hanti hxm hcm hx.2)
    exact hinc ⟨ht.1.le, htc.le⟩ ⟨hc.1.le, le_rfl⟩ htc
  · have hdec : StrictAntiOn (F k) (Icc c 1) := by
      apply strictAntiOn_of_deriv_neg (convex_Icc ..) (hcont.mono (Icc_subset_Icc hc.1.le le_rfl))
      rw [interior_Icc]
      intro x hx
      have hxm : x ∈ Icc (0:ℝ) 1 := ⟨(hc.1.trans hx.1).le, hx.2.le⟩
      rw [(dF k hk hxm).deriv]
      exact mul_neg_of_pos_of_neg (hc.1.trans hx.1) (hGc ▸ hanti hcm hxm hx.1)
    exact hdec ⟨le_rfl, hc.2.le⟩ ⟨hct.le, ht.2.le⟩ hct

private theorem D_change {n : ℕ} (b : Fin n → ℝ) {a m : ℝ} (hn : (0:ℝ) < n)
    (ha : 0 < a) (hm : 0 < m) (hb : ∀ i, 0 < b i) (hs : ∑ i, b i = (n:ℝ)*m) :
    D b a = m * F (fun i => m / b i - 1) (a/(a+m)) := by
  have h : ∀ i, m * component (m/b i-1) (a/(a+m)) =
      a*m/(a+m) - a*b i/(a+b i) := by
    intro i
    have H : 1 + (m / b i - 1) * (a / (a+m)) =
        m * (a+b i) / (b i * (a+m)) := by
      field_simp [(hb i).ne', (add_pos ha hm).ne']
      <;> ring
    unfold component
    rw [H]
    field_simp [(hb i).ne', hm.ne', (add_pos ha hm).ne', (add_pos ha (hb i)).ne']
    <;> ring
  unfold F D
  rw [Finset.mul_sum (a := m), Finset.sum_congr rfl (fun i _ => h i), Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hs]
  congr 1
  have hs' : (n:ℝ)*a + (n:ℝ)*m ≠ 0 := (add_pos (mul_pos hn ha) (mul_pos hn hm)).ne'
  field_simp [hs', (add_pos ha hm).ne']
  <;> ring

private theorem peak_exists_unique (n : ℕ) (hn : 0 < n) (b : Fin n → ℝ) (hb : ∀ i, 0 < b i)
    (hvar : ∃ i j, b i ≠ b j) :
    ∃! a : ℝ, 0 < a ∧ ∀ x : ℝ, 0 < x → D b x ≤ D b a := by
  let m := (∑ i, b i)/(n:ℝ)
  let k : Fin n → ℝ := fun i => m/b i-1
  have hn' : 0 < (n:ℝ) := by exact_mod_cast hn
  have hm : 0 < m := by
    obtain ⟨i, _, _⟩ := hvar
    exact div_pos (Finset.sum_pos' (fun j _ => (hb j).le) ⟨i, Finset.mem_univ _, hb i⟩) hn'
  have hs : ∑ i, b i = (n:ℝ)*m := by dsimp [m]; field_simp
  have hk : ∀ i, -1 < k i := by intro i; dsimp [k]; linarith [div_pos hm (hb i)]
  have hnon : ∃ i, k i ≠ 0 := by
    by_contra! h
    obtain ⟨i, j, hij⟩ := hvar
    apply hij
    have he (s : Fin n) : m = b s := by
      have hx := h s
      dsimp [k] at hx
      field_simp [(hb s).ne'] at hx
      linarith
    exact (he i).symm.trans (he j)
  have hend : F k 0 = F k 1 := by
    have hh (i : Fin n) : component (k i) 1 = 1-b i/m := by
      dsimp [component,k]
      field_simp [(hb i).ne', hm.ne']
      <;> ring
    simp only [F, component, mul_zero, add_zero, zero_div, sub_zero, Finset.sum_const_zero]
    change 0 = ∑ i, component (k i) 1
    rw [Finset.sum_congr rfl (fun i _ => hh i), Finset.sum_sub_distrib]
    simp only [div_eq_mul_inv, ← Finset.sum_mul, hs]
    simp [hm.ne']
  obtain ⟨c, hc, hpeak⟩ := shape k hk hnon hend
  let p := m*c/(1-c)
  have hp : 0 < p := div_pos (mul_pos hm hc.1) (sub_pos.mpr hc.2)
  have hpc : p/(p+m) = c := by
    apply (div_eq_iff (add_pos hp hm).ne').2
    dsimp [p]
    field_simp [(sub_pos.mpr hc.2).ne']
    <;> ring
  have peak (x : ℝ) (hx : 0 < x) (hxp : x ≠ p) : D b x < D b p := by
    have hxc : x/(x+m) ≠ c := by
      intro he
      apply hxp
      apply (eq_div_iff (sub_pos.mpr hc.2).ne').2
      have H := (div_eq_iff (add_pos hx hm).ne').1 he
      nlinarith
    have hxin : x/(x+m) ∈ Ioo (0:ℝ) 1 :=
      ⟨div_pos hx (add_pos hx hm), (div_lt_one (add_pos hx hm)).2 (by linarith)⟩
    rw [D_change b hn' hx hm hb hs, D_change b hn' hp hm hb hs, hpc]
    exact mul_lt_mul_of_pos_left (hpeak _ hxin hxc) hm
  refine ⟨p, ⟨hp, ?_⟩, ?_⟩
  · intro x hx
    by_cases h : x = p
    · exact h ▸ le_rfl
    · exact (peak x hx h).le
  · intro x hx
    by_contra h
    exact (not_lt_of_ge (hx.2 p hp)) (peak x hx.1 h)

end OMA.S_mo_204379

theorem OMA.solution : type_of% @OMA.S_mo_204379.main :=
  OMA.S_mo_204379.peak_exists_unique
