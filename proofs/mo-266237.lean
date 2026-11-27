import OMAStatements.S_mo_266237
import Mathlib.Algebra.MvPolynomial.Coeff
namespace OMA.ChanceCluster

open Finset OMA.S_mo_266237

/-- The coefficient of a monomial in a power of a sum counts labeled words
with the prescribed multiplicities. The domain may be any finite type. -/
lemma card_counts {A : Type*} [Fintype A] [DecidableEq A] {K : ℕ} (c : Fin K → ℕ)
    (hc : ∑ j, c j = Fintype.card A) :
    (univ.filter fun f : A → Fin K => counts f = c).card = Nat.multinomial univ c := by
  classical
  let deg : (Fin K → ℕ) → (Fin K →₀ ℕ) := Finsupp.equivFunOnFinite.symm
  have exponent (f : A → Fin K) :
      (∑ x, Finsupp.single (f x) (1 : ℕ)) = deg (counts f) := by
    ext j
    simp [deg, Finsupp.finsetSum_apply, Finsupp.single_apply, counts, Finset.sum_boole]
  have term (f : A → Fin K) :
      (∏ x, (MvPolynomial.X (f x) : MvPolynomial (Fin K) ℕ)) =
        MvPolynomial.monomial (deg (counts f)) 1 := by
    rw [← exponent, MvPolynomial.monomial_sum_one]
    rfl
  have expansion :
      ((∑ j : Fin K, MvPolynomial.X j : MvPolynomial (Fin K) ℕ) ^ Fintype.card A) =
        ∑ f : A → Fin K, MvPolynomial.monomial (deg (counts f)) 1 := by
    calc
      _ = ∏ _x : A, (∑ j : Fin K, MvPolynomial.X j : MvPolynomial (Fin K) ℕ) := by simp
      _ = ∑ f : A → Fin K, ∏ x, MvPolynomial.X (f x) := Fintype.prod_sum _
      _ = _ := Finset.sum_congr rfl fun f _ => term f
  have total : (deg c).sum (fun _ n => n) = Fintype.card A := by
    rw [Finsupp.sum_of_support_subset _ (Finset.subset_univ _) _ (by simp)]
    exact hc
  have h := MvPolynomial.coeff_sum_X_pow_of_fintype (R := ℕ) (deg c) (Fintype.card A)
  rw [expansion, MvPolynomial.coeff_sum, if_pos total,
    Finsupp.multinomial_eq_of_support_subset (Finset.subset_univ _)] at h
  simpa [MvPolynomial.coeff_monomial, deg, Finset.sum_boole] using h

/-- The rows are the label counts on the fibers of the reference assignment. -/
def overlap {N K : ℕ} (τ f : Fin N → Fin K) (i : Fin K) : Fin K → ℕ :=
  counts fun x : {x // τ x = i} => f x.1

lemma counts_total {A : Type*} [Fintype A] {K : ℕ} (f : A → Fin K) :
    ∑ j, counts f j = Fintype.card A := by
  classical
  simpa [counts] using (Finset.sum_card_fiberwise_eq_card_filter
    (Finset.univ : Finset A) (Finset.univ : Finset (Fin K)) f)

lemma row_total {N K : ℕ} (τ f : Fin N → Fin K) (i : Fin K) :
    ∑ j, overlap τ f i j = counts τ i := by
  rw [overlap, counts_total, Fintype.card_subtype]
  rfl

lemma col_total {N K : ℕ} (τ f : Fin N → Fin K) (j : Fin K) :
    ∑ i, overlap τ f i j = counts f j := by
  classical
  simpa only [overlap, counts, Finset.sum_boole, Nat.cast_id] using
    (Fintype.sum_fiberwise τ (fun x => if f x = j then (1 : ℕ) else 0))

set_option maxHeartbeats 1200000 in
lemma cost_overlap {N K : ℕ} (τ f : Fin N → Fin K) :
    tableDistance (overlap τ f) = distance f τ := by
  classical
  unfold tableDistance distance
  apply Finset.inf'_congr univ_nonempty rfl
  intro p _
  calc
    _ = ∑ i, ∑ x : {x // τ x = i}, (if f x.1 = p (τ x.1) then 0 else 1 : ℕ) := by
      apply Finset.sum_congr rfl
      intro i _
      calc
        _ = ∑ x : {x // τ x = i}, (if f x.1 = p i then 0 else 1 : ℕ) := by
          simpa [overlap, counts, mul_ite] using
            (Finset.sum_fiberwise' univ (fun x : {x // τ x = i} => f x.1)
              (fun j => if j = p i then (0 : ℕ) else 1))
        _ = _ := Finset.sum_congr rfl fun x _ => by rw [x.property]
    _ = ∑ x, if f x = p (τ x) then (0 : ℕ) else 1 :=
      Fintype.sum_fiberwise τ (fun x => if f x = p (τ x) then (0 : ℕ) else 1)
    _ = _ := by
      have indicator (x : Fin N) : (if f x = p (τ x) then (0 : ℕ) else 1) =
          (if f x ≠ p (τ x) then 1 else 0) := by by_cases h : f x = p (τ x) <;> simp [h]
      simp only [indicator, Finset.sum_boole, Nat.cast_id]

/-- Restricting an assignment independently to each reference class turns a
fiber of the overlap table into a Cartesian product of multinomial fibers. -/
lemma card_overlap {N K : ℕ} (τ : Fin N → Fin K) (t : Fin K → Fin K → ℕ)
    (hr : ∀ i, ∑ j, t i j = counts τ i) :
    (univ.filter fun f => overlap τ f = t).card = weight t := by
  classical
  let e : (Fin N → Fin K) ≃ ((i : Fin K) → {x // τ x = i} → Fin K) :=
    Equiv.piCongrFiberwise (f := τ) fun _ => Equiv.refl _
  let choices (i : Fin K) : Finset ({x // τ x = i} → Fin K) :=
    univ.filter fun g => counts g = t i
  have bij : (univ.filter fun f => overlap τ f = t).card = (Fintype.piFinset choices).card := by
    apply Finset.card_equiv e
    intro f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset, choices]
    exact funext_iff
  rw [bij, Fintype.card_piFinset]
  apply Finset.prod_congr rfl
  intro i _
  apply card_counts (A := {x // τ x = i}) (t i)
  rw [Fintype.card_subtype]
  exact hr i

lemma mem_tables {K m : ℕ} (t : Fin K → Fin K → ℕ) :
    t ∈ tables K m ↔ (∀ i, ∑ j, t i j = m) ∧ (∀ j, ∑ i, t i j = m) := by
  classical
  simp [tables, Fintype.mem_piFinset, Finset.mem_piAntidiag]

end OMA.ChanceCluster

open Finset OMA.S_mo_266237 OMA.ChanceCluster

theorem OMA.solution : type_of% @OMA.S_mo_266237.main := by
  classical
  intro N K m _hK hN τ hτ d
  have refCounts : counts τ = fun _ => m := (Finset.mem_filter.mp hτ).2
  let target := (tables K m).filter fun t => tableDistance t = d
  have events : ((balanced N K m).filter fun f => distance f τ = d) =
      univ.filter (fun f => overlap τ f ∈ target) := by
    ext f
    simp [balanced, target, mem_tables, row_total, col_total, refCounts, cost_overlap, funext_iff]
  have numerator : ((balanced N K m).filter fun f => distance f τ = d).card =
      ∑ t ∈ target, weight t := by
    rw [events, ← Finset.sum_card_fiberwise_eq_card_filter univ target (overlap τ)]
    apply Finset.sum_congr rfl
    intro t ht
    apply card_overlap
    intro i
    rw [refCounts]
    exact ((mem_tables t).mp (Finset.mem_filter.mp ht).1).1 i
  have denominator : (balanced N K m).card = Nat.multinomial univ (fun _ : Fin K => m) := by
    apply card_counts (A := Fin N) (fun _ : Fin K => m)
    simpa using hN.symm
  rw [numerator, denominator]
