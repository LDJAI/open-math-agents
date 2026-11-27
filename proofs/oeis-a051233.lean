import OMAStatements.S_oeis_a051233
import Mathlib.Analysis.Convex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
A pixel is represented by the square [-1,1]² around its center. Convexity
allows us to certify inscribed trapezoids by checking only the four vertices.
-/
open Set MeasureTheory MeasureTheory.Measure
open OMA.S_oeis_a051233

namespace OMA.HalfPixel

lemma covered_closed (r a b : ℝ) : IsClosed (covered r a b) :=
  (isClosed_Icc.prod isClosed_Icc).inter (isClosed_le (by fun_prop) continuous_const)

lemma square_mix (s t x y : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t = 1) :
    (s*x + t*y)^2 ≤ s*x^2 + t*y^2 := by
  have e : s*x^2 + t*y^2 - (s*x + t*y)^2 = s*t*(x-y)^2 := by
    linear_combination (-s*x^2-t*y^2) * hst
  nlinarith only [e, mul_nonneg (mul_nonneg hs ht) (sq_nonneg (x-y))]

lemma covered_convex (r a b : ℝ) : Convex ℝ (covered r a b) := by
  apply ((convex_Icc (-1 : ℝ) 1).prod (convex_Icc (-1 : ℝ) 1)).inter
  intro p hp q hq s t hs ht hst
  change (a + p.1)^2 + (b + p.2)^2 ≤ r^2 at hp
  change (a + q.1)^2 + (b + q.2)^2 ≤ r^2 at hq
  change (a + (s*p.1+t*q.1))^2 + (b + (s*p.2+t*q.2))^2 ≤ r^2
  have A : a + (s*p.1+t*q.1) = s*(a+p.1)+t*(a+q.1) := by linear_combination -a*hst
  have B : b + (s*p.2+t*q.2) = s*(b+p.2)+t*(b+q.2) := by linear_combination -b*hst
  rw [A,B]
  nlinarith only [square_mix s t (a+p.1) (a+q.1) hs ht hst,
    square_mix s t (b+p.2) (b+q.2) hs ht hst, mul_nonneg hs (sub_nonneg.mpr hp),
    mul_nonneg ht (sub_nonneg.mpr hq), congrArg (fun z : ℝ => z*r^2) hst]

lemma neg_real : MeasurePreserving Neg.neg (volume : Measure ℝ) volume := by
  refine ⟨measurable_neg, ?_⟩
  simpa only [abs_neg, abs_one, ENNReal.ofReal_one, one_smul, neg_one_mul] using
    (Real.smul_map_volume_mul_left (a := -1) (by norm_num))

/-- A width-one trapezoid including its sloping upper edge. -/
def trap (s l u v : ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 ∈ Ioo s (s+1) ∧ l < p.2 ∧ p.2 ≤ u+(v-u)*(p.1-s)}

lemma trap_meas (s l u v : ℝ) : MeasurableSet (trap s l u v) :=
  (measurable_fst measurableSet_Ioo).inter
    ((measurableSet_lt measurable_const measurable_snd).inter (measurableSet_le measurable_snd (by fun_prop)))

/-- A trapezoid and its half-turn cover a rectangle of twice the claimed area. -/
lemma trap_volume (s l u v : ℝ) (hu : l ≤ u) (hv : l ≤ v) :
    ENNReal.ofReal ((u+v)/2-l) ≤ volume (trap s l u v) := by
  let f := Prod.map (fun x : ℝ => (2*s+1)-x) (fun y : ℝ => (u+v)-y)
  have refl (k : ℝ) : MeasurePreserving (fun x : ℝ => k-x) volume volume := by
    simpa only [Function.comp_def, sub_eq_add_neg] using
      (measurePreserving_add_left (volume : Measure ℝ) k).comp neg_real
  have hf : MeasurePreserving f (volume : Measure (ℝ × ℝ)) volume :=
    (refl (2*s+1)).prod (refl (u+v))
  have sub : Ioo s (s+1) ×ˢ Ioo l (u+v-l) ⊆ trap s l u v ∪ (f ⁻¹' trap s l u v) := by
    rintro ⟨x,y⟩ ⟨⟨hx,hx'⟩,hy,hy'⟩
    by_cases h : y ≤ u+(v-u)*(x-s)
    · exact Or.inl ⟨⟨hx,hx'⟩,hy,h⟩
    · right
      change (2*s+1-x ∈ Ioo s (s+1)) ∧ l < u+v-y ∧ u+v-y ≤ u+(v-u)*(2*s+1-x-s)
      exact ⟨⟨by linarith,by linarith⟩,by linarith,by nlinarith⟩
  have h := (measure_mono sub (μ := (volume : Measure (ℝ × ℝ)))).trans (measure_union_le _ _)
  rw [hf.measure_preimage (trap_meas ..).nullMeasurableSet] at h
  change (volume.prod volume) _ ≤ _ at h
  rw [Measure.prod_prod, Real.volume_Ioo, Real.volume_Ioo] at h
  have width : s+1-s=1 := by ring
  rw [width, ENNReal.ofReal_one, one_mul] at h
  have he : u+v-l-l = ((u+v)/2-l)+((u+v)/2-l) := by ring
  rw [he, ENNReal.ofReal_add (by linarith) (by linarith)] at h
  by_contra! bad
  have hlt := ENNReal.add_lt_add_left (ENNReal.ofReal_ne_top (r := (u+v)/2-l)) bad
  exact (not_lt_of_ge h) ((add_le_add bad.le (le_refl _)).trans_lt hlt)

lemma trap_subset {C : Set (ℝ × ℝ)} (hc : Convex ℝ C) (s l u v : ℝ)
    (bl : (s,l) ∈ C) (br : (s+1,l) ∈ C) (tl : (s,u) ∈ C) (tr : (s+1,v) ∈ C) :
    trap s l u v ⊆ C := by
  rintro ⟨x,y⟩ ⟨⟨hxl,hxr⟩,hyl,hyu⟩
  change y ≤ u+(v-u)*(x-s) at hyu
  let k := x-s
  have hk : 0 ≤ k := by dsimp [k]; linarith
  have hk' : 0 ≤ 1-k := by dsimp [k]; linarith
  have hbot : (x,l) ∈ C := by
    convert hc bl br hk' hk (by ring : (1-k)+k=1) using 1
    ext <;> simp [k] <;> ring
  have htop : (x,u+(v-u)*k) ∈ C := by
    convert hc tl tr hk' hk (by ring : (1-k)+k=1) using 1
    ext <;> simp [k] <;> ring
  let z := u+(v-u)*k
  have hyz : y ≤ z := hyu
  have hpos : 0 < z-l := by linarith
  let m := (y-l)/(z-l)
  have hm : 0 ≤ m := div_nonneg (by linarith) hpos.le
  have hm' : 0 ≤ 1-m := by
    have h : m ≤ 1 := (div_le_one hpos).mpr (by linarith)
    linarith
  have hv' : (1-m)*l + m*z = y := by
    dsimp [m]; field_simp [hpos.ne']; ring
  change (x,z) ∈ C at htop
  convert hc hbot htop hm' hm (by ring : (1-m)+m=1) using 1
  ext <;> simp only [Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd, smul_eq_mul]
  · ring
  · exact hv'.symm

lemma covered_mem {r a b x y : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1)
    (hy : y ∈ Icc (-1 : ℝ) 1) (hgap : a^2+b^2+1 ≤ r^2)
    (h : x^2+y^2+2*a*x+2*b*y ≤ 1) : (x,y) ∈ covered r a b :=
  ⟨⟨hx,hy⟩, by change (a+x)^2+(b+y)^2 ≤ r^2; nlinarith⟩

end OMA.HalfPixel


open Set MeasureTheory MeasureTheory.Measure
open OMA.S_oeis_a051233

namespace OMA.HalfPixel

/-- Place the larger offset on the vertical axis. At horizontal coordinates
-1, 0, 1 use upper heights u, c, -v and lower height -1. All six
vertices belong to the disk: for each height magnitude t we use t² ≤ t.
The combined area exceeds or equals 2 because
2c + u - v = 2(2b-1-2a)/((2b-1)(2b+1)). -/
lemma inside_off_diagonal (r a b : ℝ) (ha : 0 ≤ a) (hab : a+1 ≤ b)
    (hgap : a^2+b^2+1 ≤ r^2) : 2 ≤ volume (covered r a b) := by
  let c := 1/(2*b+1)
  let u := 2*a/(2*b+1)
  let v := 2*a/(2*b-1)
  have hp : 0 < 2*b+1 := by linarith
  have hm : 0 < 2*b-1 := by linarith
  have hc : c ∈ Icc (0:ℝ) 1 :=
    ⟨div_nonneg (by norm_num) hp.le, (div_le_one hp).2 (by linarith)⟩
  have hu : u ∈ Icc (0:ℝ) 1 :=
    ⟨div_nonneg (by linarith) hp.le, (div_le_one hp).2 (by linarith)⟩
  have hv : v ∈ Icc (0:ℝ) 1 :=
    ⟨div_nonneg (by linarith) hm.le, (div_le_one hm).2 (by linarith)⟩
  have ec : c*(2*b+1) = 1 := div_mul_cancel₀ _ hp.ne'
  have eu : u*(2*b+1) = 2*a := div_mul_cancel₀ _ hp.ne'
  have ev : v*(2*b-1) = 2*a := div_mul_cancel₀ _ hm.ne'
  have hleft : ((-1:ℝ),(-1:ℝ)) ∈ covered r a b :=
    covered_mem (by norm_num) (by norm_num) hgap (by nlinarith)
  have hmid : ((0:ℝ),(-1:ℝ)) ∈ covered r a b :=
    covered_mem (by norm_num) (by norm_num) hgap (by nlinarith)
  have hright : ((1:ℝ),(-1:ℝ)) ∈ covered r a b :=
    covered_mem (by norm_num) (by norm_num) hgap (by nlinarith)
  have hlu : ((-1:ℝ),u) ∈ covered r a b :=
    covered_mem (by norm_num) ⟨by linarith [hu.1],hu.2⟩ hgap
      (by nlinarith only [eu, mul_nonneg hu.1 (sub_nonneg.mpr hu.2)])
  have hmc : ((0:ℝ),c) ∈ covered r a b :=
    covered_mem (by norm_num) ⟨by linarith [hc.1],hc.2⟩ hgap
      (by nlinarith only [ec, mul_nonneg hc.1 (sub_nonneg.mpr hc.2)])
  have hrv : ((1:ℝ),-v) ∈ covered r a b :=
    covered_mem (by norm_num) ⟨by linarith [hv.2],by linarith [hv.1]⟩ hgap
      (by nlinarith only [ev, mul_nonneg hv.1 (sub_nonneg.mpr hv.2)])
  have L := trap_subset (covered_convex r a b) (-1) (-1) u c hleft
    (by simpa using hmid) hlu (by simpa using hmc)
  have R := trap_subset (covered_convex r a b) 0 (-1) c (-v) hmid
    (by simpa using hright) hmc (by simpa using hrv)
  have dis : Disjoint (trap (-1) (-1) u c) (trap 0 (-1) c (-v)) := by
    refine Set.disjoint_left.mpr ?_
    intro z hz hw
    have h₁ := hz.1.2
    have h₂ := hw.1.1
    linarith
  have tot : 0 ≤ 2*c+u-v := by
    dsimp [c,u,v]
    field_simp [hp.ne',hm.ne']
    nlinarith
  have vol := measure_mono (Set.union_subset L R) (μ := (volume : Measure (ℝ × ℝ)))
  rw [measure_union dis (trap_meas ..)] at vol
  have lower := add_le_add
    (trap_volume (-1) (-1) u c (by linarith [hu.1]) (by linarith [hc.1]))
    (trap_volume 0 (-1) c (-v) (by linarith [hc.1]) (by linarith [hv.2]))
  apply le_trans _ (lower.trans vol)
  rw [← ENNReal.ofReal_add (by linarith [hu.1,hc.1]) (by linarith [hc.1,hv.2])]
  simpa only [ENNReal.ofReal_ofNat] using
    (ENNReal.ofReal_le_ofReal (show (2:ℝ) ≤ (u+c)/2-(-1)+((c+ -v)/2-(-1)) by linarith))

lemma swap_covered (r a b : ℝ) :
    Prod.swap ⁻¹' covered r a b = covered r b a := by
  ext ⟨x,y⟩
  change ((y ∈ Icc (-1:ℝ) 1 ∧ x ∈ Icc (-1:ℝ) 1) ∧ (a+y)^2+(b+x)^2 ≤ r^2) ↔
    ((x ∈ Icc (-1:ℝ) 1 ∧ y ∈ Icc (-1:ℝ) 1) ∧ (b+x)^2+(a+y)^2 ≤ r^2)
  constructor <;> rintro ⟨⟨h₁,h₂⟩,h⟩ <;> exact ⟨⟨h₂,h₁⟩,by simpa [add_comm] using h⟩

lemma volume_swap (r a b : ℝ) :
    volume (covered r a b) = volume (covered r b a) := by
  rw [← swap_covered r a b]
  exact (measurePreserving_swap.measure_preimage (covered_closed _ _ _).measurableSet.nullMeasurableSet).symm

/-- On the diagonal each mixed-sign quadrant contributes at least one half,
and the negative quadrant contributes one. -/
lemma inside_diagonal (r a : ℝ) (ha : 1 ≤ a) (hgap : a^2+a^2+1 ≤ r^2) :
    2 ≤ volume (covered r a a) := by
  let c := 1/(2*a+1)
  let u := 2*a/(2*a+1)
  have hp : 0 < 2*a+1 := by linarith
  have hc : c ∈ Icc (0:ℝ) 1 :=
    ⟨div_nonneg (by norm_num) hp.le, (div_le_one hp).2 (by linarith)⟩
  have hu : u ∈ Icc (0:ℝ) 1 :=
    ⟨div_nonneg (by linarith) hp.le, (div_le_one hp).2 (by linarith)⟩
  have ec : c*(2*a+1) = 1 := div_mul_cancel₀ _ hp.ne'
  have eu : u*(2*a+1) = 2*a := div_mul_cancel₀ _ hp.ne'
  have sum : u+c = 1 := by dsimp [u,c]; field_simp
  have N : trap (-1) (-1) 0 0 ⊆ covered r a a := by
    apply trap_subset (covered_convex r a a)
    all_goals apply covered_mem (by norm_num) (by norm_num) hgap; nlinarith
  have T : trap (-1) 0 u c ⊆ covered r a a := by
    apply trap_subset (covered_convex r a a)
    · apply covered_mem (by norm_num) (by norm_num) hgap; nlinarith
    · apply covered_mem (by norm_num) (by norm_num) hgap; nlinarith
    · exact covered_mem (by norm_num) ⟨by linarith [hu.1],hu.2⟩ hgap
        (by nlinarith only [eu, mul_nonneg hu.1 (sub_nonneg.mpr hu.2)])
    · exact covered_mem (by norm_num) ⟨by linarith [hc.1],hc.2⟩ hgap
        (by nlinarith only [ec, mul_nonneg hc.1 (sub_nonneg.mpr hc.2)])
  let U := Prod.swap ⁻¹' trap (-1) 0 u c
  have Usub : U ⊆ covered r a a := by
    rw [← swap_covered r a a]
    exact Set.preimage_mono T
  have Umeas : MeasurableSet U := (trap_meas ..).preimage measurable_swap
  have Uvol : volume U = volume (trap (-1) 0 u c) :=
    measurePreserving_swap.measure_preimage (trap_meas ..).nullMeasurableSet
  have nt : Disjoint (trap (-1) (-1) 0 0) (trap (-1) 0 u c) := by
    apply Set.disjoint_left.mpr
    intro z hz hw
    have h₁ := hz.2.2
    have h₂ := hw.2.1
    linarith
  have nu : Disjoint (trap (-1) (-1) 0 0 ∪ trap (-1) 0 u c) U := by
    apply Set.disjoint_left.mpr
    intro z hz hw
    have h₂ : 0 < z.1 := hw.2.1
    rcases hz with hz | hz <;> linarith [hz.1.2]
  have vol := measure_mono (Set.union_subset (Set.union_subset N T) Usub)
    (μ := (volume : Measure (ℝ × ℝ)))
  rw [measure_union nu Umeas, measure_union nt (trap_meas ..), Uvol] at vol
  have hn := trap_volume (-1) (-1) 0 0 (by norm_num) (by norm_num)
  have ht := trap_volume (-1) 0 u c hu.1 hc.1
  have low := (add_le_add (add_le_add hn ht) ht).trans vol
  rw [sum] at low
  norm_num at low
  rw [add_assoc, ← ENNReal.ofReal_add (by norm_num) (by norm_num)] at low
  norm_num at low
  exact low

lemma inside_origin (r : ℝ) (hr : 1 ≤ r^2) : 2 ≤ volume (covered r 0 0) := by
  let d := Real.sqrt (1/2)
  have hd : 0 ≤ d := Real.sqrt_nonneg _
  have he : d^2 = 1/2 := Real.sq_sqrt (by norm_num)
  have hd1 : d ≤ 1 := by nlinarith
  have sub : Icc (-d) d ×ˢ Icc (-d) d ⊆ covered r 0 0 := by
    rintro ⟨x,y⟩ ⟨⟨hxl,hxr⟩,hyl,hyr⟩
    refine ⟨⟨⟨by linarith,by linarith⟩,⟨by linarith,by linarith⟩⟩,?_⟩
    change (0+x)^2+(0+y)^2 ≤ r^2
    nlinarith only [mul_nonneg (sub_nonneg.mpr hxr) (sub_nonneg.mpr hxl),
      mul_nonneg (sub_nonneg.mpr hyr) (sub_nonneg.mpr hyl), he,hr]
  apply le_trans _ (measure_mono sub)
  change _ ≤ (volume.prod volume) _
  rw [Measure.prod_prod, Real.volume_Icc, ← ENNReal.ofReal_mul (by linarith)]
  have h' : (d - -d)*(d - -d) = 2 := by nlinarith
  rw [h']; norm_num

end OMA.HalfPixel


open Set MeasureTheory MeasureTheory.Measure
open OMA.S_oeis_a051233

namespace OMA.HalfPixel

lemma volume_neg_first (r a b : ℝ) :
    volume (covered r (-a) b) = volume (covered r a b) := by
  let f := Prod.map (fun x : ℝ => -x) (id : ℝ → ℝ)
  have hf : MeasurePreserving f (volume : Measure (ℝ × ℝ)) volume :=
    neg_real.prod (MeasurePreserving.id _)
  have pre : f ⁻¹' covered r a b = covered r (-a) b := by
    ext p
    change (((-1 ≤ -p.1 ∧ -p.1 ≤ 1) ∧ _) ∧ (a + -p.1)^2+_ ≤ _) ↔
      (((-1 ≤ p.1 ∧ p.1 ≤ 1) ∧ _) ∧ (-a+p.1)^2+_ ≤ _)
    have A : (a + -p.1)^2 = (-a+p.1)^2 := by ring
    rw [A]
    constructor <;> rintro ⟨⟨⟨h₁,h₂⟩,h₃⟩,h₄⟩ <;> exact ⟨⟨⟨by linarith,by linarith⟩,h₃⟩,h₄⟩
  rw [← pre]
  exact hf.measure_preimage (covered_closed ..).measurableSet.nullMeasurableSet

/-- If the center is outside, the covered patch and its central reflection
are disjoint. Their complement contains an open neighborhood of the center. -/
lemma outside (r a b : ℝ) (hout : r^2 < a^2+b^2) :
    volume (covered r a b) < 2 := by
  let C := covered r a b
  let D := (fun p : ℝ × ℝ => -p) ⁻¹' C
  let B : Set (ℝ × ℝ) := Icc (-1) 1 ×ˢ Icc (-1) 1
  let O : Set (ℝ × ℝ) := (Ioo (-1) 1 ×ˢ Ioo (-1) 1) \ (C ∪ D)
  have hc : IsClosed C := covered_closed .. 
  have hd : IsClosed D := hc.preimage continuous_neg
  have hO : IsOpen O := (isOpen_Ioo.prod isOpen_Ioo).sdiff (hc.union hd)
  have hn : O.Nonempty := by
    refine ⟨(0,0), ⟨by norm_num, ?_⟩⟩
    rintro (h|h)
    · have h' := h.2
      change (a+0)^2+(b+0)^2 ≤ r^2 at h'
      simp only [add_zero] at h'; linarith
    · have h' := h.2
      change (a+ -0)^2+(b+ -0)^2 ≤ r^2 at h'
      simp only [neg_zero,add_zero] at h'; linarith
  have sep : Disjoint C D := by
    apply Set.disjoint_left.mpr
    intro p h₁ h₂
    have e₁ := h₁.2
    have e₂ := h₂.2
    change (a+p.1)^2+(b+p.2)^2 ≤ r^2 at e₁
    change (a+ -p.1)^2+(b+ -p.2)^2 ≤ r^2 at e₂
    nlinarith [sq_nonneg p.1, sq_nonneg p.2]
  have sC : C ⊆ B := fun _ h => h.1
  have sD : D ⊆ B := by
    intro p h
    obtain ⟨h₁,h₂⟩ := h.1
    change -1 ≤ -p.1 ∧ -p.1 ≤ 1 at h₁
    change -1 ≤ -p.2 ∧ -p.2 ≤ 1 at h₂
    exact ⟨⟨by linarith [h₁.2],by linarith [h₁.1]⟩,⟨by linarith [h₂.2],by linarith [h₂.1]⟩⟩
  have sO : O ⊆ B := fun _ h => ⟨⟨h.1.1.1.le,h.1.1.2.le⟩,⟨h.1.2.1.le,h.1.2.2.le⟩⟩
  have disO : Disjoint (C ∪ D) O := Set.disjoint_left.mpr (fun _ h k => k.2 h)
  have hneg : MeasurePreserving (fun p : ℝ × ℝ => -p) volume volume := neg_real.prod neg_real
  have dv : volume D = volume C := hneg.measure_preimage hc.measurableSet.nullMeasurableSet
  have bv : volume B = 4 := by
    change (volume.prod volume) _ = _
    rw [Measure.prod_prod, Real.volume_Icc]
    norm_num
  have h := measure_mono (Set.union_subset (Set.union_subset sC sD) sO) (μ := (volume : Measure (ℝ × ℝ)))
  rw [measure_union disO hO.measurableSet, measure_union sep hd.measurableSet, dv, bv] at h
  by_contra! bad
  change 2 ≤ volume C at bad
  have four : (4 : ENNReal) ≤ volume C + volume C := by
    calc (4 : ENNReal) = 2+2 := by norm_num
         _ ≤ _ := add_le_add bad bad
  have more := ENNReal.add_lt_add_left (by norm_num : (4:ENNReal) ≠ ⊤) (hO.measure_pos volume hn)
  rw [add_zero] at more
  exact (not_lt_of_ge h) (lt_of_lt_of_le more (add_le_add four (le_refl _)))

end OMA.HalfPixel


open Set MeasureTheory MeasureTheory.Measure Filter
open OMA.S_oeis_a051233

namespace OMA.HalfPixel

/-- The disk boundary never passes through a pixel center. For odd n the
doubled offsets are even. For even n both offsets are odd, and their squared
sum is 2 modulo 4. -/
lemma no_boundary (n i j : ℕ) :
    (offset n i)^2 + (offset n j)^2 ≠ (n:ℤ)^2 := by
  intro h
  rcases Int.even_or_odd (n:ℤ) with ⟨k,hk⟩ | ⟨k,hk⟩ <;>
    simp only [offset,hk] at h <;> ring_nf at h <;> omega

lemma volume_abs (r a b : ℝ) :
    volume (covered r |a| |b|) = volume (covered r a b) := by
  have fst (x y : ℝ) : volume (covered r |x| y) = volume (covered r x y) := by
    rcases le_or_gt 0 x with hx | hx
    · rw [abs_of_nonneg hx]
    · rw [abs_of_neg hx,volume_neg_first]
  calc
    volume (covered r |a| |b|) = volume (covered r a |b|) := fst .. 
    _ = volume (covered r |b| a) := volume_swap ..
    _ = volume (covered r b a) := fst ..
    _ = volume (covered r a b) := volume_swap ..

lemma inside_sorted (r : ℝ) (A B : ℤ) (ha : 0 ≤ A) (hab : A ≤ B)
    (hgap : (A:ℝ)^2+(B:ℝ)^2+1 ≤ r^2) :
    2 ≤ volume (covered r A B) := by
  rcases eq_or_lt_of_le hab with h|h
  · subst B
    rcases eq_or_lt_of_le ha with h|h
    · subst A
      simp only [Int.cast_zero] at hgap ⊢
      exact inside_origin r (by linarith only [hgap])
    · exact inside_diagonal r A (by exact_mod_cast (show (1:ℤ) ≤ A by omega)) hgap
  · exact inside_off_diagonal r A B (by exact_mod_cast ha)
      (by exact_mod_cast (show A+1 ≤ B by omega)) hgap

lemma pixel_iff (n i j : ℕ) :
    2 ≤ volume (covered n (offset n i) (offset n j)) ↔
      (offset n i)^2 + (offset n j)^2 < (n:ℤ)^2 := by
  let a := offset n i
  let b := offset n j
  change 2 ≤ volume (covered n a b) ↔ a^2+b^2 < (n:ℤ)^2
  constructor
  · intro h
    by_contra! hf
    have hs : (n:ℤ)^2 < a^2+b^2 :=
      lt_of_le_of_ne hf (Ne.symm (no_boundary n i j))
    exact (outside n a b (by exact_mod_cast hs)).not_ge h
  · intro h
    have hg : a^2+b^2+1 ≤ (n:ℤ)^2 := by omega
    have habs : (|a|:ℤ)^2+(|b|:ℤ)^2+1 ≤ (n:ℤ)^2 := by simpa using hg
    rw [← volume_abs, ← Int.cast_abs, ← Int.cast_abs]
    rcases le_total |a| |b| with hs|hs
    · exact inside_sorted n |a| |b| (abs_nonneg _) hs (by exact_mod_cast habs)
    · rw [volume_swap]
      apply inside_sorted n |b| |a| (abs_nonneg _) hs
      have hg' : (|b|:ℤ)^2+(|a|:ℤ)^2+1 ≤ (n:ℤ)^2 := by linarith only [habs]
      exact_mod_cast hg'

/-- In fact all grid sizes give exactly the same count. -/
theorem counts_equal (n : ℕ) : halfCount n = centerCount n := by
  classical
  unfold halfCount centerCount
  congr 1
  apply Finset.filter_congr
  intro p _
  exact pixel_iff n p.1 p.2

end OMA.HalfPixel

theorem OMA.solution : type_of% @OMA.S_oeis_a051233.main := by
  constructor
  · intro n _
    exact (OMA.HalfPixel.counts_equal n).le
  · simpa only [OMA.HalfPixel.counts_equal, ne_self_iff_false, Finset.filter_false,
      Finset.card_empty, Nat.cast_zero, zero_div] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (nhds 0))

