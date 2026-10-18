import NLS.ZakharovShabat.SourceRealGapSeparation
import NLS.ZakharovShabat.SourceGapAngularDensity

/-! # The actual exterior spectral kernel and its integrable majorant

The original gap endpoints and profiles define measurable kernel data.
For an open selected gap, neighboring gaps give a uniform separation
constant. The kernel majorant is bounded by the angular density divided
by its square, and action summability proves integrability.
-/

noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def sourceGapHalfWidthReal (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceSubmodule p) (n : ℤ) : ℝ :=
  ((canonicalPeriodicRight hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n).re-
    (canonicalPeriodicLeft hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n).re)/2

def sourceGapCenterReal (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceSubmodule p) (n : ℤ) : ℝ :=
  ((canonicalPeriodicLeft hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n).re+
    (canonicalPeriodicRight hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n).re)/2

def sourceExteriorGapPole (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceSubmodule p) (n : ℤ)
    (z : {m : ℤ // m ≠ n} × ℝ) : ℝ :=
  (realGapAffinePoint hp hp1 φ.val z.1.val (Real.cos z.2)-sourceGapCenterReal hp hp1 φ n)/
    sourceGapHalfWidthReal hp hp1 φ n

def sourceExteriorGapRoot (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceSubmodule p) (n : ℤ)
    (z : {m : ℤ // m ≠ n} × ℝ) : ℝ :=
  Real.sqrt |(realGapAffinePoint hp hp1 φ.val z.1.val (Real.cos z.2)-
      (canonicalPeriodicLeft hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n).re)*
    (realGapAffinePoint hp hp1 φ.val z.1.val (Real.cos z.2)-
      (canonicalPeriodicRight hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n).re)|

def sourceExteriorGapKernelWeight (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceSubmodule p) (n : ℤ)
    (z : {m : ℤ // m ≠ n} × ℝ) : ℝ :=
  sourceGapAngularDensity hp hp1 φ z.1.val z.2 /
    (sourceGapHalfWidthReal hp hp1 φ n*sourceExteriorGapRoot hp hp1 φ n z)

theorem sourceGapHalfWidthReal_pos (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceSubmodule p) (n : ℤ)
    (hg : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0) :
    0 < sourceGapHalfWidthReal hp hp1 φ n := by
  have h := source_openRealGap_of_realType_gap_ne_zero hp hp1 n φ.val φ.property
    (by simpa only [sourcePeriodicGapDisplacement_apply] using hg)
  unfold sourceGapHalfWidthReal
  linarith

theorem sourceExteriorGapKernelWeight_nonneg (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (n : ℤ)
    (hg : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0)
    (z : {m : ℤ // m ≠ n} × ℝ) : 0 ≤ sourceExteriorGapKernelWeight hp hp1 φ n z := by
  exact div_nonneg (sourceGapAngularDensity_nonneg hp hp1 φ z.1.val z.2)
    (mul_nonneg (sourceGapHalfWidthReal_pos hp hp1 φ n hg).le (Real.sqrt_nonneg _))

/-- Actual neighboring gaps give a uniform kernel majorant at every exterior index and angle. -/
theorem sourceExteriorGapKernel_separation (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (n : ℤ)
    (hg : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z : {m : ℤ // m ≠ n} × ℝ,
      δ ≤ sourceExteriorGapRoot hp hp1 φ n z ∧
      1+δ/sourceGapHalfWidthReal hp hp1 φ n ≤ |sourceExteriorGapPole hp hp1 φ n z| ∧
      1 < |sourceExteriorGapPole hp hp1 φ n z| ∧
      sourceExteriorGapKernelWeight hp hp1 φ n z/(|sourceExteriorGapPole hp hp1 φ n z|-1) ≤
        sourceGapAngularDensity hp hp1 φ z.1.val z.2/δ^2 := by
  obtain ⟨δ,hδ,hsep⟩ := sourceRealGaps_uniform_exterior_separation hp hp1 φ n
  refine ⟨δ,hδ,?_⟩
  intro z
  have ht := hsep z.1.val z.1.property _ (realGapAffinePoint_cos_mem_Icc hp hp1 φ z.1.val z.2)
  have hv : δ ≤ sourceExteriorGapRoot hp hp1 φ n z :=
    NLS.ComplexAnalysis.separated_gap_sqrt_lower_bound _ _ _ δ hδ.le ht.1 ht.2.1
  have hpole := NLS.ComplexAnalysis.separated_gap_normalized_pole
    (sourceGapHalfWidthReal hp hp1 φ n) (sourceGapCenterReal hp hp1 φ n) _ δ
    (sourceGapHalfWidthReal_pos hp hp1 φ n hg) hδ ht.2.2
  refine ⟨hv,hpole.1,hpole.2,?_⟩
  exact NLS.ComplexAnalysis.exterior_gap_kernel_majorant _ _ _ _ δ
    (sourceGapAngularDensity_nonneg hp hp1 φ z.1.val z.2)
    (sourceGapHalfWidthReal_pos hp hp1 φ n hg) hδ hv hpole.1

theorem measurable_sourceExteriorGapPole (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (n : ℤ) : Measurable (sourceExteriorGapPole hp hp1 φ n) := by
  apply measurable_from_prod_countable_right
  intro m
  apply Continuous.measurable
  unfold sourceExteriorGapPole realGapAffinePoint
  fun_prop

theorem measurable_sourceExteriorGapRoot (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (n : ℤ) : Measurable (sourceExteriorGapRoot hp hp1 φ n) := by
  apply measurable_from_prod_countable_right
  intro m
  apply Continuous.measurable
  unfold sourceExteriorGapRoot realGapAffinePoint
  fun_prop

theorem measurable_sourceExteriorGapKernelWeight (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (n : ℤ) : Measurable (sourceExteriorGapKernelWeight hp hp1 φ n) := by
  unfold sourceExteriorGapKernelWeight
  exact (measurable_from_prod_countable_right (fun m => measurable_sourceGapAngularDensity hp hp1 φ m.val)).div
    (measurable_const.mul (measurable_sourceExteriorGapRoot hp hp1 φ n))

/-- Summability of actual actions proves the required exterior-distance majorant integrable. -/
theorem integrable_sourceExteriorGapKernel_majorant (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (n : ℤ)
    (hg : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0)
    (ha : Summable (fun m : ℤ => ‖sourceComplexAction hp hp1 m φ.val‖)) :
    Integrable (fun z => sourceExteriorGapKernelWeight hp hp1 φ n z /
      (|sourceExteriorGapPole hp hp1 φ n z|-1)) (Measure.count.prod volume) := by
  obtain ⟨δ,hδ,hsep⟩ := sourceExteriorGapKernel_separation hp hp1 φ n hg
  have hd := (integrable_sourceGapAngularDensity_exterior_of_summable hp hp1 φ n ha).div_const (δ^2)
  apply hd.mono'
  · exact ((measurable_sourceExteriorGapKernelWeight hp hp1 φ n).div
      ((measurable_sourceExteriorGapPole hp hp1 φ n).norm.sub measurable_const)).aestronglyMeasurable
  · apply Filter.Eventually.of_forall
    intro z
    rw [Real.norm_eq_abs,abs_of_nonneg (div_nonneg (sourceExteriorGapKernelWeight_nonneg hp hp1 φ n hg z)
      (sub_pos.mpr (hsep z).2.2.1).le)]
    exact (hsep z).2.2.2

end NLS.ZakharovShabat
