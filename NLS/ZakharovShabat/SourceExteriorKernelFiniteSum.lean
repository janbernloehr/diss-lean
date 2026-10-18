import NLS.ZakharovShabat.SourceSharpCubicFiniteGapReduction
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-! # Finite support and real coordinates of the actual kernel

The proved majorant justifies Fubini. Finite spectral support, the angular
cutoff and the normalized-coordinate identity retain the exact kernel.
-/

noncomputable section
open Set Metric Filter Topology Complex MeasureTheory NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual exterior kernel at each selected angle is jointly integrable. -/
theorem integrable_sourceExteriorGapKernel (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (n : ℤ)
    (hg : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0)
    (ha : Summable (fun m : ℤ => ‖sourceComplexAction hp hp1 m φ.val‖)) (θ : ℝ) :
    Integrable (fun z => sourceExteriorGapKernelWeight hp hp1 φ n z /
      |sourceExteriorGapPole hp hp1 φ n z-Real.cos θ|) (Measure.count.prod volume) := by
  obtain ⟨δ,_,hsep⟩ := sourceExteriorGapKernel_separation hp hp1 φ n hg
  apply (integrable_sourceExteriorGapKernel_majorant hp hp1 φ n hg ha).mono'
  · exact ((measurable_sourceExteriorGapKernelWeight hp hp1 φ n).div
      ((measurable_sourceExteriorGapPole hp hp1 φ n).sub measurable_const).norm).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun z => NLS.ComplexAnalysis.exterior_cosine_kernel_norm_le _ _ θ
      (sourceExteriorGapKernelWeight_nonneg hp hp1 φ n hg z) (hsep z).2.2.1)

/-- Finite-gap sources reduce the actual correction to finitely many angular integrals. -/
theorem sourceExteriorGapCorrection_eq_finite_sum (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (n : ℤ)
    (hg : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0)
    (hf : φ ∈ sourceFiniteGapLocus hp hp1) (θ : ℝ) :
    sourceExteriorGapCorrection hp hp1 φ n θ =
      ∑ m ∈ hf.toFinset.subtype (fun m => m ≠ n), ∫ η : ℝ,
        sourceExteriorGapKernelWeight hp hp1 φ n (m,η)/
          |sourceExteriorGapPole hp hp1 φ n (m,η)-Real.cos θ| := by
  classical
  obtain ⟨W,_,_,⟨A⟩⟩ := exists_sourcePrimitivePowerAtlas hp hp1
  have hi := integrable_sourceExteriorGapKernel hp hp1 φ n hg (A.summable_actions_of_finiteGap φ hf) θ
  unfold sourceExteriorGapCorrection
  rw [integral_prod _ hi,integral_countable hi.integral_prod_left]
  simp only [measureReal_def,Measure.count_singleton,ENNReal.toReal_one,one_smul]
  apply tsum_eq_sum
  intro m hm
  have hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) m.val = 0 := by
    by_contra hgap
    exact hm (by simpa using hf.mem_toFinset.mpr hgap)
  simp only [sourceExteriorGapKernelWeight,sourceGapAngularDensity,hgap,Complex.zero_re,zero_div,zero_mul,integral_zero]

/-- The normalized kernel at an exterior gap is the original real-coordinate kernel. -/
theorem sourceExteriorGapKernel_eq_original (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (n : ℤ)
    (hg : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0)
    (m : {m : ℤ // m ≠ n}) (θ η : ℝ) :
    sourceExteriorGapKernelWeight hp hp1 φ n (m,η)/|sourceExteriorGapPole hp hp1 φ n (m,η)-Real.cos θ| =
      sourceGapAngularDensity hp hp1 φ m.val η /
        (sourceExteriorGapRoot hp hp1 φ n (m,η) *
          |realGapAffinePoint hp hp1 φ.val m.val (Real.cos η)-realGapAffinePoint hp hp1 φ.val n (Real.cos θ)|) := by
  have he := NLS.ComplexAnalysis.normalized_exterior_kernel_eq
    (sourceGapAngularDensity hp hp1 φ m.val η) (sourceGapHalfWidthReal hp hp1 φ n)
    (sourceExteriorGapRoot hp hp1 φ n (m,η))
    (realGapAffinePoint hp hp1 φ.val m.val (Real.cos η)) (sourceGapCenterReal hp hp1 φ n)
    (Real.cos θ) (sourceGapHalfWidthReal_pos hp hp1 φ n hg)
  simpa only [sourceExteriorGapKernelWeight,sourceExteriorGapPole,sourceGapHalfWidthReal,
    sourceGapCenterReal,realGapAffinePoint] using he

/-- The angular cutoff turns the full-line kernel integral into its exact cosine interval integral. -/
theorem integral_sourceExteriorGapKernel_eq_interval (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (n : ℤ)
    (hg : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0)
    (m : {m : ℤ // m ≠ n}) (θ : ℝ) :
    (∫ η : ℝ, sourceExteriorGapKernelWeight hp hp1 φ n (m,η)/
        |sourceExteriorGapPole hp hp1 φ n (m,η)-Real.cos θ|) =
      ∫ η in (0:ℝ)..Real.pi,
        (sourceGapHalfWidthReal hp hp1 φ m.val/Real.pi * Real.sin η *
          sourceRealGapCosineProfile hp hp1 φ.val m.val η) /
        (sourceExteriorGapRoot hp hp1 φ n (m,η) *
          |realGapAffinePoint hp hp1 φ.val m.val (Real.cos η)-realGapAffinePoint hp hp1 φ.val n (Real.cos θ)|) := by
  let f : ℝ → ℝ := fun η =>
    (sourceGapHalfWidthReal hp hp1 φ m.val/Real.pi * Real.sin η * sourceRealGapCosineProfile hp hp1 φ.val m.val η) /
      (sourceExteriorGapRoot hp hp1 φ n (m,η) *
        |realGapAffinePoint hp hp1 φ.val m.val (Real.cos η)-realGapAffinePoint hp hp1 φ.val n (Real.cos θ)|)
  have he : (fun η => sourceExteriorGapKernelWeight hp hp1 φ n (m,η)/
      |sourceExteriorGapPole hp hp1 φ n (m,η)-Real.cos θ|) = (Icc (0:ℝ) Real.pi).indicator f := by
    funext η
    rw [sourceExteriorGapKernel_eq_original hp hp1 φ n hg m θ η]
    by_cases hη : η ∈ Icc (0:ℝ) Real.pi
    · simp only [sourceGapAngularDensity,indicator_of_mem hη]
      dsimp only [f,sourceGapHalfWidthReal,canonicalPeriodicGap]
      simp only [Complex.sub_re]
      ring
    · simp only [sourceGapAngularDensity,indicator_of_notMem hη,mul_zero,zero_div]
  rw [he,integral_indicator measurableSet_Icc,integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le Real.pi_pos.le]

end NLS.ZakharovShabat
