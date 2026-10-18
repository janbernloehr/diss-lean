import NLS.ZakharovShabat.SourceExteriorGapKernel
import NLS.ZakharovShabat.SourcePrimitivePowerSharpCubic

/-! # A continuous positive correction built from actual gap profiles

The explicit exterior kernel integral is nonnegative and continuous when
the actual actions are summable. Equality with the original profile
remains an explicit hypothesis in the sharp cubic-moment theorem.
-/

noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The explicit positive correction candidate built from all other actual gap profiles. -/
def sourceExteriorGapCorrection (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (n : ℤ) (θ : ℝ) : ℝ :=
  ∫ z : {m : ℤ // m ≠ n} × ℝ,
    sourceExteriorGapKernelWeight hp hp1 φ n z / |sourceExteriorGapPole hp hp1 φ n z-Real.cos θ|
      ∂(Measure.count.prod volume)

theorem sourceExteriorGapCorrection_nonneg (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (n : ℤ)
    (hg : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0)
    (θ : ℝ) : 0 ≤ sourceExteriorGapCorrection hp hp1 φ n θ :=
  integral_nonneg (fun z => div_nonneg (sourceExteriorGapKernelWeight_nonneg hp hp1 φ n hg z) (abs_nonneg _))

/-- Continuity of the explicit candidate follows from the original action trace. -/
theorem continuous_sourceExteriorGapCorrection (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (n : ℤ)
    (hg : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0)
    (ha : Summable (fun m : ℤ => ‖sourceComplexAction hp hp1 m φ.val‖)) :
    Continuous (sourceExteriorGapCorrection hp hp1 φ n) := by
  obtain ⟨δ,_,hsep⟩ := sourceExteriorGapKernel_separation hp hp1 φ n hg
  exact NLS.ComplexAnalysis.continuous_integral_exterior_cosine_kernel (Measure.count.prod volume)
    (sourceExteriorGapKernelWeight hp hp1 φ n) (sourceExteriorGapPole hp hp1 φ n)
    (measurable_sourceExteriorGapKernelWeight hp hp1 φ n) (measurable_sourceExteriorGapPole hp hp1 φ n)
    (sourceExteriorGapKernelWeight_nonneg hp hp1 φ n hg) (fun z => (hsep z).2.2.1)
    (integrable_sourceExteriorGapKernel_majorant hp hp1 φ n hg ha)

namespace SourcePrimitivePowerAtlas
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
variable (A : SourcePrimitivePowerAtlas hp hp1 W)

/-- For actual summable actions, only the explicit profile identity remains to obtain the sharp bound. -/
theorem real_action_sq_le_cubic_of_actual_gap_identity
    (φ : realTypeSourceSubmodule p) (n : ℤ)
    (ha : Summable (fun m : ℤ => ‖sourceComplexAction hp hp1 m φ.val‖))
    (hrep : ∀ x ∈ Icc (0:ℝ) Real.pi,
      sourceRealGapCosineProfile hp hp1 φ.val n x =
        sourceGapHalfWidthReal hp hp1 φ n*Real.sin x*(1+sourceExteriorGapCorrection hp hp1 φ n x)) :
    (3/4:ℝ)*‖sourceComplexAction hp hp1 n φ.val‖^2 ≤ (A.moment n 3 φ.val).re := by
  by_cases hg : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n = 0
  · rw [← A.moment_one n (A.realType_subset_domain φ.property),
      A.moment_of_collapsed φ.val (A.realType_subset_domain φ.property) n hg 1,
      A.moment_of_collapsed φ.val (A.realType_subset_domain φ.property) n hg 3]
    norm_num
  obtain ⟨δ,_,hsep⟩ := sourceExteriorGapKernel_separation hp hp1 φ n hg
  apply A.real_action_sq_le_cubic_of_exterior_kernel_representation φ n
    (Measure.count.prod volume) (sourceExteriorGapKernelWeight hp hp1 φ n) (sourceExteriorGapPole hp hp1 φ n)
    (measurable_sourceExteriorGapKernelWeight hp hp1 φ n) (measurable_sourceExteriorGapPole hp hp1 φ n)
    (sourceExteriorGapKernelWeight_nonneg hp hp1 φ n hg) (fun z => (hsep z).2.2.1)
    (integrable_sourceExteriorGapKernel_majorant hp hp1 φ n hg ha)
  simpa only [sourceExteriorGapCorrection,sourceGapHalfWidthReal,canonicalPeriodicGap,Complex.sub_re] using hrep

end SourcePrimitivePowerAtlas


end NLS.ZakharovShabat
