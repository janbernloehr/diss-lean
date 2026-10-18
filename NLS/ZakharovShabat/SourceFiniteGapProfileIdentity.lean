import NLS.ZakharovShabat.SourceFiniteGapQuotientCauchy
import NLS.ZakharovShabat.SourceExteriorContourKernel

/-! # The actual finite-gap profile representation

Combining the Cauchy formula with the exact contour-kernel identities
proves that the filled quotient is one plus the constructed correction.
The real cosine profile identity includes both selected endpoints.
-/

noncomputable section
open Set Metric Filter Topology Complex MeasureTheory NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
variable (C : SourceFullAbelianUniformCauchyFamily hp hp1 W)

/-- The actual finite-gap quotient equals one plus the explicit positive exterior correction. -/
theorem filledGapQuotient_eq_one_add_correction_finiteGap (n : ℤ)
    (φ : realTypeSourceSubmodule p) (hφ : φ.val ∈ ball C.discs.source.val C.discs.sourceRadius)
    (hf : φ ∈ sourceFiniteGapLocus hp hp1)
    (hg : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0)
    (θ : ℝ) :
    C.filledGapQuotient n φ.val (sourceCanonicalRootGapPoint hp hp1 φ.val n (Real.cos θ)) =
      1+(sourceExteriorGapCorrection hp hp1 φ n θ:ℂ) := by
  classical
  let x := sourceCanonicalRootGapPoint hp hp1 φ.val n (Real.cos θ)
  have hx : x ∈ Metric.ball (C.discs.center n) (C.discs.outer n) :=
    C.segment_subset_outer n φ.val hφ (sourceCanonicalRootGapPoint_mem_segment hp hp1 φ.val n
      (Real.cos θ) (Real.neg_one_le_cos θ) (Real.cos_le_one θ))
  let k : {m : ℤ // m ≠ n} → ℝ := fun m => ∫ η : ℝ,
    sourceExteriorGapKernelWeight hp hp1 φ n (m,η)/|sourceExteriorGapPole hp hp1 φ n (m,η)-Real.cos θ|
  have hsum : (∑ m ∈ hf.toFinset.erase n, ∮ z in C(C.discs.center m,C.discs.inner m),
      C.filledGapQuotient n φ.val z/(z-x)) =
      -(2*(Real.pi:ℂ)*I)*((∑ m ∈ hf.toFinset.subtype (fun m => m ≠ n), k m : ℝ):ℂ) := by
    rw [Complex.ofReal_sum,Finset.mul_sum]
    apply Finset.sum_bij (fun m hm => (⟨m,(Finset.mem_erase.mp hm).1⟩ : {m : ℤ // m ≠ n}))
    · intro m hm
      simpa using (Finset.mem_erase.mp hm).2
    · intro m hm j hj he
      exact congrArg Subtype.val he
    · intro m hm
      refine ⟨m.val,Finset.mem_erase.mpr ⟨m.property,?_⟩,rfl⟩
      simpa using hm
    · intro m hm
      exact C.filledGapQuotient_exterior_circle_eq_kernel n m (Finset.mem_erase.mp hm).1 φ hφ
        (hf.mem_toFinset.mp (Finset.mem_erase.mp hm).2) hg θ (C.discs.inner m) le_rfl (C.discs.inner_lt m)
  have he := C.filledGapQuotient_eq_one_sub_finite_contours n φ hφ hf x hx
  rw [hsum] at he
  have hk : (∑ m ∈ hf.toFinset.subtype (fun m => m ≠ n), k m) = sourceExteriorGapCorrection hp hp1 φ n θ :=
    (sourceExteriorGapCorrection_eq_finite_sum hp hp1 φ n hg hf θ).symm
  rw [hk] at he
  have hc : 2*(Real.pi:ℂ)*I ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num)
    (by exact_mod_cast Real.pi_ne_zero)) I_ne_zero
  apply (mul_left_inj' hc).mp
  linear_combination he

/-- The actual open-gap cosine profile has the positive exterior representation at every finite-gap source. -/
theorem real_profile_eq_actual_correction_finiteGap (n : ℤ)
    (φ : realTypeSourceSubmodule p) (hφ : φ.val ∈ ball C.discs.source.val C.discs.sourceRadius)
    (hf : φ ∈ sourceFiniteGapLocus hp hp1)
    (hg : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0)
    (θ : ℝ) (hθ : θ ∈ Icc (0:ℝ) Real.pi) :
    sourceRealGapCosineProfile hp hp1 φ.val n θ =
      sourceGapHalfWidthReal hp hp1 φ n*Real.sin θ*(1+sourceExteriorGapCorrection hp hp1 φ n θ) := by
  rw [C.real_profile_eq_filledGapQuotient n φ hφ hg θ hθ,
    C.filledGapQuotient_eq_one_add_correction_finiteGap n φ hφ hf hg θ]
  simp only [add_re,one_re,ofReal_re]

end NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily
