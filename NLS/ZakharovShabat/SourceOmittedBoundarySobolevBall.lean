import NLS.ZakharovShabat.SourceDeletedPeriodicBoundarySobolevBall
import NLS.ZakharovShabat.SourceOmittedBoundaryInverseAnalytic

/-! # Uniform omitted-product normalization and inverse error

Real-source normalization and compact finite heads bound the complete inverse-product error in the order-one weighted supremum norm.
-/

noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The signed inverse omitted-product error as an original L2 coordinate. -/
def sourceBoundaryOmittedInverseL2Error (θ : BoundaryCondition) (n : ℤ) (φ : CoeffPair 2) : ℂ :=
  (sourceStandardRootOmittedProduct (by norm_num) (by norm_num) n φ
    (canonicalPeriodOneBoundaryRoots (by norm_num) (by norm_num) θ φ n))⁻¹-(-1:ℂ)^n.natAbs

theorem continuousAt_sourceBoundaryOmittedInverseL2Error_of_real
    (φ : realTypeSourceLocus 2) (θ : BoundaryCondition) (n : ℤ) :
    ContinuousAt (sourceBoundaryOmittedInverseL2Error θ n) φ.val := by
  obtain ⟨U,_,hφU,hdata⟩ := exists_local_source_omitted_boundary_analytic
    (by norm_num) (by norm_num) φ.val φ.property
  have hd := (hdata φ.val hφU θ n).2
  exact (hd.1.continuousAt.inv₀ hd.2).sub continuousAt_const

/-- The real-source sign fixes the omitted product uniformly on every
real Sobolev ball, with inverse-index bounds for the product and its inverse. -/
theorem exists_uniform_real_higherSobolev_omitted_boundary_error_bound
    (s : ℕ) (hs : 1 ≤ s) (R : ℝ) (hR : 0 ≤ R) :
    ∃ K : ℕ, 0 < K ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ ab : realTypeHigherSobolevSourceLocus s, ‖ab.val‖ ≤ R → ∀ θ : BoundaryCondition,
      ∀ n : ℤ, K ≤ n.natAbs →
      let P := sourceStandardRootOmittedProduct (by norm_num) (by norm_num) n
        (higherSobolevSourceInclusion s ab.val)
        (canonicalPeriodOneBoundaryRoots (by norm_num) (by norm_num) θ
          (higherSobolevSourceInclusion s ab.val) n)
      ‖P-(-1:ℂ)^n.natAbs‖ ≤ C/(1+|(n:ℝ)|) ∧
      ‖P⁻¹-(-1:ℂ)^n.natAbs‖ ≤ 2*C/(1+|(n:ℝ)|) := by
  obtain ⟨K₀,hK₀,C,hC,herror⟩ := exists_uniform_real_higherSobolev_deleted_product_boundary_error_bound s hs R hR
  obtain ⟨L,hL⟩ := exists_nat_gt (2*C)
  refine ⟨max K₀ L,hK₀.trans_le (le_max_left _ _),C,hC,?_⟩
  intro ab hab θ n hn
  let φ := higherSobolevSourceInclusion s ab.val
  let P := sourceStandardRootOmittedProduct (by norm_num) (by norm_num) n φ
    (canonicalPeriodOneBoundaryRoots (by norm_num) (by norm_num) θ φ n)
  let sign : ℂ := (-1:ℂ)^n.natAbs
  let q : ℝ := 1+|(n:ℝ)|
  have hq : 0 < q := by dsimp [q]; positivity
  have hsign : sign^2 = 1 := by
    dsimp only [sign]
    rw [← pow_mul,mul_comm n.natAbs 2,pow_mul]
    norm_num
  have hsignnorm : ‖sign‖ = 1 := by simp [sign]
  obtain ⟨U,_,hφU,hdata⟩ := exists_local_source_omitted_boundary_analytic
    (by norm_num) (by norm_num) φ ab.property
  have hsq : ‖(sign*P)^2-1‖ ≤ C/q := by
    rw [mul_pow,hsign,one_mul]
    rw [sourceStandardRootOmittedProduct_sq_eq_canonicalDeletedPeriodicProduct
      (by norm_num) (by norm_num) φ n _ (hdata φ hφU θ n).1]
    exact herror ab hab θ n ((le_max_left _ _).trans hn)
  have hpos : 0 < (sign*P).re := by
    have hsgn := (sourceStandardRootOmittedProduct_boundary_sign (by norm_num) (by norm_num)
      θ φ ab.property n).2
    have he : sign = Complex.ofReal ((-1:ℝ)^n.natAbs) := by simp [sign]
    rw [he,mul_re,ofReal_re,ofReal_im,zero_mul,sub_zero]
    exact hsgn
  have he : sign*(sign*P-1) = P-sign := by linear_combination P*hsign
  have hbound : ‖P-sign‖ ≤ C/q := by
    rw [← he,norm_mul,hsignnorm,one_mul]
    exact (norm_sub_one_le_sq_sub_one_of_re_nonneg (sign*P) hpos.le).trans hsq
  have hsmall : C/q ≤ 1/2 := by
    apply (div_le_iff₀ hq).mpr
    have hnL : (L:ℝ) ≤ (n.natAbs:ℝ) := by exact_mod_cast (le_max_right K₀ L).trans hn
    have habs : |(n:ℝ)| = (n.natAbs:ℝ) := by simp
    dsimp only [q]
    rw [habs]
    linarith
  refine ⟨hbound,?_⟩
  have hinv := norm_inv_sub_inv_le_of_unit_near P sign hsignnorm (hbound.trans hsmall)
  have hsiginv : sign⁻¹ = sign := by simp [sign,← inv_pow]
  rw [hsiginv] at hinv
  exact hinv.trans ((mul_le_mul_of_nonneg_left hbound (by norm_num)).trans_eq (by ring))

/-- The complete inverse omitted-product error is bounded in the order-one
weighted supremum norm on each entire real original Hs ball. -/
theorem exists_uniform_real_sourceBoundaryOmittedInverseRemainder_bound
    (s : ℕ) (hs : 1 ≤ s) (R : ℝ) (hR : 0 ≤ R) (θ : BoundaryCondition) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ ab : realTypeHigherSobolevSourceLocus s, ‖ab.val‖ ≤ R →
      ‖sourceBoundaryOmittedInverseRemainder s θ ab.val‖ ≤ B ∧
      ∀ n, (sourceBoundaryOmittedInverseRemainder s θ ab.val).val n =
        sourceBoundaryOmittedInverseError s θ n ab.val := by
  classical
  obtain ⟨N,_,C,hC,hbound⟩ := exists_uniform_real_higherSobolev_omitted_boundary_error_bound s hs R hR
  let J := higherSobolevSourceInclusion s
  let X := closedBall (0 : SobolevSource s) R ∩ (J ⁻¹' realTypeSourceLocus 2)
  let K := closure (J '' X)
  obtain ⟨hK,hKreal⟩ := higherSobolev_real_ball_image_compact s hs R
  let H (φ : CoeffPair 2) : WeightedCoeff (Weight.sobolev 1) ⊤ := WeightedCoeff.finiteBlock
    (Weight.sobolev 1) (Coeff.lowFrequencies N) (fun n => sourceBoundaryOmittedInverseL2Error θ n φ)
  have hH : ContinuousOn H K := by
    intro φ hφ
    exact (WeightedCoeff.continuousAt_finiteBlock _ _ _ φ
      (fun n _ => continuousAt_sourceBoundaryOmittedInverseL2Error_of_real ⟨φ,hKreal hφ⟩ θ n)).continuousWithinAt
  obtain ⟨B,hB⟩ := hK.exists_bound_of_continuousOn hH
  refine ⟨2*C+max B 0,by positivity,?_⟩
  intro ab hab
  have hmem : J ab.val ∈ K := subset_closure ⟨ab.val,
    ⟨by simpa only [mem_closedBall,dist_zero_right] using hab,ab.property⟩,rfl⟩
  let g (n : ℤ) := if N ≤ n.natAbs then sourceBoundaryOmittedInverseError s θ n ab.val else 0
  have hg (n : ℤ) : ‖((Weight.sobolev 1) n:ℂ)*g n‖ ≤ 2*C := by
    by_cases hn : N ≤ n.natAbs
    · have he := (hbound ab hab θ n hn).2
      have hq : 0 < 1+|(n:ℝ)| := by positivity
      have h := (le_div_iff₀ hq).mp he
      simpa only [g,if_pos hn,norm_mul,Complex.norm_real,Real.norm_eq_abs,
        abs_of_pos ((Weight.sobolev 1).positive n),Weight.sobolev_apply,Real.rpow_one,abs_of_pos hq,
        sourceBoundaryOmittedInverseError,mul_comm] using h
    · simp only [g,if_neg hn,mul_zero,norm_zero]
      positivity
  let e : WeightedCoeff (Weight.sobolev 1) ⊤ :=
    ⟨g,memℓp_infty ⟨2*C,by rintro _ ⟨n,rfl⟩; exact hg n⟩⟩
  have hen : ‖e‖ ≤ 2*C := by
    change ‖WeightedCoeff.weightEquiv (Weight.sobolev 1) ⊤ e‖ ≤ 2*C
    exact lp.norm_le_of_forall_le (by positivity) hg
  have hval (n : ℤ) : (e+H (J ab.val)).val n = sourceBoundaryOmittedInverseError s θ n ab.val := by
    change g n+(H (J ab.val)).val n = _
    dsimp only [H]
    rw [WeightedCoeff.finiteBlock_val]
    simp only [g,Coeff.mem_lowFrequencies,J,
      sourceBoundaryOmittedInverseL2Error,sourceBoundaryOmittedInverseError]
    by_cases hn : N ≤ n.natAbs
    · simp only [if_pos hn,if_neg (not_lt_of_ge hn),add_zero]
    · simp only [if_neg hn,if_pos (Nat.lt_of_not_ge hn),zero_add]
  have heq : sourceBoundaryOmittedInverseRemainder s θ ab.val = e+H (J ab.val) := by
    apply WeightedCoeff.ofFunctionOrZero_eq_of_coordinates
    exact hval
  rw [heq]
  exact ⟨(norm_add_le _ _).trans (add_le_add hen ((hB (J ab.val) hmem).trans (le_max_left _ _))),hval⟩

end NLS.ZakharovShabat
