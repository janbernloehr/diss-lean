import NLS.ZakharovShabat.SourceOmittedBoundaryAnalytic
import NLS.ZakharovShabat.SourceDeletedPeriodicBoundaryError
import NLS.ComplexAnalysis.UnitSquareRootComparison

/-! # The signed omitted-product normalization on complex sources

Connectedness propagates the real-source sign and gives inverse-index errors for the omitted root product and its inverse.
-/

noncomputable section
open Set Complex Metric NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The actual omitted standard-root product and its inverse have the
signed free normalization with locally uniform inverse-index errors on
complex neighborhoods of every real original Hs source, for s >= 1. -/
theorem exists_local_higherSobolev_omitted_boundary_error_bound
    (s : ℕ) (hs : 1 ≤ s) (a₀ : realTypeHigherSobolevSourceLocus s) (θ : BoundaryCondition) :
    ∃ U : Set (SobolevSource s), IsOpen U ∧ a₀.val ∈ U ∧
      ∃ K : ℕ, 0 < K ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ ab ∈ U,
      ∀ n : ℤ, K ≤ n.natAbs →
        let P := sourceStandardRootOmittedProduct (by norm_num) (by norm_num) n
          (higherSobolevSourceInclusion s ab)
          (canonicalPeriodOneBoundaryRoots (by norm_num) (by norm_num) θ
            (higherSobolevSourceInclusion s ab) n)
        ‖P-(-1:ℂ)^n.natAbs‖ ≤ C/(1+|(n:ℝ)|) ∧
        ‖P⁻¹-(-1:ℂ)^n.natAbs‖ ≤ 2*C/(1+|(n:ℝ)|) := by
  obtain ⟨V,hV,haV,K₀,hK₀,C,hC,herror⟩ :=
    exists_local_higherSobolev_deleted_product_boundary_error_bound s hs a₀ θ
  let J := higherSobolevSourceInclusion s
  obtain ⟨W,hW,haW,hdata⟩ := exists_local_source_omitted_boundary_analytic
    (by norm_num) (by norm_num) (J a₀.val) a₀.property
  have hopen : IsOpen (V ∩ J ⁻¹' W) := hV.inter (hW.preimage J.continuous)
  obtain ⟨r,hr,hrsub⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds ⟨haV,haW⟩)
  let U := ball a₀.val r
  have haU : a₀.val ∈ U := mem_ball_self hr
  obtain ⟨L,hL⟩ := exists_nat_gt (2*C)
  let K := max K₀ L
  refine ⟨U,isOpen_ball,haU,K,hK₀.trans_le (le_max_left _ _),C,hC,?_⟩
  intro ab hab n hn
  let P (x : SobolevSource s) := sourceStandardRootOmittedProduct (by norm_num) (by norm_num) n
    (J x) (canonicalPeriodOneBoundaryRoots (by norm_num) (by norm_num) θ (J x) n)
  let sign : ℂ := (-1:ℂ)^n.natAbs
  let f (x : SobolevSource s) := sign*P x
  let q : ℝ := 1+|(n:ℝ)|
  have hq : 0 < q := by dsimp [q]; positivity
  have hsign : sign^2 = 1 := by
    dsimp only [sign]
    rw [← pow_mul,mul_comm n.natAbs 2,pow_mul]
    norm_num
  have hsignnorm : ‖sign‖ = 1 := by simp [sign]
  have hsq (x : SobolevSource s) : (f x)^2 = (P x)^2 := by
    dsimp only [f]
    rw [mul_pow,hsign,one_mul]
  have hsmall : C/q < 1/2 := by
    apply (div_lt_iff₀ hq).mpr
    have hnL : (L:ℝ) ≤ (n.natAbs:ℝ) := by exact_mod_cast (le_max_right K₀ L).trans hn
    have habs : |(n:ℝ)| = (n.natAbs:ℝ) := by simp
    dsimp only [q]
    rw [habs]
    linarith
  have hsqbound (x : SobolevSource s) (hx : x ∈ U) : ‖(f x)^2-1‖ ≤ C/q := by
    rw [hsq,sourceStandardRootOmittedProduct_sq_eq_canonicalDeletedPeriodicProduct
      (by norm_num) (by norm_num) (J x) n _ (hdata (J x) (hrsub hx).2 θ n).1]
    exact herror x (hrsub hx).1 n ((le_max_left _ _).trans hn)
  have hf : ContinuousOn f U := by
    intro x hx
    have haP := (hdata (J x) (hrsub hx).2 θ n).2.1.comp (J.analyticAt x)
    exact (continuousAt_const.mul haP.continuousAt).continuousWithinAt
  have hfpos : 0 < (f a₀.val).re := by
    have hsgn := (sourceStandardRootOmittedProduct_boundary_sign (by norm_num) (by norm_num)
      θ (J a₀.val) a₀.property n).2
    have he : sign = Complex.ofReal ((-1:ℝ)^n.natAbs) := by simp [sign]
    change 0 < (sign*P a₀.val).re
    rw [he,mul_re,ofReal_re,ofReal_im,zero_mul,sub_zero]
    exact hsgn
  have hroot := norm_sub_one_le_sq_sub_one_on_preconnected
    (convex_ball a₀.val r).isPreconnected f hf a₀.val haU hfpos
    (fun x hx => (hsqbound x hx).trans_lt (hsmall.trans (by norm_num))) ab hab
  have he : sign*(f ab-1) = P ab-sign := by
    dsimp only [f]
    linear_combination P ab*hsign
  have hnorm : ‖P ab-sign‖ = ‖f ab-1‖ := by
    rw [← he,norm_mul,hsignnorm,one_mul]
  have hbound : ‖P ab-sign‖ ≤ C/q := hnorm.le.trans (hroot.trans (hsqbound ab hab))
  refine ⟨hbound,?_⟩
  have hinv := norm_inv_sub_inv_le_of_unit_near (P ab) sign hsignnorm (hbound.trans hsmall.le)
  have hsiginv : sign⁻¹ = sign := by simp [sign,← inv_pow]
  rw [hsiginv] at hinv
  exact hinv.trans ((mul_le_mul_of_nonneg_left hbound (by norm_num)).trans_eq (by ring))

end NLS.ZakharovShabat
