import NLS.KdV.HillRoughAbelianGardner

/-! # Actual rough Gardner canonicality on arbitrary open domains

Original complete physical germs fix the bracket. Actual physical
mean-zero rough density extends it to EVERY real mean-zero rough source.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ComplexConjugate ENNReal
namespace NLS.KdV

private theorem cartesian_eq_sqrt_two_mul_original_raw
    (p : RealPeriodOneHillPotential) (σ : Bool) (n : ℕ+) :
    hillSignedSpectralCartesian σ n p=(Real.sqrt 2 : ℂ)*
      hillAbelianRawCoordinateSequence SpectralWeight.one (hillUnitRealSourceUnembed p)
        (if σ then (n : ℤ) else -(n : ℤ)) := by
  cases σ
  · simp only [hillSignedSpectralCartesian,Bool.false_eq_true,if_false,
      hillAbelianRawCoordinateSequence_original_neg]
    rw [hillSpectralCartesian_eq_sqrt_two_mul_abelian,map_mul,conj_ofReal]
  · simp only [hillSignedSpectralCartesian,if_true,hillAbelianRawCoordinateSequence_original_nat]
    exact hillSpectralCartesian_eq_sqrt_two_mul_abelian p n n.pos

private theorem physical_rough_abelian_Gardner_on
    (Z : PeriodOneHminusOne → WeightedCoeff (Weight.sobolev (-1/2)) 2)
    (U : Set PeriodOneHminusOne) (hU : IsOpen U) (hZa : AnalyticOnNhd ℂ Z U)
    (hZp : ∀ p : RealPeriodOneHillPotential,
      (hillPhysicalHminusEmbedding p).val∈U → ∀ j : ℤ,
      (Z (hillPhysicalHminusEmbedding p).val).val j=
        hillAbelianRawCoordinateSequence SpectralWeight.one (hillUnitRealSourceUnembed p) j)
    (p : RealPeriodOneHillPotential) (hmean : p.val.val 0=0)
    (hp : hillOriginalHminusSource p.val∈U)
    (σ τ : Bool) (n m : ℕ+) :
    NLS.Poisson.hminusGardnerBracket (hillRoughSignedAbelianComponent Z σ n)
      (hillRoughSignedAbelianComponent Z τ m) (hillOriginalHminusSource p.val)=
        hillOriginalComplexGardnerMatrixEntry σ τ n m/2 := by
  let c : ℂ := Real.sqrt 2
  let F := hillRoughSignedAbelianComponent Z σ n
  let G := hillRoughSignedAbelianComponent Z τ m
  have hFa := hillRoughSignedAbelianComponent_analytic Z hZa σ n
  have hGa := hillRoughSignedAbelianComponent_analytic Z hZa τ m
  have hsource : Continuous (fun q : RealPeriodOneHillPotential => hillOriginalHminusSource q.val) :=
    hillOriginalHminusSource.continuous.comp continuous_subtype_val
  have hnear := hsource.continuousAt.eventually (hU.mem_nhds hp)
  have hmatch (ρ : Bool) (k : ℕ+) : ∀ᶠ q : RealPeriodOneHillPotential in 𝓝 p,
      c*hillRoughSignedAbelianComponent Z ρ k (hillOriginalHminusSource q.val)=hillSignedSpectralCartesian ρ k q := by
    filter_upwards [hnear] with q hq
    unfold hillRoughSignedAbelianComponent
    rw [hillOriginalHminusSource_eq_physical,
      hZp q (show (hillPhysicalHminusEmbedding q).val ∈ U from hq)]
    exact (cartesian_eq_sqrt_two_mul_original_raw q ρ k).symm
  have hCF := (hFa _ hp).differentiableAt.hasFDerivAt.const_mul c
  have hCG := (hGa _ hp).differentiableAt.hasFDerivAt.const_mul c
  have hh := hillSignedCartesians_hminus_Gardner_original_matrix p hmean n m σ τ
    (fun q => c*F q) (fun q => c*G q)
    (analyticAt_const.mul (hFa _ hp)) (analyticAt_const.mul (hGa _ hp)) (hmatch σ n) (hmatch τ m)
  rw [NLS.Poisson.hminusGardnerBracket_of_fderiv_smul_left _ F _ _ c hCF.fderiv,
    NLS.Poisson.hminusGardnerBracket_of_fderiv_smul_right F _ G _ c hCG.fderiv] at hh
  have hc : c*c=(2 : ℂ) := by
    change (Real.sqrt 2 : ℂ)*(Real.sqrt 2 : ℂ)=2
    rw [← pow_two,← ofReal_pow,Real.sq_sqrt (by norm_num)]
    norm_num
  have htwo : (2 : ℂ)*NLS.Poisson.hminusGardnerBracket F G (hillOriginalHminusSource p.val)=
      hillOriginalComplexGardnerMatrixEntry σ τ n m := by
    calc
      _ = c*(c*NLS.Poisson.hminusGardnerBracket F G (hillOriginalHminusSource p.val)) := by rw [← mul_assoc,hc]
      _ = _ := hh
  apply (eq_div_iff (by norm_num : (2 : ℂ)≠0)).mpr
  linear_combination htwo

/-- Full original canonical matrix on EVERY real mean-zero rough point
of ANY open actual physical extension domain. No zero-centered ball is required. -/
theorem hillRoughAbelian_Gardner_matrix_on_real_domain
    (Z : PeriodOneHminusOne → WeightedCoeff (Weight.sobolev (-1/2)) 2)
    (U : Set PeriodOneHminusOne) (hU : IsOpen U) (hZa : AnalyticOnNhd ℂ Z U)
    (hZp : ∀ p : RealPeriodOneHillPotential,
      (hillPhysicalHminusEmbedding p).val∈U → ∀ j : ℤ,
      (Z (hillPhysicalHminusEmbedding p).val).val j=
        hillAbelianRawCoordinateSequence SpectralWeight.one (hillUnitRealSourceUnembed p) j)
    (q : PeriodOneHminusOne) (hq : q∈U)
    (hreal : IsRealPeriodOneHminusOne q) (hmean : q.val 0=0) (σ τ : Bool) (n m : ℕ+) :
    NLS.Poisson.hminusGardnerBracket (hillRoughSignedAbelianComponent Z σ n)
      (hillRoughSignedAbelianComponent Z τ m) q=hillOriginalComplexGardnerMatrixEntry σ τ n m/2 := by
  have hB := NLS.Poisson.analyticOnNhd_hminusGardnerBracket _ _
    (hillRoughSignedAbelianComponent_analytic Z hZa σ n) (hillRoughSignedAbelianComponent_analytic Z hZa τ m)
  exact eq_on_real_meanZero_of_original_physical hU _ _ hB.continuousOn continuousOn_const
    (fun p hp hpball => physical_rough_abelian_Gardner_on Z U hU hZa hZp p hp hpball σ τ n m)
    q hq hreal hmean


end NLS.KdV
