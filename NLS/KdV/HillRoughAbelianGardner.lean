import NLS.KdV.HillOriginalAllGapCartesianMatrix
import NLS.KdV.HillAbelianCartesianNormalization
import NLS.KdV.HillPhysicalMeanZeroRoughDensity
import NLS.Poisson.HminusGardnerAlgebra
import NLS.SequenceSpaces.WeightedSourceSignedCompletion
import NLS.SequenceSpaces.DeletedRealConjugation

/-! # Canonicality of an actual rough Abelian extension

The original complete physical germs fix the genuine H-minus-one Gardner
matrix. Density then extends it to every real mean-zero rough source in the
common ball, including closed gaps and zero Dirichlet sheets. Analytic real-form
uniqueness then extends the matrix to the entire complex mean-zero ball. The Abelian
sqrt(action) normalization has mixed complex bracket i, with its sign fixed.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ComplexConjugate
open scoped ENNReal
namespace NLS.KdV

/-- The actual positive and negative raw components, without reweighting. -/
def hillRoughSignedAbelianComponent
    (Z : PeriodOneHminusOne → WeightedCoeff (Weight.sobolev (-1/2)) 2)
    (σ : Bool) (n : ℕ+) (q : PeriodOneHminusOne) : ℂ :=
  (Z q).val (if σ then (n : ℤ) else -(n : ℤ))

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

theorem hillRoughSignedAbelianComponent_analytic
    (Z : PeriodOneHminusOne → WeightedCoeff (Weight.sobolev (-1/2)) 2)
    {U : Set PeriodOneHminusOne} (hZa : AnalyticOnNhd ℂ Z U) (σ : Bool) (n : ℕ+) :
    AnalyticOnNhd ℂ (hillRoughSignedAbelianComponent Z σ n) U := by
  intro q hq
  exact ((WeightedCoeff.evalCLM (Weight.sobolev (-1/2)) 2
    (if σ then (n : ℤ) else -(n : ℤ))).analyticAt _).comp (hZa q hq)

private theorem physical_rough_abelian_Gardner
    (Z : PeriodOneHminusOne → WeightedCoeff (Weight.sobolev (-1/2)) 2)
    (η : ℝ) (hZa : AnalyticOnNhd ℂ Z (ball (0 : PeriodOneHminusOne) η))
    (hZp : ∀ p : RealPeriodOneHillPotential,
      (hillPhysicalHminusEmbedding p).val∈ball (0 : PeriodOneHminusOne) η → ∀ j : ℤ,
      (Z (hillPhysicalHminusEmbedding p).val).val j=
        hillAbelianRawCoordinateSequence SpectralWeight.one (hillUnitRealSourceUnembed p) j)
    (p : RealPeriodOneHillPotential) (hmean : p.val.val 0=0)
    (hp : hillOriginalHminusSource p.val∈ball (0 : PeriodOneHminusOne) η)
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
  have hnear := hsource.continuousAt.eventually (isOpen_ball.mem_nhds hp)
  have hmatch (ρ : Bool) (k : ℕ+) : ∀ᶠ q : RealPeriodOneHillPotential in 𝓝 p,
      c*hillRoughSignedAbelianComponent Z ρ k (hillOriginalHminusSource q.val)=hillSignedSpectralCartesian ρ k q := by
    filter_upwards [hnear] with q hq
    unfold hillRoughSignedAbelianComponent
    rw [hillOriginalHminusSource_eq_physical,
      hZp q (by simpa only [mem_ball,hillOriginalHminusSource_eq_physical] using hq)]
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

/-- Full original canonical matrix on the entire real mean-zero rough ball. -/
theorem hillRoughAbelian_Gardner_matrix_on_real_ball
    (Z : PeriodOneHminusOne → WeightedCoeff (Weight.sobolev (-1/2)) 2)
    (η : ℝ) (hZa : AnalyticOnNhd ℂ Z (ball (0 : PeriodOneHminusOne) η))
    (hZp : ∀ p : RealPeriodOneHillPotential,
      (hillPhysicalHminusEmbedding p).val∈ball (0 : PeriodOneHminusOne) η → ∀ j : ℤ,
      (Z (hillPhysicalHminusEmbedding p).val).val j=
        hillAbelianRawCoordinateSequence SpectralWeight.one (hillUnitRealSourceUnembed p) j)
    (q : PeriodOneHminusOne) (hq : q∈ball (0 : PeriodOneHminusOne) η)
    (hreal : IsRealPeriodOneHminusOne q) (hmean : q.val 0=0) (σ τ : Bool) (n m : ℕ+) :
    NLS.Poisson.hminusGardnerBracket (hillRoughSignedAbelianComponent Z σ n)
      (hillRoughSignedAbelianComponent Z τ m) q=hillOriginalComplexGardnerMatrixEntry σ τ n m/2 := by
  have hB := NLS.Poisson.analyticOnNhd_hminusGardnerBracket _ _
    (hillRoughSignedAbelianComponent_analytic Z hZa σ n) (hillRoughSignedAbelianComponent_analytic Z hZa τ m)
  exact eq_on_real_meanZero_of_original_physical isOpen_ball _ _ hB.continuousOn continuousOn_const
    (fun p hp hpball => physical_rough_abelian_Gardner Z η hZa hZp p hp hpball σ τ n m)
    q hq hreal hmean

/-- Analytic real-form uniqueness gives the same canonical matrix on the
ENTIRE complex mean-zero rough ball, with no reality hypothesis. -/
theorem hillRoughAbelian_Gardner_matrix_on_complex_ball
    (Z : PeriodOneHminusOne → WeightedCoeff (Weight.sobolev (-1/2)) 2)
    (η : ℝ) (hη : 0<η) (hZa : AnalyticOnNhd ℂ Z (ball (0 : PeriodOneHminusOne) η))
    (hZp : ∀ p : RealPeriodOneHillPotential,
      (hillPhysicalHminusEmbedding p).val∈ball (0 : PeriodOneHminusOne) η → ∀ j : ℤ,
      (Z (hillPhysicalHminusEmbedding p).val).val j=
        hillAbelianRawCoordinateSequence SpectralWeight.one (hillUnitRealSourceUnembed p) j)
    (q : PeriodOneHminusOne) (hq : q∈ball (0 : PeriodOneHminusOne) η) (hmean : q.val 0=0)
    (σ τ : Bool) (n m : ℕ+) :
    NLS.Poisson.hminusGardnerBracket (hillRoughSignedAbelianComponent Z σ n)
      (hillRoughSignedAbelianComponent Z τ m) q=hillOriginalComplexGardnerMatrixEntry σ τ n m/2 := by
  let v := Weight.sobolev (-1)
  let I := WeightedCoeff.weightIsometry v 2
  let D := Coeff.deleteCoordinate (p := 2) 0
  let Q := I.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp D
  have hDnorm (u : Coeff 2) : ‖D u‖≤‖u‖ := by
    apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞)≠0)
    intro j
    by_cases hj : j=0
    · subst j
      simp only [D,Coeff.deleteCoordinate_apply_same,norm_zero,norm_nonneg]
    · rw [Coeff.deleteCoordinate_apply_other 0 j hj]
  have hQball (u : Coeff 2) (hu : u∈ball 0 η) : Q u∈ball (0 : PeriodOneHminusOne) η := by
    apply mem_ball_zero_iff.mpr
    change ‖I.symm (D u)‖<η
    rw [LinearIsometryEquiv.norm_map]
    exact (hDnorm u).trans_lt (mem_ball_zero_iff.mp hu)
  let B := NLS.Poisson.hminusGardnerBracket (hillRoughSignedAbelianComponent Z σ n)
    (hillRoughSignedAbelianComponent Z τ m)
  have hBa := NLS.Poisson.analyticOnNhd_hminusGardnerBracket _ _
    (hillRoughSignedAbelianComponent_analytic Z hZa σ n) (hillRoughSignedAbelianComponent_analytic Z hZa τ m)
  have ha : AnalyticOnNhd ℂ (fun u : Coeff 2 => B (Q u)) (ball (0 : Coeff 2) η) :=
    fun u hu => (hBa _ (hQball u hu)).comp (f := Q) (Q.analyticAt u)
  have he := periodOneL2_real_form_identity isOpen_ball isPreconnected_ball (mem_ball_self hη)
    (fun u : Coeff 2 => B (Q u)) (fun _ => hillOriginalComplexGardnerMatrixEntry σ τ n m/2)
    ha analyticOnNhd_const (by
      intro u hu hJu
      have hDu : periodOneL2Conjugation (D u)=D u := by
        have hh := congrArg (fun a : DeletedCoeff 2 0 => a.val) (deleteCoordinateTo_conjugation u)
        rw [hJu] at hh
        exact hh.symm
      have hQr : IsRealPeriodOneHminusOne (Q u) := by
        apply (WeightedCoeff.weightIsometry_fixed_iff_raw v (Weight.sobolev_neg (-1)) (Q u)).mp
        change periodOneL2Conjugation (I (I.symm (D u)))=I (I.symm (D u))
        simpa only [LinearIsometryEquiv.apply_symm_apply] using hDu
      have hQm : (Q u).val 0=0 := by
        change (D u) 0/(v 0 : ℂ)=0
        rw [Coeff.deleteCoordinate_apply_same,zero_div]
      exact hillRoughAbelian_Gardner_matrix_on_real_ball Z η hZa hZp (Q u) (hQball u hu) hQr hQm σ τ n m)
  have hIq : I q∈ball (0 : Coeff 2) η := by
    simpa only [mem_ball_zero_iff,LinearIsometryEquiv.norm_map] using hq
  have hI0 : (I q) 0=0 := by
    change (v 0 : ℂ)*q.val 0=0
    rw [hmean,mul_zero]
  have hQq : Q (I q)=q := by
    change I.symm (D (I q))=q
    rw [(Coeff.deleteCoordinate_eq_self_iff 0 (I q)).mpr hI0]
    exact I.symm_apply_apply q
  simpa only [hQq] using he hIq

end NLS.KdV
