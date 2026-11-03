import NLS.KdV.HillHierarchyMomentContinuity
import NLS.KdV.HillSobolevEnergy
import NLS.KdV.HillFinitePhysicalPotential
import NLS.KdV.HillRealWeightedTruncation
import NLS.KdV.HillSmoothEnergyTrace

/-! # The actual physical energy trace for real mean-zero H1 Hill potentials

The finite physical smooth trace, real mean-zero Fourier approximation and
independent continuity of both sides prove the energy trace on the entire
native real mean-zero H1 domain. The positive-index real gap-integral series
sums to H1/4 with the physical unit-period derivative convention.
-/

noncomputable section
open Set Complex MeasureTheory Filter Topology
namespace NLS.KdV
open NLS.Fourier NLS.ZakharovShabat
open scoped ComplexConjugate

theorem hillContinuousCoefficients_nativeH1
    (p : WeightedCoeff hillH1Weight.doubleIndex.toWeight 2) :
    hillContinuousCoefficients (periodOneSobolevSynthesis (hillNativeH1ToScalar p)) =
      hillPeriodOneUnitPotential hillH1Weight p := by
  apply Subtype.ext
  funext k
  rw [hillContinuousCoefficients_apply]
  change fourierCoeff (continuousSynthesis (Coeff.periodDouble
    (WeightedCoeff.sobolevToL1CLM 2 (by norm_num) (hillNativeH1ToScalar p)))) k = _
  rw [fourierCoeff_continuousSynthesis]
  change Coeff.periodDouble (WeightedCoeff.sobolevToL1CLM 2 (by norm_num) (hillNativeH1ToScalar p)) k =
    (hillForgetWeight hillH1Weight 2 (hillPeriodOnePotential hillH1Weight p)).val k
  rw [hillForgetWeight_apply]
  by_cases hk : k % 2 = 0
  · have he : k = 2*(k/2) := by omega
    rw [he, Coeff.periodDouble_even, hillPeriodOnePotential_even,
      WeightedCoeff.sobolevToL1CLM_apply, hillNativeH1ToScalar_apply]
  · have he : k = 2*(k/2)+1 := by omega
    rw [he, Coeff.periodDouble_odd, hillPeriodOnePotential_odd]

theorem mean_nativeH1PhysicalPotential
    (p : WeightedCoeff hillH1Weight.doubleIndex.toWeight 2) :
    (∫ x in (0 : ℝ)..1, periodOneSobolevSynthesis (hillNativeH1ToScalar p) (x : AddCircle (2 : ℝ))) =
      p.val 0 := by
  have h := periodOneCoefficient_periodOneSobolevSynthesis (hillNativeH1ToScalar p) 0
  rw [hillNativeH1ToScalar_apply] at h
  unfold periodOneCoefficient at h
  rw [fourierCoeffOn_eq_integral] at h
  simpa using h

theorem real_nativeH1PhysicalPotential
    (p : WeightedCoeff hillH1Weight.doubleIndex.toWeight 2)
    (hr : IsRealHillPotential (hillH1Weight.doubleIndex.toCoeff p)) :
    ∀ x : AddCircle (2 : ℝ), (periodOneSobolevSynthesis (hillNativeH1ToScalar p) x).im = 0 := by
  apply hillContinuousPotential_real_of_coefficients
  rw [hillContinuousCoefficients_nativeH1]
  exact hillPeriodOneUnitPotential_real hillH1Weight p hr


theorem hillNativeH1Synthesis_finite
    (p : WeightedCoeff hillH1Weight.doubleIndex.toWeight 2) (a : ℤ →₀ ℂ)
    (hp : p = WeightedCoeff.ofFinsupp hillH1Weight.doubleIndex.toWeight 2 a) :
    periodOneSobolevSynthesis (hillNativeH1ToScalar p) = hillFinitePhysicalPotential a := by
  have ha : WeightedCoeff.sobolevToL1CLM 2 (by norm_num) (hillNativeH1ToScalar p) =
      Coeff.ofFinsupp (p := 1) a := by
    ext k
    rw [WeightedCoeff.sobolevToL1CLM_apply, hillNativeH1ToScalar_apply, hp]
    rfl
  change continuousSynthesis (Coeff.periodDouble
    (WeightedCoeff.sobolevToL1CLM 2 (by norm_num) (hillNativeH1ToScalar p))) =
      continuousSynthesis (Coeff.periodDouble (Coeff.ofFinsupp (p := 1) a))
  rw [ha]

theorem hillContinuousCoefficients_finitePhysical_weighted (w : SpectralWeight) (a : ℤ →₀ ℂ) :
    hillContinuousCoefficients (hillFinitePhysicalPotential a) = hillPeriodOneUnitPotential w
      (WeightedCoeff.ofFinsupp w.doubleIndex.toWeight 2 a) := by
  exact (hillContinuousCoefficients_finitePhysical a).trans
    (hillPeriodOneUnitPotential_eq_of_coeff_eq SpectralWeight.one w
      (WeightedCoeff.ofFinsupp SpectralWeight.one.doubleIndex.toWeight 2 a)
      (WeightedCoeff.ofFinsupp w.doubleIndex.toWeight 2 a) (fun _ => rfl))

theorem tsum_hillHierarchyMomentTerm_energy_finite
    (p : RealHillWeightedPotential hillH1Weight) (a : ℤ →₀ ℂ)
    (hp : p.val = WeightedCoeff.ofFinsupp hillH1Weight.doubleIndex.toWeight 2 a)
    (hmean : p.val.val 0 = 0) :
    ((∑' n : ℕ, hillHierarchyMomentTerm hillH1Weight p 1 n : ℝ) : ℂ) =
      hillNativeH1Energy p.val / 4 := by
  have ha (n : ℤ) : a (-n) = conj (a n) := by
    have h := p.property n
    simpa only [SpectralWeight.toCoeff_apply, hp, WeightedCoeff.ofFinsupp_apply] using h
  have haz : a 0 = 0 := by simpa only [hp, WeightedCoeff.ofFinsupp_apply] using hmean
  let Q := hillFinitePhysicalPotential a
  have hreal := real_hillFinitePhysicalPotential a ha
  have hperiodic := periodic_hillFinitePhysicalPotential a
  have hzero : (∫ x in (0 : ℝ)..1, Q (x : AddCircle (2 : ℝ))) = 0 :=
    (mean_hillFinitePhysicalPotential a).trans haz
  have h := hasSum_hillPhysicalMoments_energy_smooth Q hreal
    (contDiff_hillFinitePhysicalPotential a) hperiodic hzero
  have hcoeff : hillContinuousCoefficients Q = hillPeriodOneUnitPotential hillH1Weight p.val := by
    rw [hp]
    exact hillContinuousCoefficients_finitePhysical_weighted _ a
  have he (k : ℕ) : (2*(k+1 : ℕ)*Real.pi : ℂ) *
      hillL2RealContourMoment (hillContinuousCoefficients Q) (hillContinuousCoefficients_mem_even Q hperiodic)
        (isRealHillPotential_hillContinuousCoefficients Q hreal) (k+1) 1 =
      (hillHierarchyMomentTerm hillH1Weight p 1 (k+1) : ℂ) := by
    rw [hillL2RealContourMoment_eq_gapIntegral _ _ _ (k+1) (by omega)]
    rw [hillRealGapIntegral_congr (hillContinuousCoefficients Q)
      (hillPeriodOneUnitPotential hillH1Weight p.val)
      (hillContinuousCoefficients_mem_even Q hperiodic)
      (hillPeriodOneUnitPotential_even hillH1Weight p.val)
      (isRealHillPotential_hillContinuousCoefficients Q hreal)
      (hillPeriodOneUnitPotential_real hillH1Weight p.val p.property) hcoeff (k+1) 1]
    unfold hillHierarchyMomentTerm
    push_cast
    ring
  rw [funext he] at h
  have hE : hillNativeH1Energy p.val = classicalHamiltonian
      (fun x : ℝ => Q (x : AddCircle (2 : ℝ))) := by
    rw [hillNativeH1Energy_eq_classical, hillNativeH1Synthesis_finite p.val a hp]
  rw [← hE] at h
  have hs := summable_hillHierarchyMomentTerm hillH1Weight p 1
    (fun n _ => hillH1Weight_growth n)
  have hz : hillHierarchyMomentTerm hillH1Weight p 1 0 = 0 := by simp [hillHierarchyMomentTerm]
  have ht := hs.sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one, hz, zero_add] at ht
  have hpos := ((summable_nat_add_iff 1).mpr hs).hasSum
  rw [ht] at hpos
  have hc : HasSum (fun k : ℕ => (hillHierarchyMomentTerm hillH1Weight p 1 (k+1) : ℂ))
      ((∑' n : ℕ, hillHierarchyMomentTerm hillH1Weight p 1 n : ℝ) : ℂ) := by
    simpa only [Complex.ofRealCLM_apply] using Complex.ofRealCLM.hasSum hpos
  exact hc.unique h

theorem tsum_hillHierarchyMomentTerm_energy_h1
    (q : RealHillWeightedPotential hillH1Weight) (hmean : q.val.val 0 = 0) :
    ((∑' n : ℕ, hillHierarchyMomentTerm hillH1Weight q 1 n : ℝ) : ℂ) =
      hillNativeH1Energy q.val / 4 := by
  have hfinite (N : ℕ) :
      ((∑' n : ℕ, hillHierarchyMomentTerm hillH1Weight
        (hillRealWeightedTruncate hillH1Weight N q) 1 n : ℝ) : ℂ) =
      hillNativeH1Energy (hillRealWeightedTruncate hillH1Weight N q).val / 4 :=
    tsum_hillHierarchyMomentTerm_energy_finite _ (hillRealTruncationFinsupp hillH1Weight N q)
      (hillRealWeightedTruncate_eq_ofFinsupp hillH1Weight N q)
      (hillRealWeightedTruncate_mean_zero hillH1Weight N q hmean)
  have hq := tendsto_hillRealWeightedTruncate hillH1Weight q
  have hL : Continuous (fun p : RealHillWeightedPotential hillH1Weight =>
      ((∑' n : ℕ, hillHierarchyMomentTerm hillH1Weight p 1 n : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_tsum_hillHierarchyMomentTerm hillH1Weight 1
      (fun n _ => hillH1Weight_growth n))
  have hR : Continuous (fun p : RealHillWeightedPotential hillH1Weight => hillNativeH1Energy p.val / 4) :=
    (continuous_hillNativeH1Energy.comp continuous_subtype_val).div_const 4
  have hLt := (hL.tendsto q).comp hq
  have hRt := (hR.tendsto q).comp hq
  simp only [Function.comp_def] at hLt hRt
  rw [funext hfinite] at hLt
  exact tendsto_nhds_unique hLt hRt


theorem hasSum_hillHierarchyMoments_energy_h1
    (q : RealHillWeightedPotential hillH1Weight) (hmean : q.val.val 0 = 0) :
    HasSum (fun k : ℕ => hillHierarchyMomentTerm hillH1Weight q 1 (k+1))
      ((hillNativeH1Energy q.val).re / 4) := by
  have hs := summable_hillHierarchyMomentTerm hillH1Weight q 1
    (fun n _ => hillH1Weight_growth n)
  have hz : hillHierarchyMomentTerm hillH1Weight q 1 0 = 0 := by simp [hillHierarchyMomentTerm]
  have ht := hs.sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one, hz, zero_add] at ht
  have hv := congrArg Complex.re (tsum_hillHierarchyMomentTerm_energy_h1 q hmean)
  simp only [Complex.ofReal_re, Complex.div_ofNat_re] at hv
  have h := ((summable_nat_add_iff 1).mpr hs).hasSum
  rw [ht, hv] at h
  exact h

theorem hillNativeH1Energy_im_eq_zero
    (q : RealHillWeightedPotential hillH1Weight) (hmean : q.val.val 0 = 0) :
    (hillNativeH1Energy q.val).im = 0 := by
  have h := congrArg Complex.im (tsum_hillHierarchyMomentTerm_energy_h1 q hmean)
  simp only [Complex.ofReal_im, Complex.div_ofNat_im] at h
  linarith

theorem hasSum_hillRealMoments_energy_h1
    (q : WeightedCoeff hillH1Weight.doubleIndex.toWeight 2)
    (hr : IsRealHillPotential (hillH1Weight.doubleIndex.toCoeff q))
    (hmean : q.val 0 = 0) :
    HasSum (fun k : ℕ => (2*Real.pi*(k+1 : ℕ)) *
      hillRealGapIntegral (hillPeriodOneUnitPotential hillH1Weight q)
        (hillPeriodOneUnitPotential_even hillH1Weight q)
        (hillPeriodOneUnitPotential_real hillH1Weight q hr) (k+1) 1)
      ((classicalHamiltonian (fun x : ℝ =>
        periodOneSobolevSynthesis (hillNativeH1ToScalar q) (x : AddCircle (2 : ℝ)))).re / 4) := by
  have h := hasSum_hillHierarchyMoments_energy_h1 ⟨q, hr⟩ hmean
  simpa only [hillHierarchyMomentTerm, hillNativeH1Energy_eq_classical] using h



theorem isReal_hillScalarToNativeH1 (a : ScalarDomain 2)
    (hr : IsRealHillPotential (scalarInclusion a)) :
    IsRealHillPotential (hillH1Weight.doubleIndex.toCoeff (hillScalarToNativeH1 a)) := by
  intro k
  simpa only [SpectralWeight.toCoeff_apply, hillScalarToNativeH1_apply, scalarInclusion_apply] using hr k

theorem real_periodOneSobolevSynthesis_of_coefficients (a : ScalarDomain 2)
    (hr : IsRealHillPotential (scalarInclusion a)) :
    ∀ x : AddCircle (2 : ℝ), (periodOneSobolevSynthesis a x).im = 0 := by
  have h := real_nativeH1PhysicalPotential (hillScalarToNativeH1 a) (isReal_hillScalarToNativeH1 a hr)
  simpa only [hillNativeH1ToScalar_scalarToNativeH1] using h

theorem mean_periodOneSobolevSynthesis (a : ScalarDomain 2) :
    (∫ x in (0 : ℝ)..1, periodOneSobolevSynthesis a (x : AddCircle (2 : ℝ))) = a.val 0 := by
  have h := mean_nativeH1PhysicalPotential (hillScalarToNativeH1 a)
  simpa only [hillNativeH1ToScalar_scalarToNativeH1, hillScalarToNativeH1_apply] using h

theorem hasSum_hillPhysicalSobolevMoments_energy
    (a : ScalarDomain 2) (hr : IsRealHillPotential (scalarInclusion a)) (hmean : a.val 0 = 0) :
    let Q := periodOneSobolevSynthesis a
    HasSum (fun k : ℕ => (2*Real.pi*(k+1 : ℕ)) *
      hillRealGapIntegral (hillContinuousCoefficients Q)
        (hillContinuousCoefficients_mem_even Q (periodOneSobolevSynthesis_periodic a))
        (isRealHillPotential_hillContinuousCoefficients Q (real_periodOneSobolevSynthesis_of_coefficients a hr))
        (k+1) 1)
      ((classicalHamiltonian (fun x : ℝ => Q (x : AddCircle (2 : ℝ)))).re / 4) := by
  dsimp only
  let Q := periodOneSobolevSynthesis a
  let q := hillScalarToNativeH1 a
  have hrq := isReal_hillScalarToNativeH1 a hr
  have hzero : q.val 0 = 0 := by simpa only [q, hillScalarToNativeH1_apply] using hmean
  have h := hasSum_hillRealMoments_energy_h1 q hrq hzero
  have hCQ : hillContinuousCoefficients Q = hillPeriodOneUnitPotential hillH1Weight q := by
    have hc := hillContinuousCoefficients_nativeH1 q
    simpa only [q, hillNativeH1ToScalar_scalarToNativeH1] using hc
  have he (k : ℕ) : hillRealGapIntegral (hillPeriodOneUnitPotential hillH1Weight q)
      (hillPeriodOneUnitPotential_even hillH1Weight q)
      (hillPeriodOneUnitPotential_real hillH1Weight q hrq) (k+1) 1 =
    hillRealGapIntegral (hillContinuousCoefficients Q)
      (hillContinuousCoefficients_mem_even Q (periodOneSobolevSynthesis_periodic a))
      (isRealHillPotential_hillContinuousCoefficients Q (real_periodOneSobolevSynthesis_of_coefficients a hr))
      (k+1) 1 :=
    hillRealGapIntegral_congr _ _ _ _ _ _ hCQ.symm (k+1) 1
  have hefun : (fun k : ℕ => (2*Real.pi*(k+1 : ℕ)) *
      hillRealGapIntegral (hillPeriodOneUnitPotential hillH1Weight q)
        (hillPeriodOneUnitPotential_even hillH1Weight q)
        (hillPeriodOneUnitPotential_real hillH1Weight q hrq) (k+1) 1) =
      (fun k : ℕ => (2*Real.pi*(k+1 : ℕ)) *
        hillRealGapIntegral (hillContinuousCoefficients Q)
          (hillContinuousCoefficients_mem_even Q (periodOneSobolevSynthesis_periodic a))
          (isRealHillPotential_hillContinuousCoefficients Q (real_periodOneSobolevSynthesis_of_coefficients a hr))
          (k+1) 1) := by
    funext k
    rw [he]
  rw [hefun] at h
  simpa only [q, hillNativeH1ToScalar_scalarToNativeH1] using h


theorem isReal_scalarInclusion_of_physical_real (a : ScalarDomain 2)
    (hreal : ∀ x : AddCircle (2 : ℝ), (periodOneSobolevSynthesis a x).im = 0) :
    IsRealHillPotential (scalarInclusion a) := by
  let q := hillScalarToNativeH1 a
  have hCQ : hillContinuousCoefficients (periodOneSobolevSynthesis a) =
      hillPeriodOneUnitPotential hillH1Weight q := by
    have hc := hillContinuousCoefficients_nativeH1 q
    simpa only [q, hillNativeH1ToScalar_scalarToNativeH1] using hc
  have hr := isRealHillPotential_hillContinuousCoefficients (periodOneSobolevSynthesis a) hreal
  rw [hCQ] at hr
  intro k
  have h := hr (2*k)
  simp only [SpectralWeight.toCoeff_apply] at h
  have he : -(2*k : ℤ) = 2*(-k) := by ring
  rw [he] at h
  dsimp only [hillPeriodOneUnitPotential] at h
  rw [hillForgetWeight_apply, hillForgetWeight_apply,
    hillPeriodOnePotential_even, hillPeriodOnePotential_even] at h
  simpa only [q, hillScalarToNativeH1_apply, scalarInclusion_apply] using h

theorem hasSum_hillPhysicalH1Moments_energy
    (a : ScalarDomain 2)
    (hreal : ∀ x : AddCircle (2 : ℝ), (periodOneSobolevSynthesis a x).im = 0)
    (hmean : (∫ x in (0 : ℝ)..1, periodOneSobolevSynthesis a (x : AddCircle (2 : ℝ))) = 0) :
    let Q := periodOneSobolevSynthesis a
    HasSum (fun k : ℕ => (2*Real.pi*(k+1 : ℕ)) *
      hillRealGapIntegral (hillContinuousCoefficients Q)
        (hillContinuousCoefficients_mem_even Q (periodOneSobolevSynthesis_periodic a))
        (isRealHillPotential_hillContinuousCoefficients Q hreal) (k+1) 1)
      ((classicalHamiltonian (fun x : ℝ => Q (x : AddCircle (2 : ℝ)))).re / 4) := by
  have hr := isReal_scalarInclusion_of_physical_real a hreal
  have hz : a.val 0 = 0 := (mean_periodOneSobolevSynthesis a).symm.trans hmean
  exact hasSum_hillPhysicalSobolevMoments_energy a hr hz

end NLS.KdV
