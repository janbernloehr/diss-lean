import NLS.KdV.HillActionSourceStationarity
import NLS.ComplexAnalysis.SquareRootSourceStationarity
import Mathlib.Analysis.Complex.SqrtDeriv
import Mathlib.Analysis.RCLike.Sqrt

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

/-- The actual positive action amplitude, continued at an open physical gap. -/
def hillLocalActionAmplitude (n : ℕ) (p : Coeff 2) : ℂ :=
  Complex.sqrt (2*hillRealSourceMoment q hq hr n 0 p)

/-- This amplitude matches the original physical action, with its positive sign. -/
theorem eventually_hillLocalActionAmplitude_eq_physical (n : ℕ) (hn : 1≤n) :
    ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
      hillLocalActionAmplitude q hq hr n (SpectralWeight.one.toCoeff p.val)=
        (Real.sqrt (2*hillRealGapIntegral p.val p.property.1 p.property.2 n 0) : ℂ) := by
  obtain ⟨V,hV,hqV,hmatch⟩ := exists_hillRealSourceMoments_physical_neighborhood q hq hr n hn
  filter_upwards [hV.mem_nhds hqV] with p hp
  rw [hillLocalActionAmplitude,hmatch p hp 0,←ofReal_ofNat,←ofReal_mul]
  exact Complex.sqrt_of_nonneg (by exact_mod_cast (mul_nonneg (by norm_num : (0 : ℝ)≤2)
    (hillRealGapIntegral_nonneg_even p.val p.property.1 p.property.2 n hn 0)))

/-- The action amplitude is analytic at every open physical gap. -/
theorem analyticAt_hillLocalActionAmplitude (n : ℕ) (hn : 1≤n)
    (hgap : hillRealGapHalfLength q hq hr n≠0) :
    AnalyticAt ℂ (hillLocalActionAmplitude q hq hr n) (SpectralWeight.one.toCoeff q) := by
  have hopen : hillRealLabels q hq hr (2*n-1)<hillRealLabels q hq hr (2*n) := by
    apply lt_of_le_of_ne (monotone_hillRealLabels q hq hr (by omega))
    intro he
    exact hgap (by simp only [hillRealGapHalfLength,he,sub_self,zero_div])
  have hpos := (hillRealGapIntegral_pos_iff q hq hr n hn).mpr hopen
  obtain ⟨V,_,hqV,hmatch⟩ := exists_hillRealSourceMoments_physical_neighborhood q hq hr n hn
  have hbase := hmatch ⟨q,hq,hr⟩ hqV 0
  have hslit : 2*hillRealSourceMoment q hq hr n 0 (SpectralWeight.one.toCoeff q)∈Complex.slitPlane := by
    rw [hbase,Complex.mem_slitPlane_iff]
    left
    norm_num [mul_re]
    exact hpos
  exact (Complex.differentiableOn_sqrt.analyticAt (Complex.isOpen_slitPlane.mem_nhds hslit)).comp
    (f := fun p : Coeff 2 => 2*hillRealSourceMoment q hq hr n 0 p)
    (analyticAt_const.mul (analyticAt_hillRealSourceMoment q hq hr n hn 0))

/-- The positive action amplitude is stationary under every physical action source. -/
theorem hillLocalActionAmplitude_physicalActionSource_fderiv (n k : ℕ) (hn : 1≤n) (hk : 1≤k)
    (hgap : hillRealGapHalfLength q hq hr n≠0) :
    (fderiv ℂ (hillLocalActionAmplitude q hq hr n) (SpectralWeight.one.toCoeff q))
      (SpectralWeight.one.toCoeff (hillPhysicalMomentHamiltonianSource q hq hr k hk 0))=0 := by
  have hA := analyticAt_hillLocalActionAmplitude q hq hr n hn hgap
  have hF : AnalyticAt ℂ (fun p : Coeff 2 => 2*hillRealSourceMoment q hq hr n 0 p)
      (SpectralWeight.one.toCoeff q) :=
    analyticAt_const.mul (analyticAt_hillRealSourceMoment q hq hr n hn 0)
  have hne : hillLocalActionAmplitude q hq hr n (SpectralWeight.one.toCoeff q)≠0 := by
    rw [(eventually_hillLocalActionAmplitude_eq_physical q hq hr n hn).self_of_nhds]
    apply ofReal_ne_zero.mpr
    apply (Real.sqrt_pos.mpr ?_).ne'
    apply mul_pos (by norm_num)
    apply (hillRealGapIntegral_pos_iff q hq hr n hn).mpr
    apply lt_of_le_of_ne (monotone_hillRealLabels q hq hr (by omega))
    intro he
    exact hgap (by simp only [hillRealGapHalfLength,he,sub_self,zero_div])
  apply squareRoot_source_fderiv_eq_zero _ _ _ _ hA hF
    (Filter.Eventually.of_forall (fun p => complex_sqrt_sq _)) hne
  rw [fderiv_const_mul (analyticAt_hillRealSourceMoment q hq hr n hn 0).differentiableAt]
  simp only [smul_apply,smul_eq_mul,hillRealSourceMoment_physicalMomentHamiltonianSource_fderiv q hq hr n k hn hk 0 0,mul_zero]

end NLS.KdV
