import NLS.KdV.HillDeflatedTraceCharts
import NLS.KdV.HillEnergyChiPositivity

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV



variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

theorem hillDeflatedTraceNumerator_eq_chi_of_cut (n : ℕ) (hn : 1 ≤ n) (z : ℂ)
    (hz : z ∈ hillL2RealCutDomain q hq hr) (hzn : z ∈ hillGapFilledDomain q hq hr n) :
    hillDeflatedTraceNumerator q hq hr n z =
      ((hillGapCriticalPoint q hq hr n : ℂ)-z)/(2*I)*hillEnergyChi q hq hr n z := by
  have h := hillL2LogarithmicDifferential_selectedFactor q hq hr n hn z hz hzn
  rw [hillEnergyCanonicalRootProduct_eq_endpoint_mul_deflated q hq hr n hn z,
    hillEnergyCriticalRootRatio] at h
  have hE : endpointRoot (hillRealLabels q hq hr (2*n-1)) (hillRealLabels q hq hr (2*n)) z ≠ 0 :=
    endpointRoot_ne_zero_of_not_mem_segment _ _ _ (not_mem_hillGapSegment_of_mem_realCutDomain q hq hr z hz n hn)
  unfold hillDeflatedTraceNumerator
  have h := congrArg (fun v : ℂ => v*endpointRoot (hillRealLabels q hq hr (2*n-1)) (hillRealLabels q hq hr (2*n)) z) h
  field_simp [hE] at h ⊢
  linear_combination h

theorem hillDeflatedTraceNumerator_eq_chi (n : ℕ) (hn : 1 ≤ n) (z : ℂ)
    (hz : z ∈ hillGapFilledDomain q hq hr n) :
    hillDeflatedTraceNumerator q hq hr n z =
      ((hillGapCriticalPoint q hq hr n : ℂ)-z)/(2*I)*hillEnergyChi q hq hr n z := by
  by_cases hi : z.im ≠ 0
  · exact hillDeflatedTraceNumerator_eq_chi_of_cut q hq hr n hn z (Or.inl hi) hz
  have hzr : z = (z.re : ℂ) := by apply Complex.ext <;> simp [not_ne_iff.mp hi]
  rw [hzr] at hz ⊢
  let := real_upper_nhds_neBot z.re
  have hfilled : ∀ᶠ w in 𝓝[{w : ℂ | 0 < w.im}] (z.re : ℂ), w ∈ hillGapFilledDomain q hq hr n :=
    nhdsWithin_le_nhds ((isOpen_hillGapFilledDomain q hq hr n).mem_nhds hz)
  have hH := (analyticOnNhd_hillDeflatedTraceNumerator q hq hr n hn _ hz).continuousAt.tendsto.mono_left
    (nhdsWithin_le_nhds : 𝓝[{w : ℂ | 0 < w.im}] (z.re : ℂ) ≤ 𝓝 (z.re : ℂ))
  have hFa : AnalyticAt ℂ (fun w : ℂ => ((hillGapCriticalPoint q hq hr n : ℂ)-w)/(2*I)*hillEnergyChi q hq hr n w) (z.re : ℂ) :=
    ((analyticAt_const.sub analyticAt_id).div_const).mul (analyticOnNhd_hillEnergyChi q hq hr n _ hz)
  have hF := hFa.continuousAt.tendsto.mono_left
    (nhdsWithin_le_nhds : 𝓝[{w : ℂ | 0 < w.im}] (z.re : ℂ) ≤ 𝓝 (z.re : ℂ))
  apply tendsto_nhds_unique hH
  apply hF.congr'
  filter_upwards [hfilled,self_mem_nhdsWithin] with w hw hwi
  exact (hillDeflatedTraceNumerator_eq_chi_of_cut q hq hr n hn w (Or.inl (ne_of_gt hwi)) hw).symm

theorem neg_I_mul_deriv_hillDeflatedTraceNumerator_at_closed_gap (n : ℕ) (hn : 1 ≤ n)
    (hc : hillRealLabels q hq hr (2*n-1) = hillRealLabels q hq hr (2*n)) :
    -I*deriv (hillDeflatedTraceNumerator q hq hr n) (hillRealLabels q hq hr (2*n-1) : ℂ) =
      hillEnergyChi q hq hr n (hillRealLabels q hq hr (2*n-1) : ℂ)/2 := by
  let x : ℂ := hillRealLabels q hq hr (2*n-1)
  change -I*deriv (hillDeflatedTraceNumerator q hq hr n) x = hillEnergyChi q hq hr n x/2
  have hx : x ∈ hillGapFilledDomain q hq hr n :=
    hillGapSegment_subset_filledDomain q hq hr n hn (left_mem_segment ℝ _ _)
  have hspec := (hillGapCriticalPoint_spec q hq hr n hn).1
  rw [← hc] at hspec
  have hσ : (hillGapCriticalPoint q hq hr n : ℂ) = x := by
    change (hillGapCriticalPoint q hq hr n : ℂ) = (hillRealLabels q hq hr (2*n-1) : ℂ)
    exact congrArg Complex.ofReal (le_antisymm hspec.2 hspec.1)
  have he : hillDeflatedTraceNumerator q hq hr n =ᶠ[𝓝 x]
      (fun w : ℂ => (x-w)/(2*I)*hillEnergyChi q hq hr n w) := by
    filter_upwards [(isOpen_hillGapFilledDomain q hq hr n).mem_nhds hx] with w hw
    rw [hillDeflatedTraceNumerator_eq_chi q hq hr n hn w hw,hσ]
  have hd := (((hasDerivAt_const x x).sub (hasDerivAt_id x)).div_const (2*I)).mul
    (analyticOnNhd_hillEnergyChi q hq hr n x hx).differentiableAt.hasDerivAt
  have hd' : HasDerivAt (fun w : ℂ => (x-w)/(2*I)*hillEnergyChi q hq hr n w)
      ((-1 : ℂ)/(2*I)*hillEnergyChi q hq hr n x) x := by
    convert! hd using 1; simp only [Pi.sub_apply,id_eq,sub_self,zero_div,zero_mul,add_zero,zero_sub]
  rw [(hd'.congr_of_eventuallyEq he).deriv]
  field_simp

end NLS.KdV
