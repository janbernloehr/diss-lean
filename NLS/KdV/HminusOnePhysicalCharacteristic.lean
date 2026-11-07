import NLS.KdV.PeriodOneHminusOneOriginal
import NLS.KdV.SingularHillL2Characteristic
import NLS.KdV.SingularHillSpectralPersistence
import NLS.KdV.HillHminusOneDiscAsymptotics
import NLS.ComplexAnalysis.ClosedZeroGraph

/-! Exact physical characteristic criterion for all unit-period H-minus-one
potentials, via the original full-domain operator and L2 density. -/
noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue NLS.ComplexAnalysis

/-- The existing L2 physical criterion in the exact unit-period normalization. -/
theorem singularHillSpectrum_periodOneL2_iff (a : Coeff 2) (z : ℂ) :
    z ∈ singularHillSpectrum (periodOneOriginal (periodOneL2Inclusion a)) ↔
      hillHminusDiscriminant (periodOneL2Inclusion a) z ^ 2 = 4 := by
  rw [periodOneOriginal_L2, singularHillSpectrum_L2_iff_discriminant
    (periodOneL2OriginalCoefficients a) (by
      rw [periodOneL2OriginalCoefficients_toCoeff]
      exact Coeff.periodDouble_mem a), periodOneL2OriginalCoefficients_toCoeff,
    hillHminusDiscriminant_eq_hillL2]

/-- High full-disc trace asymptotics exclude an identically zero characteristic
at every complex H-minus-one potential. -/
theorem exists_hminusOne_physical_characteristic_ne_zero (q : PeriodOneHminusOne) :
    ∃ z : ℂ, hillHminusDiscriminant q z ^ 2 ≠ 4 := by
  obtain ⟨N,V,_,_,hq,hd⟩ := exists_hillHminus_disc_trace_approximation q
    (Real.pi/4) (by positivity) le_rfl (1/4) (by norm_num)
  let z : ℂ := (Real.pi : ℂ)*N+(Real.pi/4 : ℝ)
  have hz : z ∈ closedBall ((Real.pi : ℂ)*N) (Real.pi/4) := by
    simp only [mem_closedBall, dist_eq_norm, z, add_sub_cancel_left, norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity : 0 < Real.pi/4)]
    exact le_rfl
  have happrox := hd q hq N le_rfl z hz
  have hfree : ‖2*cos z‖ = Real.sqrt 2 := by
    have he := congrArg norm (freeHillTrace_parity_shift N z)
    simp only [norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul,z,
      add_sub_cancel_left, ← ofReal_cos, Real.cos_pi_div_four, norm_real,
      Real.norm_eq_abs] at he
    rw [abs_of_nonneg (by positivity : 0 ≤ Real.sqrt 2/2)] at he
    norm_num at he
    rw [norm_mul]
    norm_num
    dsimp only [z]
    simp only [ofReal_div, ofReal_ofNat]
    linarith
  have hsmall : ‖hillHminusDiscriminant q (z^2)‖ < 2 := by
    have h := norm_le_norm_sub_add (hillHminusDiscriminant q (z^2)) (2*cos z)
    rw [hfree] at h
    have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
    nlinarith [Real.sqrt_nonneg 2]
  refine ⟨z^2, fun he => ?_⟩
  have hn := congrArg norm he
  rw [norm_pow] at hn
  norm_num at hn
  nlinarith [norm_nonneg (hillHminusDiscriminant q (z^2))]

/-- Joint continuity of the original physical characteristic, with parameter first. -/
theorem continuous_hminusOne_physical_characteristic :
    Continuous (fun p : PeriodOneHminusOne × ℂ => hillHminusDiscriminant p.1 p.2 ^ 2 - 4) := by
  have hd := analyticOnNhd_hillHminusDiscriminant_joint.continuous
  have hm : Continuous (fun p : PeriodOneHminusOne × ℂ => (p.2,p.1)) :=
    continuous_snd.prodMk continuous_fst
  exact ((hd.comp hm).pow 2).sub continuous_const

/-- Every characteristic zero is in the ENTIRE original full-domain spectrum,
for every complex unit-period H-minus-one potential. -/
theorem singularHillSpectrum_of_hminusOne_characteristic
    (q : PeriodOneHminusOne) (z : ℂ) (hz : hillHminusDiscriminant q z ^ 2 = 4) :
    z ∈ singularHillSpectrum (periodOneOriginal q) := by
  let F : PeriodOneHminusOne → ℂ → ℂ := fun a w => hillHminusDiscriminant a w ^ 2 - 4
  have ha (a : PeriodOneHminusOne) : AnalyticOnNhd ℂ (F a) univ := by
    intro w _
    exact (((analyticOnNhd_hillHminusDiscriminant_joint (w,a) (mem_univ _)).comp
      (f := fun w : ℂ => (w,a)) (analyticAt_id.prod analyticAt_const)).pow 2).sub analyticAt_const
  let K := {p : PeriodOneHminusOne × ℂ | p.2 ∈ singularHillSpectrum (periodOneOriginal p.1)}
  have hK : IsClosed K := by
    have hm : Continuous (fun p : PeriodOneHminusOne × ℂ => (periodOneOriginal p.1,p.2)) :=
      (periodOneOriginal.continuous.comp continuous_fst).prodMk continuous_snd
    exact (isOpen_singularHillJointResolvent.preimage hm).isClosed_compl
  obtain ⟨b,hb⟩ := exists_hminusOne_physical_characteristic_ne_zero q
  apply zero_graph_mem_closed_of_closure_parameters F continuous_hminusOne_physical_characteristic ha
    (range periodOneL2Inclusion) K hK ?_ q (denseRange_periodOneL2Inclusion q)
      b (sub_ne_zero.mpr hb) z (sub_eq_zero.mpr hz)
  rintro a ⟨v,rfl⟩ w hw
  exact (singularHillSpectrum_periodOneL2_iff v w).mpr (sub_eq_zero.mp hw)

/-- Every original full-domain spectral point is a characteristic zero,
with no reality, endpoint regularity or simplicity restriction. -/
theorem hminusOne_characteristic_of_singularHillSpectrum
    (q : PeriodOneHminusOne) (z : ℂ) (hz : z ∈ singularHillSpectrum (periodOneOriginal q)) :
    hillHminusDiscriminant q z ^ 2 = 4 := by
  by_contra hchar
  have hne : (q,z) ∈ {p : PeriodOneHminusOne × ℂ |
      hillHminusDiscriminant p.1 p.2 ^ 2 - 4 ≠ 0} := sub_ne_zero.mpr hchar
  have hopen : IsOpen {p : PeriodOneHminusOne × ℂ |
      hillHminusDiscriminant p.1 p.2 ^ 2 - 4 ≠ 0} :=
    isOpen_ne_fun continuous_hminusOne_physical_characteristic continuous_const
  obtain ⟨U,hU,V,hV,hUV⟩ := mem_nhds_prod_iff.mp (hopen.mem_nhds hne)
  obtain ⟨ε,hε,hεV⟩ := Metric.mem_nhds_iff.mp hV
  obtain ⟨ρ,hρ,hρε,hcircle⟩ := exists_singularHill_resolvent_circle (periodOneOriginal q) z ε hε
  have hp := singularHillRieszProjection_ne_zero_of_mem_spectrum (periodOneOriginal q) z ρ hρ
    hcircle z (mem_ball_self hρ) hz
  have hpnear : ∀ᶠ a in 𝓝 q, singularHillRieszProjection (periodOneOriginal a) z ρ ≠ 0 :=
    periodOneOriginal.continuous.continuousAt.tendsto.eventually
      (eventually_singularHillRieszProjection_ne_zero (periodOneOriginal q) z ρ hρ hcircle hp)
  have hfreq : ∃ᶠ a in 𝓝 q, a ∈ range periodOneL2Inclusion :=
    mem_closure_iff_frequently.mp (denseRange_periodOneL2Inclusion q)
  have hU' : ∀ᶠ a in 𝓝 q, a ∈ U := hU
  obtain ⟨a,⟨v,rfl⟩,haU,haP⟩ := (hfreq.and_eventually (hU'.and hpnear)).exists
  apply haP
  apply singularHillRieszProjection_eq_zero_of_closedBall_resolvent
    (periodOneOriginal (periodOneL2Inclusion v)) z ρ hρ.le
  intro w hw
  by_contra hn
  have hs : w ∈ singularHillSpectrum (periodOneOriginal (periodOneL2Inclusion v)) := hn
  have htrace := (singularHillSpectrum_periodOneL2_iff v w).mp hs
  have hnonzero : hillHminusDiscriminant (periodOneL2Inclusion v) w ^ 2 - 4 ≠ 0 :=
    hUV (a := (periodOneL2Inclusion v,w)) ⟨haU,hεV (closedBall_subset_ball hρε hw)⟩
  exact hnonzero (sub_eq_zero.mpr htrace)

/-- The complete original H1/H-minus-one spectrum is EXACTLY the physical
energy-discriminant zero set at every complex unit-period H-minus-one potential. -/
theorem singularHillSpectrum_periodOne_iff_discriminant
    (q : PeriodOneHminusOne) (z : ℂ) :
    z ∈ singularHillSpectrum (periodOneOriginal q) ↔ hillHminusDiscriminant q z ^ 2 = 4 :=
  ⟨hminusOne_characteristic_of_singularHillSpectrum q z,
    singularHillSpectrum_of_hminusOne_characteristic q z⟩

end NLS.KdV
