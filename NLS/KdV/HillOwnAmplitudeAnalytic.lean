import NLS.KdV.HillOwnCartesianAmplitude
import NLS.KdV.HillOwnGapFactorAnalytic

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV



variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

theorem exists_hillOwnCartesianAmplitude_analytic_extension (n : ℕ) (hn : 1 ≤ n) :
    ∃ F : Coeff 2 → ℂ, AnalyticAt ℂ F (SpectralWeight.one.toCoeff q) ∧
      ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
        F (SpectralWeight.one.toCoeff p.val) = hillOwnCartesianAmplitude p.val p.property.1 p.property.2 n hn := by
  obtain ⟨G,hG,hmatch⟩ := exists_hillOwnGapFactor_analytic_extension q hq hr n hn
  refine ⟨fun p => hillLocalActionGapPrefactor q hq hr n p*G p,
    (analyticAt_hillLocalActionGapPrefactor q hq hr n hn).mul hG,?_⟩
  filter_upwards [hillLocalActionGapPrefactor_eventually_eq_physical q hq hr n hn,hmatch] with p hp hGp
  rw [hp,hGp]
  rfl

theorem continuous_hillOwnCartesianAmplitude (n : ℕ) (hn : 1 ≤ n) :
    Continuous (fun p : RealPeriodOneHillPotential => hillOwnCartesianAmplitude p.val p.property.1 p.property.2 n hn) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  obtain ⟨F,hF,hmatch⟩ := exists_hillOwnCartesianAmplitude_analytic_extension p.val p.property.1 p.property.2 n hn
  let P : RealPeriodOneHillPotential → Coeff 2 := fun p => SpectralWeight.one.toCoeff p.val
  have hP : Continuous P := SpectralWeight.one.toCoeff.continuous.comp continuous_subtype_val
  have hc : ContinuousAt (fun r : RealPeriodOneHillPotential => F (P r)) p :=
    ContinuousAt.comp (f := P) hF.continuousAt hP.continuousAt
  exact hc.congr_of_eventuallyEq (Filter.EventuallyEq.symm hmatch)

theorem exists_hillSpectralCartesian_analytic_own_factor (n : ℕ) (hn : 1 ≤ n) :
    ∃ F : Coeff 2 → ℂ, AnalyticAt ℂ F (SpectralWeight.one.toCoeff q) ∧
      ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
        hillSpectralCartesian p.val p.property.1 p.property.2 n hn = F (SpectralWeight.one.toCoeff p.val)*
          Complex.exp (I*hillSummedRegularAbelianCorrection p.val p.property.1 p.property.2 n hn) := by
  obtain ⟨F,hF,hmatch⟩ := exists_hillOwnCartesianAmplitude_analytic_extension q hq hr n hn
  refine ⟨F,hF,?_⟩
  filter_upwards [hmatch] with p hp
  rw [hillSpectralCartesian_eq_ownAmplitude_mul_correction,hp]

theorem hillOwnCartesianAmplitude_eq_zero_iff (n : ℕ) (hn : 1 ≤ n) :
    hillOwnCartesianAmplitude q hq hr n hn = 0 ↔ hillRealGapHalfLength q hq hr n = 0 := by
  refine ⟨?_,hillOwnCartesianAmplitude_closed q hq hr n hn⟩
  intro hz
  by_contra hδ
  have hc : hillRealLabels q hq hr (2*n-1) ≠ hillRealLabels q hq hr (2*n) := by
    intro he
    apply hδ
    simp only [hillRealGapHalfLength,he,sub_self,zero_div]
  have hI := (hillRealGapIntegral_pos_iff q hq hr n hn).mpr
    (lt_of_le_of_ne (monotone_hillRealLabels q hq hr (by omega)) hc)
  have h := hillOwnCartesianAmplitude_action_identity q hq hr n hn
  rw [hz] at h
  simp only [zero_re,zero_im,zero_pow (by norm_num : (2 : ℕ) ≠ 0),zero_add] at h
  linarith

theorem hillSpectralCartesian_eq_zero_iff (n : ℕ) (hn : 1 ≤ n) :
    hillSpectralCartesian q hq hr n hn = 0 ↔ hillRealGapHalfLength q hq hr n = 0 := by
  rw [hillSpectralCartesian_eq_ownAmplitude_mul_correction,mul_eq_zero]
  simp only [Complex.exp_ne_zero,or_false,hillOwnCartesianAmplitude_eq_zero_iff]

end NLS.KdV
