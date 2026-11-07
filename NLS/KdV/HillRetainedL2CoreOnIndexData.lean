import NLS.KdV.HillRetainedSpectralCoreDiracIdentity
import NLS.KdV.HillL2TerminalModelOneSmoothing
import NLS.KdV.HillL2OnIndexExponentialSmoothing
import NLS.SequenceSpaces.SignedOrderLinearInclusions

/-! Physical core smoothing and the actual on-index exponential share
ONE retained patch, ONE original family and ONE common complex L2
neighborhood. The core itself has an exact analytic H1/2 realization. -/
noncomputable section
open Set Complex Filter Topology NLS.ZakharovShabat
namespace NLS.KdV.HillProductEquationPatch

private theorem eventually_L2_open (q : Coeff 2) (V : Set PeriodOneHminusOne)
    (hV : IsOpen V) (hqV : periodOneL2Inclusion q ∈ V) :
    ∀ᶠ r in 𝓝 q, periodOneL2Inclusion r ∈ V :=
  periodOneL2Inclusion.continuous.continuousAt.tendsto.eventually (hV.mem_nhds hqV)

private theorem core_raw_of_model (P : HillProductEquationPatch) (r : Coeff 2) (k : ℤ)
    (he : P.physicalSpectralCoreMap (periodOneL2Inclusion r) =
      sourceHillTerminalModel (P.rotatedDiracSource (periodOneL2Inclusion r)))
    (h : (P.l2TerminalModelFourierRemainder r).val k =
      (sourceHillTerminalModel (P.rotatedDiracSource (periodOneL2Inclusion r))).val k -
        WeightedCoeff.halfFourierSymbol k * r k) :
    (P.l2TerminalModelFourierRemainder r).val k =
      (P.physicalSpectralCoreMap (periodOneL2Inclusion r)).val k -
        WeightedCoeff.halfFourierSymbol k * r k :=
  h.trans (congrArg (fun a : WeightedCoeff (Weight.signedSobolev (-1/2)) 2 =>
    a.val k - WeightedCoeff.halfFourierSymbol k * r k) he.symm)

theorem exists_retained_l2Core_smoothing (P : HillProductEquationPatch)
    (H : SourceLemma12_12Data (by norm_num) (by norm_num) P.parent.family.originalDomain
      P.parent.family.domain P.parent.family.roots)
    (q : Coeff 2) (hq : periodOneL2Inclusion q ∈ P.source)
    (hr : IsRealPeriodOneHminusOne (periodOneL2Inclusion q)) :
    ∃ U : Set (Coeff 2), IsOpen U ∧ q ∈ U ∧
      (∀ r ∈ U, periodOneL2Inclusion r ∈ P.physicalDirichletSource ∩ hillHminusActionAngleNativeDomain) ∧
      AnalyticOnNhd ℂ P.l2TerminalModelFourierRemainder U ∧ ∀ r ∈ U, ∀ k : ℤ,
        (P.l2TerminalModelFourierRemainder r).val k =
          (P.physicalSpectralCoreMap (periodOneL2Inclusion r)).val k -
            WeightedCoeff.halfFourierSymbol k * r k := by
  obtain ⟨V,hV,hqV,hVP,he⟩ := P.exists_retained_core_Dirac_identity_neighborhood H _ hq hr
  have hall : ∀ᶠ r in 𝓝 q,
      periodOneL2Inclusion r ∈ P.physicalDirichletSource ∩ hillHminusActionAngleNativeDomain ∧
      AnalyticAt ℂ P.l2TerminalModelFourierRemainder r ∧ ∀ k : ℤ,
        (P.l2TerminalModelFourierRemainder r).val k =
          (P.physicalSpectralCoreMap (periodOneL2Inclusion r)).val k -
            WeightedCoeff.halfFourierSymbol k * r k :=
    ((eventually_L2_open q V hV hqV).and (P.eventually_l2TerminalModelFourierRemainder_data q hq hr)).mono
      (fun r h => ⟨hVP _ h.1,h.2.1,fun k => P.core_raw_of_model r k (he _ h.1) (h.2.2 k)⟩)
  obtain ⟨U,hUsub,hU,hqU⟩ := _root_.mem_nhds_iff.mp hall
  exact ⟨U,hU,hqU,fun r hrU => (hUsub hrU).1,fun r hrU => (hUsub hrU).2.1,
    fun r hrU => (hUsub hrU).2.2⟩

private theorem sobolev_one_ge_one (k : ℤ) : 1 ≤ Weight.sobolev 1 k := by
  simp only [Weight.sobolev_apply,Real.rpow_one]
  linarith [abs_nonneg (k : ℝ)]

private theorem analytic_exp_of_exponent (P : HillProductEquationPatch) (r : Coeff 2)
    (h : AnalyticAt ℂ P.l2OnIndexSobolevExponent r) : AnalyticAt ℂ P.l2OnIndexExponentialRemainder r :=
  (WeightedCoeff.analyticAt_weightedExpRemainder (Weight.sobolev 1) sobolev_one_ge_one _).comp h

private theorem exp_raw_of_exponent_raw (P : HillProductEquationPatch) (r : Coeff 2) (k : ℤ)
    (h : (P.l2OnIndexSobolevExponent r).val k = P.physicalOnIndexSignedExponent (periodOneL2Inclusion r) k) :
    (P.l2OnIndexExponentialRemainder r).val k =
      Complex.exp (P.physicalOnIndexSignedExponent (periodOneL2Inclusion r) k) - 1 := by
  rw [l2OnIndexExponentialRemainder,WeightedCoeff.weightedExpRemainder_apply _ sobolev_one_ge_one,h]

theorem exists_retained_l2Core_onIndex_data (P : HillProductEquationPatch)
    (H : SourceLemma12_12Data (by norm_num) (by norm_num) P.parent.family.originalDomain
      P.parent.family.domain P.parent.family.roots)
    (q : Coeff 2) (hq : periodOneL2Inclusion q ∈ P.source)
    (hr : IsRealPeriodOneHminusOne (periodOneL2Inclusion q)) :
    ∃ U : Set (Coeff 2), IsOpen U ∧ q ∈ U ∧
      (∀ r ∈ U, periodOneL2Inclusion r ∈ P.physicalDirichletSource ∩ hillHminusActionAngleNativeDomain) ∧
      AnalyticOnNhd ℂ P.l2TerminalModelFourierRemainder U ∧
      AnalyticOnNhd ℂ P.l2OnIndexExponentialRemainder U ∧ ∀ r ∈ U, ∀ k : ℤ,
        (P.l2TerminalModelFourierRemainder r).val k =
          (P.physicalSpectralCoreMap (periodOneL2Inclusion r)).val k - WeightedCoeff.halfFourierSymbol k * r k ∧
        (P.l2OnIndexExponentialRemainder r).val k =
          Complex.exp (P.physicalOnIndexSignedExponent (periodOneL2Inclusion r) k) - 1 := by
  obtain ⟨Uc,hUc,hqUc,hUcP,hRc,hrawc⟩ := P.exists_retained_l2Core_smoothing H q hq hr
  obtain ⟨Up,hUp,hqUp,_,_,_,hEp,hrawp⟩ :=
    P.exists_local_l2OnIndexSobolevExponent_data H q (hUcP q hqUc).1 hr
  exact ⟨Uc ∩ Up,hUc.inter hUp,⟨hqUc,hqUp⟩,fun r hrU => hUcP r hrU.1,
    fun r hrU => hRc r hrU.1,fun r hrU => P.analytic_exp_of_exponent r (hEp r hrU.2),
    fun r hrU k => ⟨hrawc r hrU.1 k,P.exp_raw_of_exponent_raw r k ((hrawp r hrU.2).2 k)⟩⟩

def l2StrongSpectralCore (P : HillProductEquationPatch) (q : Coeff 2) :
    WeightedCoeff (Weight.signedSobolev (1/2)) 2 :=
  WeightedCoeff.l2FreeHalfFourier q +
    WeightedCoeff.signedOrderInclusion (1/2) (3/2) (by norm_num) 2 (P.l2TerminalModelFourierRemainder q)

theorem analytic_l2StrongSpectralCore (P : HillProductEquationPatch) (q : Coeff 2)
    (h : AnalyticAt ℂ P.l2TerminalModelFourierRemainder q) : AnalyticAt ℂ P.l2StrongSpectralCore q :=
  (WeightedCoeff.l2FreeHalfFourier.analyticAt q).add
    (((WeightedCoeff.signedOrderInclusion (1/2) (3/2) (by norm_num) 2).analyticAt _).comp h)

theorem l2StrongSpectralCore_apply_of_remainder (P : HillProductEquationPatch) (q : Coeff 2) (k : ℤ)
    (h : (P.l2TerminalModelFourierRemainder q).val k =
      (P.physicalSpectralCoreMap (periodOneL2Inclusion q)).val k - WeightedCoeff.halfFourierSymbol k * q k) :
    (P.l2StrongSpectralCore q).val k = (P.physicalSpectralCoreMap (periodOneL2Inclusion q)).val k := by
  simp only [l2StrongSpectralCore,WeightedCoeff.add_val,WeightedCoeff.l2FreeHalfFourier_apply,
    WeightedCoeff.signedOrderInclusion_apply,h]
  ring

end NLS.KdV.HillProductEquationPatch
