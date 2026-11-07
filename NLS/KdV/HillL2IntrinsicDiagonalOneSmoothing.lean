import NLS.KdV.HillRetainedL2CoreOnIndexData
import NLS.SequenceSpaces.WeightedInfinityPointwiseProduct

/-! Restore the ACTUAL on-index phase on the SAME retained spectral
core. The intrinsic diagonal map minus the ORIGINAL half-Fourier map
has an analytic native H3/2 realization on a common complex L2 source
neighborhood of every real potential. -/
noncomputable section
open Set Complex NLS.ZakharovShabat
namespace NLS.KdV.HillProductEquationPatch

theorem intrinsicDiagonalMap_from_physicalCore (P : HillProductEquationPatch) (q : PeriodOneHminusOne) :
    hillHminusIntrinsicDiagonalMap q =
      WeightedCoeff.exponentialSymbolEquiv (Weight.signedSobolev (-1/2))
        (P.physicalOnIndexSignedExponent q) (P.physicalSpectralCoreMap q) := by
  change hillHminusIntrinsicDiagonalMap q =
    (WeightedCoeff.exponentialSymbolEquiv _ (P.physicalOnIndexSignedExponent q))
      ((WeightedCoeff.exponentialSymbolEquiv _ (P.physicalOnIndexSignedExponent q)).symm
        (hillHminusIntrinsicDiagonalMap q))
  exact ((WeightedCoeff.exponentialSymbolEquiv _ _).apply_symm_apply _).symm

private theorem intrinsic_from_core_apply (P : HillProductEquationPatch) (q : PeriodOneHminusOne) (k : ℤ) :
    (hillHminusIntrinsicDiagonalMap q).val k = Complex.exp (P.physicalOnIndexSignedExponent q k) *
      (P.physicalSpectralCoreMap q).val k := by
  rw [P.intrinsicDiagonalMap_from_physicalCore q,WeightedCoeff.exponentialSymbolEquiv_apply]

def l2IntrinsicDiagonalFourierRemainder (P : HillProductEquationPatch) (q : Coeff 2) :
    WeightedCoeff (Weight.signedSobolev (3/2)) 2 :=
  P.l2TerminalModelFourierRemainder q + WeightedCoeff.signedSobolevInfinityProduct (1/2) (3/2)
    (by norm_num) (P.l2OnIndexExponentialRemainder q) (P.l2StrongSpectralCore q)

private theorem analytic_intrinsic_remainder_of_data (P : HillProductEquationPatch) (q : Coeff 2)
    (hc : AnalyticAt ℂ P.l2TerminalModelFourierRemainder q)
    (he : AnalyticAt ℂ P.l2OnIndexExponentialRemainder q) :
    AnalyticAt ℂ P.l2IntrinsicDiagonalFourierRemainder q := by
  have hp : AnalyticAt ℂ (fun r : Coeff 2 => WeightedCoeff.signedSobolevInfinityProduct (1/2) (3/2)
      (by norm_num) (P.l2OnIndexExponentialRemainder r) (P.l2StrongSpectralCore r)) q :=
    (WeightedCoeff.analyticAt_signedSobolevInfinityProduct (1/2) (3/2) (by norm_num) _).comp
      (f := fun r : Coeff 2 => (P.l2OnIndexExponentialRemainder r,P.l2StrongSpectralCore r))
        (he.prod (P.analytic_l2StrongSpectralCore q hc))
  exact hc.add hp

private theorem intrinsic_remainder_raw_of_data (P : HillProductEquationPatch) (q : Coeff 2) (k : ℤ)
    (hc : (P.l2TerminalModelFourierRemainder q).val k =
      (P.physicalSpectralCoreMap (periodOneL2Inclusion q)).val k - WeightedCoeff.halfFourierSymbol k * q k)
    (he : (P.l2OnIndexExponentialRemainder q).val k =
      Complex.exp (P.physicalOnIndexSignedExponent (periodOneL2Inclusion q) k) - 1) :
    (P.l2IntrinsicDiagonalFourierRemainder q).val k =
      (hillHminusIntrinsicDiagonalMap (periodOneL2Inclusion q)).val k - WeightedCoeff.halfFourierSymbol k * q k := by
  simp only [l2IntrinsicDiagonalFourierRemainder,WeightedCoeff.add_val,
    WeightedCoeff.signedSobolevInfinityProduct_apply,he,P.l2StrongSpectralCore_apply_of_remainder q k hc,hc]
  rw [P.intrinsic_from_core_apply]
  ring

theorem exists_retained_l2IntrinsicDiagonal_one_smoothing (P : HillProductEquationPatch)
    (H : SourceLemma12_12Data (by norm_num) (by norm_num) P.parent.family.originalDomain
      P.parent.family.domain P.parent.family.roots)
    (q : Coeff 2) (hq : periodOneL2Inclusion q ∈ P.source)
    (hr : IsRealPeriodOneHminusOne (periodOneL2Inclusion q)) :
    ∃ U : Set (Coeff 2), IsOpen U ∧ q ∈ U ∧
      (∀ r ∈ U, periodOneL2Inclusion r ∈ P.physicalDirichletSource ∩ hillHminusActionAngleNativeDomain) ∧
      AnalyticOnNhd ℂ P.l2IntrinsicDiagonalFourierRemainder U ∧ ∀ r ∈ U, ∀ k : ℤ,
        (P.l2IntrinsicDiagonalFourierRemainder r).val k =
          (hillHminusIntrinsicDiagonalMap (periodOneL2Inclusion r)).val k - WeightedCoeff.halfFourierSymbol k * r k := by
  obtain ⟨U,hU,hqU,hUP,hc,he,hraw⟩ := P.exists_retained_l2Core_onIndex_data H q hq hr
  exact ⟨U,hU,hqU,hUP,fun r hrU => P.analytic_intrinsic_remainder_of_data r (hc r hrU) (he r hrU),
    fun r hrU k => P.intrinsic_remainder_raw_of_data r k (hraw r hrU k).1 (hraw r hrU k).2⟩

end NLS.KdV.HillProductEquationPatch
namespace NLS.KdV

theorem exists_hillL2IntrinsicDiagonal_one_smoothing (q : Coeff 2)
    (hr : IsRealPeriodOneHminusOne (periodOneL2Inclusion q)) :
    ∃ P : HillProductEquationPatch, ∃ U : Set (Coeff 2), IsOpen U ∧ q ∈ U ∧
      (∀ r ∈ U, periodOneL2Inclusion r ∈ P.physicalDirichletSource ∩ hillHminusActionAngleNativeDomain) ∧
      AnalyticOnNhd ℂ P.l2IntrinsicDiagonalFourierRemainder U ∧ ∀ r ∈ U, ∀ k : ℤ,
        (P.l2IntrinsicDiagonalFourierRemainder r).val k =
          (hillHminusIntrinsicDiagonalMap (periodOneL2Inclusion r)).val k - WeightedCoeff.halfFourierSymbol k * r k := by
  obtain ⟨A,H⟩ := exists_miuraHillPsiFamily_with_original_estimates
  obtain ⟨P,hqP,_,hPA⟩ := exists_hillProductEquationPatch_with_family A (periodOneL2Inclusion q) hr
  have HP : SourceLemma12_12Data (by norm_num) (by norm_num) P.parent.family.originalDomain
      P.parent.family.domain P.parent.family.roots := by rw [hPA]; exact H
  obtain ⟨U,hU,hqU,hUP,ha,hraw⟩ := P.exists_retained_l2IntrinsicDiagonal_one_smoothing HP q hqP hr
  exact ⟨P,U,hU,hqU,hUP,ha,hraw⟩

end NLS.KdV
