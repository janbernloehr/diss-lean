import NLS.KdV.HillMiuraH2TerminalFourier
import NLS.KdV.HillL2MassivePrincipalSmoothing
import NLS.KdV.HillRotatedDiracL2Regularity
import NLS.ZakharovShabat.SourceHillH1TerminalOneSmoothing

/-! The SAME actual Hill terminal model minus the article's free
half-Fourier transform is analytic from L2 to native signed H3/2.
The three explicit terms are the spectral defect, the actual Miura
H2 remainder and the already normalized massive principal correction. -/
noncomputable section
open Set Complex Filter Topology NLS.ZakharovShabat
namespace NLS.KdV.HillProductEquationPatch

def l2MiuraTerminalRemainder (P : HillProductEquationPatch) (q : Coeff 2) :
    WeightedCoeff (Weight.signedSobolev (3/2)) 2 :=
  hillMiuraH2TerminalFourier (P.parent.parent.miuraBall.actionBall.l2SmoothingRemainder q)

private theorem analytic_Miura_term (P : HillProductEquationPatch) (q : Coeff 2)
    (hq : periodOneL2Inclusion q ∈ P.source) : AnalyticAt ℂ P.l2MiuraTerminalRemainder q :=
  (hillMiuraH2TerminalFourier.analyticAt _).comp
    (P.parent.parent.miuraBall.actionBall.analytic_l2SmoothingRemainder q
      (P.parent.subset (P.subset hq)).1)

private theorem nonzero_Miura_difference (P : HillProductEquationPatch) (q : Coeff 2)
    (hq : periodOneL2Inclusion q ∈ P.source) (j : ℤ) (hj : j ≠ 0) :
    P.parent.parent.miuraBall.actionBall.lift (periodOneL2Inclusion q) j -
      periodOneMassInverse 0 (periodOneL2Inclusion q) j =
        (P.parent.parent.miuraBall.actionBall.l2SmoothingRemainder q).val j := by
  rw [P.parent.parent.miuraBall.actionBall.l2SmoothingRemainder_apply q
    (P.parent.subset (P.subset hq)).1 j, periodOneMassInverse_apply, periodOneL2Inclusion_apply]
  simp only [HillHminusMiuraActionBall.l2Forcing, lp.coeFn_add, Pi.add_apply,
    lp.single_apply, Pi.single_apply, if_neg hj, add_zero]

theorem l2MiuraTerminalRemainder_apply (P : HillProductEquationPatch) (q : Coeff 2)
    (hq : periodOneL2Inclusion q ∈ P.source) (k : ℤ) :
    (P.l2MiuraTerminalRemainder q).val k =
      (sourceHillTerminalFourier (P.rotatedDiracSource (periodOneL2Inclusion q))).val k -
        (hillSpectralCoreDiracPrincipal (periodOneL2Inclusion q)).val k :=
  hillMiuraH2TerminalFourier_eq_difference _ _ _ (P.nonzero_Miura_difference q hq) k

def l2TerminalModelFourierRemainder (P : HillProductEquationPatch) (q : Coeff 2) :
    WeightedCoeff (Weight.signedSobolev (3/2)) 2 :=
  sourceHillH1TerminalRemainder (P.rotatedDiracL2Lift q) + P.l2MiuraTerminalRemainder q +
    hillL2PrincipalFourierRemainder q

private theorem real_H1_rotated (P : HillProductEquationPatch) (q : Coeff 2)
    (hq : periodOneL2Inclusion q ∈ P.source)
    (hr : IsRealPeriodOneHminusOne (periodOneL2Inclusion q)) :
    IsRealType (CoeffPair.toMax 2 (sobolevSourceInclusion (P.rotatedDiracL2Lift q))) := by
  rw [P.sobolevSourceInclusion_rotatedDiracL2Lift q hq]
  exact P.isRealType_rotatedDiracSource _ hq hr

private theorem H1_model_domain (P : HillProductEquationPatch) (q : Coeff 2)
    (hq : periodOneL2Inclusion q ∈ P.source)
    (hr : IsRealPeriodOneHminusOne (periodOneL2Inclusion q)) :
    ∃ V : Set (ScalarDomain 2 × ScalarDomain 2), IsOpen V ∧ P.rotatedDiracL2Lift q ∈ V ∧
      AnalyticOnNhd ℂ sourceHillH1TerminalRemainder V ∧
      ∀ a ∈ V, ∀ k : ℤ, (sourceHillH1TerminalRemainder a).val k =
        (sourceHillTerminalModel (sobolevSourceInclusion a)).val k -
          (sourceHillTerminalFourier (sobolevSourceInclusion a)).val k :=
  exists_local_sourceHillH1TerminalRemainder_analytic
    ⟨P.rotatedDiracL2Lift q,P.real_H1_rotated q hq hr⟩

private theorem analytic_spectral_term (P : HillProductEquationPatch) (q : Coeff 2)
    (hq : periodOneL2Inclusion q ∈ P.source)
    (hr : IsRealPeriodOneHminusOne (periodOneL2Inclusion q)) :
    AnalyticAt ℂ (fun r : Coeff 2 => sourceHillH1TerminalRemainder (P.rotatedDiracL2Lift r)) q := by
  obtain ⟨V,_,hqV,hVa,_⟩ := P.H1_model_domain q hq hr
  exact (hVa _ hqV).comp (f := P.rotatedDiracL2Lift) (P.analytic_rotatedDiracL2Lift q hq)

theorem analytic_l2TerminalModelFourierRemainder (P : HillProductEquationPatch) (q : Coeff 2)
    (hq : periodOneL2Inclusion q ∈ P.source)
    (hr : IsRealPeriodOneHminusOne (periodOneL2Inclusion q)) :
    AnalyticAt ℂ P.l2TerminalModelFourierRemainder q :=
  ((P.analytic_spectral_term q hq hr).add (P.analytic_Miura_term q hq)).add
    (hillL2PrincipalFourierRemainder.analyticAt q)

private theorem model_raw_identity (P : HillProductEquationPatch) (r : Coeff 2)
    (hrP : periodOneL2Inclusion r ∈ P.source) (k : ℤ)
    (h : (sourceHillH1TerminalRemainder (P.rotatedDiracL2Lift r)).val k =
      (sourceHillTerminalModel (sobolevSourceInclusion (P.rotatedDiracL2Lift r))).val k -
        (sourceHillTerminalFourier (sobolevSourceInclusion (P.rotatedDiracL2Lift r))).val k) :
    (P.l2TerminalModelFourierRemainder r).val k =
      (sourceHillTerminalModel (P.rotatedDiracSource (periodOneL2Inclusion r))).val k -
        WeightedCoeff.halfFourierSymbol k * r k := by
  have hm := h.trans (congrArg (fun ψ : CoeffPair 2 => (sourceHillTerminalModel ψ).val k -
    (sourceHillTerminalFourier ψ).val k) (P.sobolevSourceInclusion_rotatedDiracL2Lift r hrP))
  change (sourceHillH1TerminalRemainder (P.rotatedDiracL2Lift r)).val k +
    (P.l2MiuraTerminalRemainder r).val k + (hillL2PrincipalFourierRemainder r).val k = _
  rw [hm,P.l2MiuraTerminalRemainder_apply r hrP k,hillL2PrincipalFourierRemainder_eq_actual]
  ring

private theorem eventually_in_source (P : HillProductEquationPatch) (q : Coeff 2)
    (hq : periodOneL2Inclusion q ∈ P.source) :
    ∀ᶠ r in 𝓝 q, periodOneL2Inclusion r ∈ P.source :=
  periodOneL2Inclusion.continuous.continuousAt.tendsto.eventually (P.source_open.mem_nhds hq)

private theorem eventually_in_H1_domain (P : HillProductEquationPatch) (q : Coeff 2)
    (hq : periodOneL2Inclusion q ∈ P.source) (V : Set (ScalarDomain 2 × ScalarDomain 2))
    (hV : IsOpen V) (hqV : P.rotatedDiracL2Lift q ∈ V) :
    ∀ᶠ r in 𝓝 q, P.rotatedDiracL2Lift r ∈ V :=
  (P.analytic_rotatedDiracL2Lift q hq).continuousAt.tendsto.eventually (hV.mem_nhds hqV)

private theorem analytic_model_of_mem (P : HillProductEquationPatch)
    (V : Set (ScalarDomain 2 × ScalarDomain 2)) (hVa : AnalyticOnNhd ℂ sourceHillH1TerminalRemainder V)
    (r : Coeff 2) (hrP : periodOneL2Inclusion r ∈ P.source) (hrV : P.rotatedDiracL2Lift r ∈ V) :
    AnalyticAt ℂ P.l2TerminalModelFourierRemainder r :=
  (((hVa _ hrV).comp (f := P.rotatedDiracL2Lift) (P.analytic_rotatedDiracL2Lift r hrP)).add
    (P.analytic_Miura_term r hrP)).add (hillL2PrincipalFourierRemainder.analyticAt r)

theorem eventually_l2TerminalModelFourierRemainder_data (P : HillProductEquationPatch)
    (q : Coeff 2) (hq : periodOneL2Inclusion q ∈ P.source)
    (hr : IsRealPeriodOneHminusOne (periodOneL2Inclusion q)) :
    ∀ᶠ r in 𝓝 q, AnalyticAt ℂ P.l2TerminalModelFourierRemainder r ∧ ∀ k : ℤ,
      (P.l2TerminalModelFourierRemainder r).val k =
        (sourceHillTerminalModel (P.rotatedDiracSource (periodOneL2Inclusion r))).val k -
          WeightedCoeff.halfFourierSymbol k * r k := by
  obtain ⟨V,hV,hqV,hVa,hVc⟩ := P.H1_model_domain q hq hr
  exact ((P.eventually_in_source q hq).and (P.eventually_in_H1_domain q hq V hV hqV)).mono
    (fun r h => ⟨P.analytic_model_of_mem V hVa r h.1 h.2,
      fun k => P.model_raw_identity r h.1 k (hVc _ h.2 k)⟩)

theorem eventually_l2TerminalModelFourierRemainder_apply (P : HillProductEquationPatch)
    (q : Coeff 2) (hq : periodOneL2Inclusion q ∈ P.source)
    (hr : IsRealPeriodOneHminusOne (periodOneL2Inclusion q)) :
    ∀ᶠ r in 𝓝 q, ∀ k : ℤ, (P.l2TerminalModelFourierRemainder r).val k =
      (sourceHillTerminalModel (P.rotatedDiracSource (periodOneL2Inclusion r))).val k -
        WeightedCoeff.halfFourierSymbol k * r k := by
  exact (P.eventually_l2TerminalModelFourierRemainder_data q hq hr).mono (fun _ h => h.2)

end NLS.KdV.HillProductEquationPatch
