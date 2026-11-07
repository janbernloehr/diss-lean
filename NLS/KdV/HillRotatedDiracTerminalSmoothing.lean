import NLS.KdV.HillRotatedDiracL2Regularity
import NLS.ZakharovShabat.SourceSignedTerminalOneSmoothing

/-! The literal signed terminal Fourier defect of the actual Hill
rotated source is analytic in H2 on a complex L2 neighborhood of each
real source in the patch. All raw coefficients are identified. -/
noncomputable section
open Set Complex Filter Topology NLS.ZakharovShabat
namespace NLS.KdV.HillProductEquationPatch

def l2TerminalFourierRemainder (P : HillProductEquationPatch) (q : Coeff 2) :
    WeightedCoeff (Weight.sobolev (((1 : ℕ) : ℝ) + 1)) 2 :=
  sourceSignedTerminalFourierRemainder 1
    (higherSobolevSourceOneEquiv (P.rotatedDiracL2Lift q))

private theorem analytic_l2SobolevDiracSource (P : HillProductEquationPatch) (q : Coeff 2)
    (hq : periodOneL2Inclusion q ∈ P.source) :
    AnalyticAt ℂ (fun r : Coeff 2 => higherSobolevSourceOneEquiv (P.rotatedDiracL2Lift r)) q :=
  (higherSobolevSourceOneEquiv.analyticAt _).comp (P.analytic_rotatedDiracL2Lift q hq)

private theorem l2SobolevDiracSource_image (P : HillProductEquationPatch) (r : Coeff 2)
    (hrP : periodOneL2Inclusion r ∈ P.source) :
    higherSobolevSourceInclusion 1 (higherSobolevSourceOneEquiv (P.rotatedDiracL2Lift r)) =
      P.rotatedDiracSource (periodOneL2Inclusion r) :=
  (higherSobolevSourceInclusion_one (P.rotatedDiracL2Lift r)).trans
    (P.sobolevSourceInclusion_rotatedDiracL2Lift r hrP)

private theorem real_l2SobolevDiracSource (P : HillProductEquationPatch) (q : Coeff 2)
    (hq : periodOneL2Inclusion q ∈ P.source)
    (hr : IsRealPeriodOneHminusOne (periodOneL2Inclusion q)) :
    IsRealType (CoeffPair.toMax 2 (higherSobolevSourceInclusion 1
      (higherSobolevSourceOneEquiv (P.rotatedDiracL2Lift q)))) := by
  rw [P.l2SobolevDiracSource_image q hq]
  exact P.isRealType_rotatedDiracSource _ hq hr

private theorem local_terminal_domain (P : HillProductEquationPatch) (q : Coeff 2)
    (hq : periodOneL2Inclusion q ∈ P.source)
    (hr : IsRealPeriodOneHminusOne (periodOneL2Inclusion q)) :
    ∃ V : Set (SobolevSource 1), IsOpen V ∧
      higherSobolevSourceOneEquiv (P.rotatedDiracL2Lift q) ∈ V ∧
      AnalyticOnNhd ℂ (sourceSignedTerminalFourierRemainder 1) V ∧
      ∀ b ∈ V, ∀ k : ℤ, (sourceSignedTerminalFourierRemainder 1 b).val k =
        sourceSignedTerminalSequence (higherSobolevSourceInclusion 1 b) k -
          sourceSignedTerminalFourier (higherSobolevSourceInclusion 1 b) k :=
  exists_local_sourceSignedTerminalFourierRemainder_analytic 1 (by norm_num)
    ⟨higherSobolevSourceOneEquiv (P.rotatedDiracL2Lift q),P.real_l2SobolevDiracSource q hq hr⟩

theorem analytic_l2TerminalFourierRemainder (P : HillProductEquationPatch)
    (q : Coeff 2) (hq : periodOneL2Inclusion q ∈ P.source)
    (hr : IsRealPeriodOneHminusOne (periodOneL2Inclusion q)) :
    AnalyticAt ℂ P.l2TerminalFourierRemainder q := by
  obtain ⟨V,_,hqV,hVa,_⟩ := P.local_terminal_domain q hq hr
  exact (hVa _ hqV).comp
    (f := fun r : Coeff 2 => higherSobolevSourceOneEquiv (P.rotatedDiracL2Lift r))
    (P.analytic_l2SobolevDiracSource q hq)

private theorem terminal_raw_identity (P : HillProductEquationPatch) (r : Coeff 2)
    (hrP : periodOneL2Inclusion r ∈ P.source) (k : ℤ)
    (h : (sourceSignedTerminalFourierRemainder 1
      (higherSobolevSourceOneEquiv (P.rotatedDiracL2Lift r))).val k =
        sourceSignedTerminalSequence (higherSobolevSourceInclusion 1
          (higherSobolevSourceOneEquiv (P.rotatedDiracL2Lift r))) k -
        sourceSignedTerminalFourier (higherSobolevSourceInclusion 1
          (higherSobolevSourceOneEquiv (P.rotatedDiracL2Lift r))) k) :
    (P.l2TerminalFourierRemainder r).val k =
      sourceSignedTerminalSequence (P.rotatedDiracSource (periodOneL2Inclusion r)) k -
        sourceSignedTerminalFourier (P.rotatedDiracSource (periodOneL2Inclusion r)) k :=
  h.trans (congrArg (fun ψ : CoeffPair 2 =>
    sourceSignedTerminalSequence ψ k - sourceSignedTerminalFourier ψ k)
      (P.l2SobolevDiracSource_image r hrP))

private theorem eventually_l2_source (P : HillProductEquationPatch) (q : Coeff 2)
    (hq : periodOneL2Inclusion q ∈ P.source) :
    ∀ᶠ r in 𝓝 q, periodOneL2Inclusion r ∈ P.source :=
  periodOneL2Inclusion.continuous.continuousAt.tendsto.eventually (P.source_open.mem_nhds hq)

private theorem eventually_l2Sobolev_mem (P : HillProductEquationPatch) (q : Coeff 2)
    (hq : periodOneL2Inclusion q ∈ P.source) (V : Set (SobolevSource 1)) (hV : IsOpen V)
    (hqV : higherSobolevSourceOneEquiv (P.rotatedDiracL2Lift q) ∈ V) :
    ∀ᶠ r in 𝓝 q, higherSobolevSourceOneEquiv (P.rotatedDiracL2Lift r) ∈ V :=
  (P.analytic_l2SobolevDiracSource q hq).continuousAt.tendsto.eventually (hV.mem_nhds hqV)

theorem eventually_l2TerminalFourierRemainder_apply (P : HillProductEquationPatch)
    (q : Coeff 2) (hq : periodOneL2Inclusion q ∈ P.source)
    (hr : IsRealPeriodOneHminusOne (periodOneL2Inclusion q)) :
    ∀ᶠ r in 𝓝 q, ∀ k : ℤ, (P.l2TerminalFourierRemainder r).val k =
      sourceSignedTerminalSequence (P.rotatedDiracSource (periodOneL2Inclusion r)) k -
        sourceSignedTerminalFourier (P.rotatedDiracSource (periodOneL2Inclusion r)) k := by
  obtain ⟨V,hV,hqV,_,hVc⟩ := P.local_terminal_domain q hq hr
  exact ((P.eventually_l2_source q hq).and (P.eventually_l2Sobolev_mem q hq V hV hqV)).mono
    (fun r h k => P.terminal_raw_identity r h.1 k (hVc _ h.2 k))

end NLS.KdV.HillProductEquationPatch
