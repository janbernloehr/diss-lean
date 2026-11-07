import NLS.KdV.HillRotatedDiracFractionalWeight
import NLS.KdV.HillRetainedSpectralCoreDiracIdentity
import NLS.ZakharovShabat.SourceFractionalHillTerminal
import NLS.SequenceSpaces.SignedOrderLinearInclusions

/-! The actual retained Hill spectral core, analytic in its full
fractional signed Hilbert target at every original real rough source. -/
noncomputable section
open Set Complex Filter Topology NLS.WeightedCoeff NLS.ZakharovShabat
namespace NLS.KdV.HillProductEquationPatch

def fractionalSpectralCore (P : HillProductEquationPatch) (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (q : WeightedCoeff (Weight.sobolev (-r)) 2) : WeightedCoeff (Weight.signedSobolev (1/2-r)) 2 :=
  signedOrderInclusion (1/2-r) ((1-r)-1/2) (by linarith) 2
    (sourceFractionalHillTerminal (1-r) (by linarith) (P.rotatedDiracFractionalWeightCoordinates r hr hr1 q))

private theorem fractionalCore_raw_of_data (P : HillProductEquationPatch)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) (q : WeightedCoeff (Weight.sobolev (-r)) 2)
    (hq : sobolevInclusion (show (-1:ℝ) ≤ -r by linarith) q ∈ P.source)
    (hcore : P.physicalSpectralCoreMap (sobolevInclusion (show (-1:ℝ) ≤ -r by linarith) q) =
      sourceHillTerminalModel (P.rotatedDiracSource (sobolevInclusion (show (-1:ℝ) ≤ -r by linarith) q)))
    (hterm : ∀ k, (sourceFractionalHillTerminal (1-r) (by linarith)
        (P.rotatedDiracFractionalWeightCoordinates r hr hr1 q)).val k =
      (sourceHillTerminalModel (normalizedWeightedSource (sourceSobolevSpectralWeight (1-r) (by linarith))
        (P.rotatedDiracFractionalWeightCoordinates r hr hr1 q))).val k) (k : ℤ) :
    (P.fractionalSpectralCore r hr hr1 q).val k =
      (P.physicalSpectralCoreMap (sobolevInclusion (show (-1:ℝ) ≤ -r by linarith) q)).val k := by
  rw [fractionalSpectralCore,signedOrderInclusion_apply,hterm,
    P.rotatedDiracFractionalWeightCoordinates_decode r hr hr1 q hq,← hcore]

theorem exists_retained_fractionalSpectralCore_analytic
    (P : HillProductEquationPatch)
    (H : SourceLemma12_12Data (by norm_num) (by norm_num) P.parent.family.originalDomain
      P.parent.family.domain P.parent.family.roots)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) (q : WeightedCoeff (Weight.sobolev (-r)) 2)
    (hq : sobolevInclusion (show (-1:ℝ) ≤ -r by linarith) q ∈ P.source)
    (hqreal : IsRealPeriodOneHminusOne (sobolevInclusion (show (-1:ℝ) ≤ -r by linarith) q)) :
    ∃ U : Set (WeightedCoeff (Weight.sobolev (-r)) 2), IsOpen U ∧ q ∈ U ∧
      (∀ a ∈ U, sobolevInclusion (show (-1:ℝ) ≤ -r by linarith) a ∈
        P.physicalDirichletSource ∩ hillHminusActionAngleNativeDomain) ∧
      AnalyticOnNhd ℂ (P.fractionalSpectralCore r hr hr1) U ∧
      ∀ a ∈ U, ∀ k, (P.fractionalSpectralCore r hr hr1 a).val k =
        (P.physicalSpectralCoreMap (sobolevInclusion (show (-1:ℝ) ≤ -r by linarith) a)).val k := by
  let T : WeightedCoeff (Weight.sobolev (-r)) 2 →L[ℂ] PeriodOneHminusOne :=
    sobolevInclusion (show (-1:ℝ) ≤ -r by linarith)
  obtain ⟨V,hV,hqV,hVP,hmodel⟩ := P.exists_retained_core_Dirac_identity_neighborhood H (T q) hq hqreal
  let φ : realTypeSourceLocus 2 := ⟨P.rotatedDiracFractionalWeightCoordinates r hr hr1 q,
    P.rotatedDiracFractionalWeightCoordinates_real r hr hr1 q hq hqreal⟩
  obtain ⟨W,hW,hφW,hWa,hWc⟩ := exists_local_sourceFractionalHillTerminal_analytic
    (1-r) (by linarith) φ
  have haφ := P.analytic_rotatedDiracFractionalWeightCoordinates r hr hr1 q hq
  have hevent : ∀ᶠ a in 𝓝 q, T a ∈ V ∧ P.rotatedDiracFractionalWeightCoordinates r hr hr1 a ∈ W :=
    (T.continuous.continuousAt.tendsto.eventually (hV.mem_nhds hqV)).and
      (haφ.continuousAt.tendsto.eventually (hW.mem_nhds hφW))
  obtain ⟨U,hUsub,hU,hqU⟩ := _root_.mem_nhds_iff.mp hevent
  refine ⟨U,hU,hqU,fun a ha => hVP (T a) (hUsub ha).1,?_,?_⟩
  · intro a ha
    have hsrc : T a ∈ P.source := (hVP (T a) (hUsub ha).1).1.1
    have ht := (hWa _ (hUsub ha).2).comp
      (P.analytic_rotatedDiracFractionalWeightCoordinates r hr hr1 a hsrc)
    exact ((signedOrderInclusion (1/2-r) ((1-r)-1/2) (by linarith) 2).analyticAt _).comp ht
  · intro a ha k
    exact P.fractionalCore_raw_of_data r hr hr1 a (hVP (T a) (hUsub ha).1).1.1
      (hmodel (T a) (hUsub ha).1) (hWc _ (hUsub ha).2) k

end NLS.KdV.HillProductEquationPatch
