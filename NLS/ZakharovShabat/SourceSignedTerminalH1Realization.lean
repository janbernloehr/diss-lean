import NLS.ZakharovShabat.SourceSignedTerminalOneSmoothing
import NLS.SequenceSpaces.WeightedMultiplier

/-! The literal signed terminal sequence, now analytically realized in
H1. The free signed Fourier operator retains the original components,
and its full nonlinear defect is the already proved H2 remainder. -/
noncomputable section
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat

def sourceSignedSobolevTerminalFourier :
    (ScalarDomain 2 × ScalarDomain 2) →L[ℂ] ScalarDomain 2 :=
  (WeightedCoeff.signedPositiveSplice (Weight.sobolev 1) 2).comp
    (((-2 : ℂ) • ContinuousLinearMap.snd ℂ (ScalarDomain 2) (ScalarDomain 2)).prod
      ((-2 : ℂ) • (WeightedCoeff.reflection 1).toContinuousLinearEquiv.toContinuousLinearMap.comp
        (ContinuousLinearMap.fst ℂ (ScalarDomain 2) (ScalarDomain 2))))

theorem sourceSignedSobolevTerminalFourier_apply (a : ScalarDomain 2 × ScalarDomain 2) (k : ℤ) :
    (sourceSignedSobolevTerminalFourier a).val k =
      sourceSignedTerminalFourier (sobolevSourceInclusion a) k := by
  rcases lt_trichotomy 0 k with hk | hk | hk
  · rw [sourceSignedTerminalFourier_positive _ k hk]
    change (WeightedCoeff.signedPositiveSplice (Weight.sobolev 1) 2
      ((-2 : ℂ) • a.2, (-2 : ℂ) • WeightedCoeff.reflection 1 a.1)).val k = _
    rw [WeightedCoeff.signedPositiveSplice_positive _ _ _ _ k hk]
    simp only [WeightedCoeff.smul_val, sobolevSourceInclusion_snd]
  · subst k
    rw [sourceSignedTerminalFourier_zero]
    change (WeightedCoeff.signedPositiveSplice (Weight.sobolev 1) 2
      ((-2 : ℂ) • a.2, (-2 : ℂ) • WeightedCoeff.reflection 1 a.1)).val 0 = 0
    exact WeightedCoeff.signedPositiveSplice_zero _ _ _ _
  · rw [sourceSignedTerminalFourier_negative _ k hk]
    change (WeightedCoeff.signedPositiveSplice (Weight.sobolev 1) 2
      ((-2 : ℂ) • a.2, (-2 : ℂ) • WeightedCoeff.reflection 1 a.1)).val k = _
    rw [WeightedCoeff.signedPositiveSplice_negative _ _ (Weight.sobolev_neg 1) _ _ k hk]
    simp only [WeightedCoeff.smul_val, WeightedCoeff.reflection_apply, neg_neg,
      sobolevSourceInclusion_fst]

def sourceSignedTerminalH2Remainder (a : ScalarDomain 2 × ScalarDomain 2) :
    WeightedCoeff (Weight.sobolev (1 + 1)) 2 :=
  WeightedCoeff.inclusionCLM _ _ (by intro k; norm_num)
    (sourceSignedTerminalFourierRemainder 1 (higherSobolevSourceOneEquiv a))

theorem sourceSignedTerminalH2Remainder_apply (a : ScalarDomain 2 × ScalarDomain 2) (k : ℤ) :
    (sourceSignedTerminalH2Remainder a).val k =
      (sourceSignedTerminalFourierRemainder 1 (higherSobolevSourceOneEquiv a)).val k :=
  WeightedCoeff.inclusionCLM_apply _ _ _ _ k

private def terminalH2ToH1 : WeightedCoeff (Weight.sobolev (1 + 1)) 2 →L[ℂ] ScalarDomain 2 :=
  WeightedCoeff.sobolevInclusion (by norm_num : (1 : ℝ) ≤ 1 + 1)

def sourceSignedTerminalH1Sequence (a : ScalarDomain 2 × ScalarDomain 2) : ScalarDomain 2 :=
  sourceSignedSobolevTerminalFourier a + terminalH2ToH1 (sourceSignedTerminalH2Remainder a)

theorem sourceSignedTerminalH1Sequence_apply (a : ScalarDomain 2 × ScalarDomain 2) (k : ℤ) :
    (sourceSignedTerminalH1Sequence a).val k =
      sourceSignedTerminalFourier (sobolevSourceInclusion a) k +
        (sourceSignedTerminalH2Remainder a).val k := by
  simp only [sourceSignedTerminalH1Sequence, WeightedCoeff.add_val,
    sourceSignedSobolevTerminalFourier_apply, terminalH2ToH1, WeightedCoeff.sobolevInclusion_apply]

private theorem real_one_source (a : realTypeSobolevSourceLocus) :
    IsRealType (CoeffPair.toMax 2 (higherSobolevSourceInclusion 1
      (higherSobolevSourceOneEquiv a.val))) := by
  rw [higherSobolevSourceInclusion_one]
  exact a.property

private theorem local_one_terminal_domain (a : realTypeSobolevSourceLocus) :
    ∃ V : Set (SobolevSource 1), IsOpen V ∧ higherSobolevSourceOneEquiv a.val ∈ V ∧
      AnalyticOnNhd ℂ (sourceSignedTerminalFourierRemainder 1) V ∧
      ∀ b ∈ V, ∀ k : ℤ, (sourceSignedTerminalFourierRemainder 1 b).val k =
        sourceSignedTerminalSequence (higherSobolevSourceInclusion 1 b) k -
          sourceSignedTerminalFourier (higherSobolevSourceInclusion 1 b) k :=
  exists_local_sourceSignedTerminalFourierRemainder_analytic 1 (by norm_num)
    ⟨higherSobolevSourceOneEquiv a.val,real_one_source a⟩

private theorem analytic_H2_on_domain (V : Set (SobolevSource 1))
    (hRa : AnalyticOnNhd ℂ (sourceSignedTerminalFourierRemainder 1) V)
    (b : ScalarDomain 2 × ScalarDomain 2) (hb : higherSobolevSourceOneEquiv b ∈ V) :
    AnalyticAt ℂ sourceSignedTerminalH2Remainder b :=
  ((WeightedCoeff.inclusionCLM (Weight.sobolev (((1 : ℕ) : ℝ) + 1))
    (Weight.sobolev (1 + 1)) (by intro k; norm_num) (p := 2)).analyticAt _).comp
      ((hRa _ hb).comp (f := higherSobolevSourceOneEquiv) (higherSobolevSourceOneEquiv.analyticAt b))

private theorem analytic_H1_of_H2 (b : ScalarDomain 2 × ScalarDomain 2)
    (hR : AnalyticAt ℂ sourceSignedTerminalH2Remainder b) :
    AnalyticAt ℂ sourceSignedTerminalH1Sequence b :=
  (sourceSignedSobolevTerminalFourier.analyticAt b).add ((terminalH2ToH1.analyticAt _).comp hR)

private theorem H2_raw_of_one_raw (b : ScalarDomain 2 × ScalarDomain 2) (k : ℤ)
    (h : (sourceSignedTerminalFourierRemainder 1 (higherSobolevSourceOneEquiv b)).val k =
      sourceSignedTerminalSequence (higherSobolevSourceInclusion 1 (higherSobolevSourceOneEquiv b)) k -
        sourceSignedTerminalFourier (higherSobolevSourceInclusion 1 (higherSobolevSourceOneEquiv b)) k) :
    (sourceSignedTerminalH2Remainder b).val k =
      sourceSignedTerminalSequence (sobolevSourceInclusion b) k -
        sourceSignedTerminalFourier (sobolevSourceInclusion b) k :=
  (sourceSignedTerminalH2Remainder_apply b k).trans
    (h.trans (congrArg (fun ψ : CoeffPair 2 => sourceSignedTerminalSequence ψ k -
      sourceSignedTerminalFourier ψ k) (higherSobolevSourceInclusion_one b)))

private theorem H1_raw_of_H2_raw (b : ScalarDomain 2 × ScalarDomain 2) (k : ℤ)
    (h : (sourceSignedTerminalH2Remainder b).val k =
      sourceSignedTerminalSequence (sobolevSourceInclusion b) k -
        sourceSignedTerminalFourier (sobolevSourceInclusion b) k) :
    (sourceSignedTerminalH1Sequence b).val k = sourceSignedTerminalSequence (sobolevSourceInclusion b) k := by
  rw [sourceSignedTerminalH1Sequence_apply,h]
  ring

private theorem eventually_in_one_domain (a : ScalarDomain 2 × ScalarDomain 2)
    (V : Set (SobolevSource 1)) (hV : IsOpen V) (haV : higherSobolevSourceOneEquiv a ∈ V) :
    ∀ᶠ b in nhds a, higherSobolevSourceOneEquiv b ∈ V :=
  higherSobolevSourceOneEquiv.continuous.continuousAt.tendsto.eventually (hV.mem_nhds haV)

private theorem eventually_H1_H2_realization (a : realTypeSobolevSourceLocus) :
    ∀ᶠ b in nhds a.val, AnalyticAt ℂ sourceSignedTerminalH2Remainder b ∧
      AnalyticAt ℂ sourceSignedTerminalH1Sequence b ∧ ∀ k : ℤ,
        (sourceSignedTerminalH2Remainder b).val k =
          sourceSignedTerminalSequence (sobolevSourceInclusion b) k -
            sourceSignedTerminalFourier (sobolevSourceInclusion b) k ∧
        (sourceSignedTerminalH1Sequence b).val k = sourceSignedTerminalSequence (sobolevSourceInclusion b) k := by
  obtain ⟨V,hV,haV,hRa,hRc⟩ := local_one_terminal_domain a
  exact (eventually_in_one_domain a.val V hV haV).mono (fun b hb =>
    ⟨analytic_H2_on_domain V hRa b hb,analytic_H1_of_H2 b (analytic_H2_on_domain V hRa b hb),
      fun k => ⟨H2_raw_of_one_raw b k (hRc _ hb k),
        H1_raw_of_H2_raw b k (H2_raw_of_one_raw b k (hRc _ hb k))⟩⟩)

theorem exists_local_sourceSignedTerminal_H1_H2_realization (a : realTypeSobolevSourceLocus) :
    ∃ U : Set (ScalarDomain 2 × ScalarDomain 2), IsOpen U ∧ a.val ∈ U ∧
      AnalyticOnNhd ℂ sourceSignedTerminalH2Remainder U ∧
      AnalyticOnNhd ℂ sourceSignedTerminalH1Sequence U ∧
      ∀ b ∈ U, ∀ k : ℤ,
        (sourceSignedTerminalH2Remainder b).val k =
          sourceSignedTerminalSequence (sobolevSourceInclusion b) k -
            sourceSignedTerminalFourier (sobolevSourceInclusion b) k ∧
        (sourceSignedTerminalH1Sequence b).val k = sourceSignedTerminalSequence (sobolevSourceInclusion b) k := by
  obtain ⟨U,hUsub,hU,haU⟩ := _root_.mem_nhds_iff.mp (eventually_H1_H2_realization a)
  exact ⟨U,hU,haU,fun b hb => (hUsub hb).1,fun b hb => (hUsub hb).2.1,
    fun b hb => (hUsub hb).2.2⟩

end NLS.ZakharovShabat
