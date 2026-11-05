import NLS.ZakharovShabat.SourceSignedTerminalH1Realization
import NLS.ZakharovShabat.SourceAngularBetaH1Decay

/-! Uniform one-order bounds for the actual Dirichlet-to-midpoint
displacement and periodic gap at every positive label near every real
H1 source. The gap is only bounded; no analytic ordering of endpoints
is inferred. The midpoint is recovered from both literal terminals. -/
noncomputable section
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat

def sourcePositiveDirichletMidpointH1 (a : ScalarDomain 2 × ScalarDomain 2) : ScalarDomain 2 :=
  (-1/4 : ℂ) • (sourceSignedTerminalH1Sequence a +
    WeightedCoeff.reflection 1 (sourceSignedTerminalH1Sequence a))

private theorem midpoint_eq_terminal_sum (ψ : CoeffPair 2) (n : ℤ) :
    sourceDirichletMidpointDisplacement (by simp) (by norm_num) ψ n =
      -(sourceGapWeightedEtaTerminalCoordinate (by simp) (by norm_num) n 1 ψ +
        sourceGapWeightedEtaTerminalCoordinate (by simp) (by norm_num) n (-1) ψ) / 4 := by
  simp only [sourceDirichletMidpointDisplacement_apply,sourceStandardRootMidpoint,
    sourceGapWeightedEtaTerminalCoordinate]
  ring

private theorem midpoint_positive_apply (a : ScalarDomain 2 × ScalarDomain 2)
    (hraw : ∀ k : ℤ, (sourceSignedTerminalH1Sequence a).val k =
      sourceSignedTerminalSequence (sobolevSourceInclusion a) k)
    (hlabels : ∀ k : ℤ,
      (0 < k → sourceSignedTerminalSequence (sobolevSourceInclusion a) k =
        sourceGapWeightedEtaTerminalCoordinate (by simp) (by norm_num) k 1 (sobolevSourceInclusion a)) ∧
      (k < 0 → sourceSignedTerminalSequence (sobolevSourceInclusion a) k =
        sourceGapWeightedEtaTerminalCoordinate (by simp) (by norm_num) (-k) (-1) (sobolevSourceInclusion a)))
    (n : ℕ+) :
    (sourcePositiveDirichletMidpointH1 a).val ((n : ℕ) : ℤ) =
      sourceDirichletMidpointDisplacement (by simp) (by norm_num) (sobolevSourceInclusion a) ((n : ℕ) : ℤ) := by
  have hn : (0 : ℤ) < ((n : ℕ) : ℤ) := by exact_mod_cast n.pos
  simp only [sourcePositiveDirichletMidpointH1,WeightedCoeff.smul_val,WeightedCoeff.add_val,
    WeightedCoeff.reflection_apply,hraw,midpoint_eq_terminal_sum]
  rw [(hlabels _).1 hn,(hlabels _).2 (neg_neg_of_pos hn),neg_neg]
  ring

private theorem analytic_midpoint_of_terminal (a : ScalarDomain 2 × ScalarDomain 2)
    (h : AnalyticAt ℂ sourceSignedTerminalH1Sequence a) :
    AnalyticAt ℂ sourcePositiveDirichletMidpointH1 a :=
  (h.add (((WeightedCoeff.reflection 1 (p := 2)).toContinuousLinearEquiv.toContinuousLinearMap.analyticAt _).comp h)).const_smul
    (c := (-1/4 : ℂ))

private theorem h1_weighted_coefficient_bound (a : ScalarDomain 2) (k : ℤ) :
    Weight.sobolev 1 k * ‖a.val k‖ ≤ ‖a‖ := by
  simpa only [mul_comm] using (le_div_iff₀ ((Weight.sobolev 1).positive k)).mp
    (WeightedCoeff.norm_apply_le _ 2 a k)

theorem exists_local_sourceH1Dirichlet_gap_weight_bound (a : realTypeSobolevSourceLocus) :
    ∃ U : Set (ScalarDomain 2 × ScalarDomain 2), IsOpen U ∧ a.val ∈ U ∧
      ∃ M : ℝ, 0 < M ∧ ∀ b ∈ U, ∀ n : ℕ+,
        Weight.sobolev 1 ((n : ℕ) : ℤ) *
          (‖sourceDirichletMidpointDisplacement (by simp) (by norm_num) (sobolevSourceInclusion b) ((n : ℕ) : ℤ)‖ +
            ‖sourcePeriodicGapDisplacement (by simp) (by norm_num) (sobolevSourceInclusion b) ((n : ℕ) : ℤ)‖) ≤ M := by
  obtain ⟨V,hV,haV,_,hT,hraw⟩ := exists_local_sourceSignedTerminal_H1_H2_realization a
  obtain ⟨W,hW,hreal,_,hlabels⟩ := exists_sourceSignedTerminalSequence_compact_derivative_domain
  have hnear : ∀ᶠ b in 𝓝 a.val,
      ‖sourcePositiveDirichletMidpointH1 b‖ < ‖sourcePositiveDirichletMidpointH1 a.val‖ + 1 :=
    (analytic_midpoint_of_terminal a.val (hT a.val haV)).continuousAt.norm.eventually
      (Iio_mem_nhds (by linarith))
  obtain ⟨O,hOsub,hO,haO⟩ := _root_.mem_nhds_iff.mp hnear
  obtain ⟨G,hG,haG,C,hC,hgap⟩ := exists_local_sourceWeightedGapSequence_bound
    (by simp) (by norm_num) (SpectralWeight.sobolev 1 (by norm_num))
    sobolevSourceInclusion sobolevSourceWeightedPeriodOne weightedBaseToPair_sobolevSourceWeightedPeriodOne a.val
  let U := (V ∩ sobolevSourceInclusion ⁻¹' W) ∩ (O ∩ G)
  refine ⟨U,(hV.inter (hW.preimage sobolevSourceInclusion.continuous)).inter (hO.inter hG),
    ⟨⟨haV,hreal a.property⟩,haO,haG⟩,‖sourcePositiveDirichletMidpointH1 a.val‖+1+C,by positivity,?_⟩
  intro b hb n
  have hmid := midpoint_positive_apply b (fun k => (hraw b hb.1.1 k).2)
    (fun k => ⟨(hlabels _ hb.1.2).1 k,(hlabels _ hb.1.2).2.1 k⟩) n
  have hd : Weight.sobolev 1 ((n : ℕ) : ℤ) *
      ‖sourceDirichletMidpointDisplacement (by simp) (by norm_num) (sobolevSourceInclusion b) ((n : ℕ) : ℤ)‖ ≤
        ‖sourcePositiveDirichletMidpointH1 b‖ := by
    rw [← hmid]
    exact h1_weighted_coefficient_bound _ _
  have hg : Weight.sobolev 1 ((n : ℕ) : ℤ) *
      ‖sourcePeriodicGapDisplacement (by simp) (by norm_num) (sobolevSourceInclusion b) ((n : ℕ) : ℤ)‖ ≤ C := by
    have hm := sourceH1WeightedGapSequence_majorant b ((n : ℕ) : ℤ)
    change Weight.sobolev 1 ((n : ℕ) : ℤ) * _ ≤ _
    rw [Weight.sobolev_apply,Real.rpow_one]
    exact hm.trans ((lp.norm_apply_le_norm (by norm_num) _ _).trans (hgap b hb.2.2))
  rw [mul_add]
  have hn : ‖sourcePositiveDirichletMidpointH1 b‖ < ‖sourcePositiveDirichletMidpointH1 a.val‖ + 1 :=
    hOsub hb.2.1
  exact (add_le_add hd hg).trans (by linarith)

end NLS.ZakharovShabat
