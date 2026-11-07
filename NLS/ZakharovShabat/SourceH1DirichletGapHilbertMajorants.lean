import NLS.ZakharovShabat.SourceH1DirichletGapWeights

/-! The complex positive Dirichlet-midpoint and periodic-gap weights
have actual Hilbert majorants AFTER one index derivative, uniformly
on one H1 neighborhood of every real source. No complex interlacing
or analytic ordering of gap endpoints is used. -/
noncomputable section
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat

private theorem positive_midpoint_raw (b : ScalarDomain 2 × ScalarDomain 2)
    (hraw : ∀ k : ℤ, (sourceSignedTerminalH1Sequence b).val k =
      sourceSignedTerminalSequence (sobolevSourceInclusion b) k)
    (hp : ∀ k : ℤ, 0 < k → sourceSignedTerminalSequence (sobolevSourceInclusion b) k =
      sourceGapWeightedEtaTerminalCoordinate (by simp) (by norm_num) k 1 (sobolevSourceInclusion b))
    (hm : ∀ k : ℤ, k < 0 → sourceSignedTerminalSequence (sobolevSourceInclusion b) k =
      sourceGapWeightedEtaTerminalCoordinate (by simp) (by norm_num) (-k) (-1) (sobolevSourceInclusion b))
    (n : ℕ+) : (sourcePositiveDirichletMidpointH1 b).val ((n:ℕ):ℤ) =
      sourceDirichletMidpointDisplacement (by simp) (by norm_num) (sobolevSourceInclusion b) ((n:ℕ):ℤ) := by
  have hn : (0:ℤ) < ((n:ℕ):ℤ) := by exact_mod_cast n.pos
  simp only [sourcePositiveDirichletMidpointH1,WeightedCoeff.smul_val,WeightedCoeff.add_val,
    WeightedCoeff.reflection_apply,hraw,hp _ hn,hm _ (neg_neg_of_pos hn),neg_neg,
    sourceDirichletMidpointDisplacement_apply,sourceGapWeightedEtaTerminalCoordinate,sourceStandardRootMidpoint]
  ring

private theorem analytic_midpoint (b : ScalarDomain 2 × ScalarDomain 2)
    (h : AnalyticAt ℂ sourceSignedTerminalH1Sequence b) : AnalyticAt ℂ sourcePositiveDirichletMidpointH1 b :=
  (h.add (((WeightedCoeff.reflection 1 (p := 2)).toContinuousLinearEquiv.toContinuousLinearMap.analyticAt _).comp h)).const_smul
    (c := (-1/4:ℂ))

theorem exists_local_sourceH1Dirichlet_gap_Hilbert_majorants (a : realTypeSobolevSourceLocus) :
    ∃ U : Set (ScalarDomain 2 × ScalarDomain 2), IsOpen U ∧ a.val ∈ U ∧
      ∃ M : ℝ, 0 ≤ M ∧ ∀ b ∈ U, ∃ G D : Coeff 2, ‖G‖+‖D‖ ≤ M ∧ ∀ n : ℕ+,
        (1+(n:ℝ))*(‖sourcePeriodicGapDisplacement (by simp) (by norm_num) (sobolevSourceInclusion b) ((n:ℕ):ℤ)‖+
          ‖sourceDirichletMidpointDisplacement (by simp) (by norm_num) (sobolevSourceInclusion b) ((n:ℕ):ℤ)‖) ≤
            ‖G ((n:ℕ):ℤ)‖+‖D ((n:ℕ):ℤ)‖ := by
  obtain ⟨V,hV,haV,_,hT,hraw⟩ := exists_local_sourceSignedTerminal_H1_H2_realization a
  obtain ⟨W,hW,hreal,_,hlabels⟩ := exists_sourceSignedTerminalSequence_compact_derivative_domain
  have hnear : ∀ᶠ b in 𝓝 a.val,
      ‖sourcePositiveDirichletMidpointH1 b‖ < ‖sourcePositiveDirichletMidpointH1 a.val‖+1 :=
    (analytic_midpoint a.val (hT a.val haV)).continuousAt.norm.eventually (Iio_mem_nhds (by linarith))
  obtain ⟨O,hOsub,hO,haO⟩ := _root_.mem_nhds_iff.mp hnear
  obtain ⟨T,hTopen,haT,C,hC,hgap⟩ := exists_local_sourceWeightedGapSequence_bound
    (by simp) (by norm_num) (SpectralWeight.sobolev 1 (by norm_num))
      sobolevSourceInclusion sobolevSourceWeightedPeriodOne weightedBaseToPair_sobolevSourceWeightedPeriodOne a.val
  let U := (V ∩ sobolevSourceInclusion ⁻¹' W) ∩ (O ∩ T)
  refine ⟨U,(hV.inter (hW.preimage sobolevSourceInclusion.continuous)).inter (hO.inter hTopen),
    ⟨⟨haV,hreal a.property⟩,haO,haT⟩,C+‖sourcePositiveDirichletMidpointH1 a.val‖+1,by positivity,?_⟩
  intro b hb
  let D := WeightedCoeff.weightIsometry (Weight.sobolev 1) 2 (sourcePositiveDirichletMidpointH1 b)
  have hD : ‖D‖ = ‖sourcePositiveDirichletMidpointH1 b‖ :=
    (WeightedCoeff.weightIsometry (Weight.sobolev 1) 2).norm_map _
  refine ⟨sourceH1WeightedGapSequence b,D,?_,?_⟩
  · rw [hD]
    have hg : ‖sourceH1WeightedGapSequence b‖ ≤ C := hgap b hb.2.2
    have hd : ‖sourcePositiveDirichletMidpointH1 b‖ < ‖sourcePositiveDirichletMidpointH1 a.val‖+1 := hOsub hb.2.1
    linarith
  · intro n
    have hd := positive_midpoint_raw b (fun k => (hraw b hb.1.1 k).2)
      (hlabels _ hb.1.2).1 (hlabels _ hb.1.2).2.1 n
    have hDn : ‖D ((n:ℕ):ℤ)‖ = (1+(n:ℝ))*
        ‖sourceDirichletMidpointDisplacement (by simp) (by norm_num) (sobolevSourceInclusion b) ((n:ℕ):ℤ)‖ := by
      change ‖(Weight.sobolev 1 ((n:ℕ):ℤ):ℂ)*(sourcePositiveDirichletMidpointH1 b).val ((n:ℕ):ℤ)‖ = _
      rw [hd,norm_mul,Complex.norm_real,Real.norm_of_nonneg ((Weight.sobolev 1).positive _).le]
      simp only [Weight.sobolev_apply,Real.rpow_one,Int.cast_natCast,abs_of_nonneg (by positivity : (0:ℝ) ≤ (n:ℝ))]
    have hg := sourceH1WeightedGapSequence_majorant b ((n:ℕ):ℤ)
    simp only [Int.cast_natCast,abs_of_nonneg (by positivity : (0:ℝ) ≤ (n:ℝ))] at hg
    rw [mul_add,← hDn]
    linarith

end NLS.ZakharovShabat
