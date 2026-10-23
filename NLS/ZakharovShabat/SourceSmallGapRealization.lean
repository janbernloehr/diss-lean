import NLS.ZakharovShabat.SourceSmallSquaredGapUniqueness

/-! # Small prescribed gaps with a prescribed source-norm bound

Continuity of the analytic local inverse gives realizations inside any
chosen positive source ball. Combining this with small-source squared-gap
uniqueness solves the local periodic inverse problem up to isospectrality.
-/
noncomputable section
open Set Complex Filter Topology
namespace NLS.ZakharovShabat

/-- Sufficiently small signed data have a symmetric realization within any prescribed
positive bound on the original Hilbert source norm. -/
theorem exists_small_symmetric_signed_gap_realization_norm_lt (r : ℝ) (hr : 0 < r) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ b : RealCoeff 2, ‖b‖ < δ →
      ∃ φ : realTypeSourceSubmodule 2, ‖φ.val‖ < r ∧
        realSourceSpatialReflection φ = φ ∧ ∀ n,
        sourceSignedGapSequence (by simp) (by norm_num) φ.val n = (b n : ℂ) := by
  obtain ⟨G,hG,hzero,_,hright,_⟩ := exists_symmetricSourceSignedGap_localInverse_zero
  have hc : ContinuousAt (fun b => symmetricSourceCoefficients 2 (G b)) 0 :=
    (symmetricSourceCoefficients 2).continuous.continuousAt.comp hG.continuousAt
  have hs : ∀ᶠ b in 𝓝 (0 : RealCoeff 2),
      symmetricSourceCoefficients 2 (G b) ∈ Metric.ball (0 : CoeffPair 2) r := by
    apply hc.preimage_mem_nhds
    simpa only [hzero,map_zero] using Metric.ball_mem_nhds (0 : CoeffPair 2) hr
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp (hright.and hs)
  refine ⟨δ,hδ,fun b hb => ?_⟩
  have h := hball (show b ∈ Metric.ball (0 : RealCoeff 2) δ by
    simpa only [Metric.mem_ball,dist_zero_right] using hb)
  let φ := symmetricRealSourceCoefficients 2 (G b)
  refine ⟨φ,?_,symmetricRealSourceCoefficients_reflection_fixed (G b),fun n => ?_⟩
  · simpa only [φ,symmetricRealSourceCoefficients_val,Metric.mem_ball,dist_zero_right] using h.2
  · apply Complex.ext
    · exact congrArg (fun a : RealCoeff 2 => a n) h.1
    · simpa only [ofReal_im] using sourceSignedGapSequence_im_eq_zero (by simp) (by norm_num) φ n

/-- Small nonnegative periodic gap data can be realized within any prescribed source ball. -/
theorem exists_small_symmetric_periodic_gap_realization_norm_lt (r : ℝ) (hr : 0 < r) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ γ : RealCoeff 2, ‖γ‖ < δ → (∀ n, 0 ≤ γ n) →
      ∃ φ : realTypeSourceSubmodule 2, ‖φ.val‖ < r ∧
        realSourceSpatialReflection φ = φ ∧ ∀ n,
        canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential φ.val)
          (periodOnePotential_mem _) n = (γ n : ℂ) := by
  obtain ⟨δ,hδ,hrealize⟩ := exists_small_symmetric_signed_gap_realization_norm_lt r hr
  refine ⟨δ,hδ,fun γ hγ hnonneg => ?_⟩
  obtain ⟨φ,hφnorm,hφ,he⟩ := hrealize γ hγ
  refine ⟨φ,hφnorm,hφ,fun n => ?_⟩
  apply Complex.ext
  · have h := abs_sourceSignedGapSequence_re_of_reflection_fixed (by simp) (by norm_num) φ hφ n
    rw [he n,ofReal_re,abs_of_nonneg (hnonneg n)] at h
    exact h.symm
  · have h := canonicalPeriodicEndpoints_im_eq_zero_of_realType (by simp) (by norm_num) _
      (periodOnePotential_mem _) (isRealType_periodOnePotential φ.val φ.property) n
    simp only [canonicalPeriodicGap,sub_im,h.1,h.2,sub_self,ofReal_im]

/-- Every sufficiently small nonnegative Hilbert gap sequence determines exactly one actual
periodic spectrum among sources in a fixed small source ball, and has a symmetric realization. -/
theorem exists_small_periodic_gap_inverse_up_to_isospectrality :
    ∃ r : ℝ, 0 < r ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ γ : RealCoeff 2, ‖γ‖ < δ → (∀ n, 0 ≤ γ n) →
        ∃ φ : realTypeSourceSubmodule 2, ‖φ.val‖ < r ∧
          realSourceSpatialReflection φ = φ ∧
          (∀ n, canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential φ.val)
            (periodOnePotential_mem _) n = (γ n : ℂ)) ∧
          ∀ ψ : realTypeSourceSubmodule 2, ‖ψ.val‖ < r →
            (∀ n, canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential ψ.val)
              (periodOnePotential_mem _) n = (γ n : ℂ)) →
            ψ ∈ sourceIsospectralSet (by simp) φ := by
  obtain ⟨r,hr,hunique⟩ := exists_small_source_squared_gap_spectral_uniqueness
  obtain ⟨δ,hδ,hrealize⟩ := exists_small_symmetric_periodic_gap_realization_norm_lt r hr
  refine ⟨r,hr,δ,hδ,fun γ hγ hnonneg => ?_⟩
  obtain ⟨φ,hφ,hfixed,hgaps⟩ := hrealize γ hγ hnonneg
  refine ⟨φ,hφ,hfixed,hgaps,fun ψ hψ hψgaps => ?_⟩
  apply hunique φ ψ hφ hψ
  intro n
  rw [hgaps n,hψgaps n]

end NLS.ZakharovShabat
