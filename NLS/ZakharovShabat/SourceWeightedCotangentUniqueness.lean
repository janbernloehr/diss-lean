import NLS.ZakharovShabat.SourceWeightedInclusion
import NLS.SequenceSpaces.SourceCotangent

/-! # Original Hilbert cotangents are determined by their weighted restriction

Every signed raw Fourier mode has a weighted representative. Equality on the
weighted source therefore determines both Hilbert cotangent sequences, and
the original dual pairing determines the entire cotangent.
-/
noncomputable section
set_option autoImplicit false
namespace NLS.ZakharovShabat

/-- No Hilbert cotangent information is lost by restriction to an original
weighted source, for any spectral weight. -/
theorem sourceHilbertCotangent_eq_of_weighted_restriction (w : SpectralWeight)
    (L M : CoeffPair 2 →L[ℂ] ℂ)
    (he : L.comp (originalWeightedSourceCLM w) = M.comp (originalWeightedSourceCLM w)) : L = M := by
  have hc : CoeffPair.cotangentCoefficients le_rfl L = CoeffPair.cotangentCoefficients le_rfl M := by
    apply Prod.ext
    · ext n
      rw [CoeffPair.cotangentCoefficients_fst,CoeffPair.cotangentCoefficients_fst]
      have h := congrArg (fun N => N (WeightedCoeffPair.inlCLM (sourceFrequencyWeight w)
        (WeightedCoeff.single (sourceFrequencyWeight w) n 1))) he
      simpa only [ContinuousLinearMap.comp_apply,originalWeightedSourceCLM_inl_single] using h
    · ext n
      rw [CoeffPair.cotangentCoefficients_snd,CoeffPair.cotangentCoefficients_snd]
      have h := congrArg (fun N => N (WeightedCoeffPair.inrCLM (sourceFrequencyWeight w)
        (WeightedCoeff.single (sourceFrequencyWeight w) n 1))) he
      simpa only [ContinuousLinearMap.comp_apply,originalWeightedSourceCLM_inr_single] using h
  apply ContinuousLinearMap.ext
  intro h
  have hr : CoeffPair.exponentInclusion le_rfl h = h := by
    apply (CoeffPair.toMax 2).injective
    apply Prod.ext <;> ext n <;> rfl
  have hL := CoeffPair.dualPairing_cotangentCoefficients le_rfl L h
  have hM := CoeffPair.dualPairing_cotangentCoefficients le_rfl M h
  rw [hc,hr] at hL
  rw [hr] at hM
  exact hL.symm.trans hM

end NLS.ZakharovShabat
