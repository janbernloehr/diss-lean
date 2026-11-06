import NLS.Poisson.HminusGardnerBracket
import NLS.SequenceSpaces.SobolevDerivative
import NLS.SequenceSpaces.HilbertCotangent
import NLS.SequenceSpaces.SourceCotangentNormBound

noncomputable section
set_option autoImplicit false
open Complex
open scoped ENNReal

namespace NLS.Poisson



/-- The original unit-period Hilbert Fourier source embeds contractively
in H-minus-one, preserving every raw coefficient. -/
def hilbertToHminus : Coeff 2 →L[ℂ] WeightedCoeff (Weight.sobolev (-1)) 2 :=
  (WeightedCoeff.sobolevInclusion (by norm_num : (-1 : ℝ)≤0)).comp
    (WeightedCoeff.weightIsometry (Weight.sobolev 0) 2).symm.toContinuousLinearEquiv.toContinuousLinearMap

theorem hilbertToHminus_apply (h : Coeff 2) (k : ℤ) : (hilbertToHminus h).val k=h k := by
  change (WeightedCoeff.sobolevInclusion (by norm_num : (-1 : ℝ)≤0)
    ((WeightedCoeff.weightIsometry (Weight.sobolev 0) 2).symm h)).val k=_
  rw [WeightedCoeff.sobolevInclusion_apply]
  have he := congrArg (fun a : Coeff 2 => a k)
    ((WeightedCoeff.weightIsometry (Weight.sobolev 0) 2).apply_symm_apply h)
  change (Weight.sobolev 0 k : ℂ)*((WeightedCoeff.weightIsometry (Weight.sobolev 0) 2).symm h).val k=h k at he
  simpa only [Weight.sobolev_zero_apply,ofReal_one,one_mul] using he

/-- The H-minus-one cotangent extraction returns the literal original H1
coefficient sequence from its physical Sobolev pairing. -/
theorem hminusCotangentCLM_pairing (a : WeightedCoeff (Weight.sobolev 1) 2) :
    hminusCotangentCLM (WeightedCoeff.sobolevBilinearPairing 1 a)=a := by
  apply Subtype.ext
  funext k
  rw [hminusCotangentCLM_apply,WeightedCoeff.sobolevBilinearPairing_apply]
  simp [WeightedCoeff.ofFinsupp_apply,Finsupp.single_apply,neg_eq_iff_eq_neg]

/-- Original unit-mode values identify a Hilbert differential with the
restriction of its actual H-minus-one cotangent extension. -/
theorem hilbertDifferential_eq_hminusRestriction_of_modes
    (L : Coeff 2 →L[ℂ] ℂ) (a : WeightedCoeff (Weight.sobolev 1) 2)
    (hm : ∀ n : ℤ, L (lp.single 2 n 1)=a.val (-n)) :
    L=(WeightedCoeff.sobolevBilinearPairing 1 a).comp hilbertToHminus := by
  let B := (WeightedCoeff.sobolevBilinearPairing 1 a).comp hilbertToHminus
  have hB (n : ℤ) : B (lp.single 2 n 1)=a.val (-n) := by
    change WeightedCoeff.sobolevBilinearPairing 1 a (hilbertToHminus (lp.single 2 n 1))=_
    rw [WeightedCoeff.sobolevBilinearPairing_apply]
    simp [hilbertToHminus_apply,lp.single_apply,Pi.single_apply,neg_eq_iff_eq_neg]
  have he : L=Coeff.dualPairing (Coeff.hilbertCotangentCoefficients B) :=
    Coeff.eq_dualPairing_of_single (by simp : (2 : ℝ≥0∞)≠⊤) L _ (by
      intro n
      rw [Coeff.hilbertCotangentCoefficients_apply,hm n,hB n])
  ext h
  rw [he,Coeff.dualPairing_hilbertCotangentCoefficients]

end NLS.Poisson
