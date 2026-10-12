import NLS.SequenceSpaces.InfinityDuality
import NLS.SequenceSpaces.SobolevBilinearPairing
import NLS.SequenceSpaces.WeightedPairNormInfty

/-! # Failure of unrestricted Sobolev gradient representation at infinity

The infinity obstruction survives every real Sobolev weight and the exact
source pair norm. The pairing here is the corrected physical bilinear one;
its frequency reversal does not repair failure of full-dual representation.
-/
noncomputable section
open scoped ENNReal
namespace NLS.WeightedCoeff

/-- No real Sobolev order makes every infinity-source functional representable. -/
theorem exists_sobolev_functional_without_gradient (s : ℝ) :
    ∃ L : WeightedCoeff (Weight.sobolev s) ⊤ →L[ℂ] ℂ,
      ∀ b : WeightedCoeff (Weight.sobolev (-s)) 1,
        ¬∀ h : WeightedCoeff (Weight.sobolev s) ⊤, sobolevBilinearPairing s h b = L h := by
  obtain ⟨L,hL⟩ := Coeff.exists_nonrepresented_functional
  let e := weightIsometry (Weight.sobolev s) ⊤
  refine ⟨L.comp e.toContinuousLinearEquiv.toContinuousLinearMap,?_⟩
  intro b hb
  apply hL (Coeff.reflection (weightIsometry (Weight.sobolev (-s)) 1 b))
  ext x
  have he := hb (e.symm x)
  change Coeff.dualPairing (e (e.symm x))
    (Coeff.reflection (weightIsometry (Weight.sobolev (-s)) 1 b)) = L (e (e.symm x)) at he
  simp only [LinearIsometryEquiv.apply_symm_apply] at he
  simpa only [Coeff.dualPairing_apply,mul_comm] using he

/-- The failed representative would be the derivative of an everywhere-analytic function. -/
theorem exists_analytic_sobolev_without_gradient (s : ℝ) :
    ∃ F : WeightedCoeff (Weight.sobolev s) ⊤ → ℂ, AnalyticOnNhd ℂ F Set.univ ∧
      ∀ x, ¬∃ b : WeightedCoeff (Weight.sobolev (-s)) 1,
        ∀ h : WeightedCoeff (Weight.sobolev s) ⊤, sobolevBilinearPairing s h b = fderiv ℂ F x h := by
  obtain ⟨L,hL⟩ := exists_sobolev_functional_without_gradient s
  refine ⟨L,fun x _ => L.analyticAt x,?_⟩
  intro x ⟨b,hb⟩
  apply hL b
  intro h
  simpa only [L.hasFDerivAt.fderiv] using hb h

end NLS.WeightedCoeff
namespace NLS.WeightedCoeffPairInfty

/-- The original weighted infinity pair norm admits analytic functionals without
any opposite-order l1 pair gradient. Both inputs and candidate gradients use
signed pair coefficients as in (1.2). Reversing both first-component scalar
indices leaves the physical product unchanged. -/
theorem exists_analytic_sobolev_pair_without_gradient (s : ℝ) :
    ∃ F : WeightedCoeffPairInfty (Weight.sobolev s) → ℂ,
      AnalyticOnNhd ℂ F Set.univ ∧
      ∀ x, ¬∃ g : WeightedCoeffPair (Weight.sobolev (-s)) 1,
        ∀ h : WeightedCoeffPairInfty (Weight.sobolev s),
          fderiv ℂ F x h =
            WeightedCoeff.sobolevBilinearPairing s h.1 g.fst +
            WeightedCoeff.sobolevBilinearPairing s h.2 g.snd := by
  obtain ⟨L,hL⟩ := WeightedCoeff.exists_sobolev_functional_without_gradient s
  let K : WeightedCoeffPairInfty (Weight.sobolev s) →L[ℂ] ℂ :=
    L.comp ((ContinuousLinearMap.fst ℂ _ _).comp
      (toMax (Weight.sobolev s)).toContinuousLinearMap)
  refine ⟨K,fun x _ => K.analyticAt x,?_⟩
  intro x ⟨g,hg⟩
  apply hL g.fst
  intro a
  have he := hg (ofPair (Weight.sobolev s) a 0)
  rw [K.hasFDerivAt.fderiv] at he
  change L a = WeightedCoeff.sobolevBilinearPairing s a g.fst +
    WeightedCoeff.sobolevBilinearPairing s 0 g.snd at he
  simpa only [map_zero,zero_apply,add_zero] using he.symm

end NLS.WeightedCoeffPairInfty
