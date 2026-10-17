import NLS.ZakharovShabat.SourceBirkhoffWeightedJacobianInvertible
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic

/-! # Actual complex local inverses in the native weighted spaces

At every weighted real source the full Jacobian is a bounded complex
linear equivalence. The analytic inverse theorem constructs a local
inverse of the actual weighted Birkhoff map, with both inverse germs
and strict derivative equal to the bounded inverse Jacobian.
-/

noncomputable section
open Set Metric Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceBirkhoffMapComplexData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- The actual weighted Jacobian as a bounded complex linear equivalence. -/
def originalWeightedJacobianEquiv
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s) (w : SpectralWeight)
    (a : weightedRealSourceSubmodule (p := p) w) :
    WeightedCoeffPair (sourceFrequencyWeight w) p ≃L[ℂ] WeightedCoeffPair (sourceFrequencyWeight w) p :=
  ContinuousLinearEquiv.ofBijective (fderiv ℂ (originalWeightedBirkhoffMap hp hp1 s w) a.val)
    (LinearMap.ker_eq_bot.mpr (D.originalWeightedBirkhoffMap_fderiv_bijective w a).1)
    (LinearMap.range_eq_top.mpr (D.originalWeightedBirkhoffMap_fderiv_bijective w a).2)

@[simp] theorem originalWeightedJacobianEquiv_toContinuousLinearMap
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s) (w : SpectralWeight)
    (a : weightedRealSourceSubmodule (p := p) w) :
    (D.originalWeightedJacobianEquiv w a).toContinuousLinearMap =
      fderiv ℂ (originalWeightedBirkhoffMap hp hp1 s w) a.val := rfl

/-- Forgetting the weight commutes with the actual bounded inverse Jacobian. -/
theorem originalWeightedJacobianEquiv_symm_forget
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s) (w : SpectralWeight)
    (a : weightedRealSourceSubmodule (p := p) w) :
    (originalWeightedSourceCLM w).comp (D.originalWeightedJacobianEquiv w a).symm.toContinuousLinearMap =
      (D.jacobianEquivAll (originalWeightedRealSource w a)).symm.toContinuousLinearMap.comp
        (weightedBirkhoffTargetInclusion w) := by
  have hspec := D.originalWeightedComplexDomain_spec w
  have hc := (hspec.2.2.2 a.val (hspec.2.1 a)).2.2
  apply ContinuousLinearMap.ext
  intro v
  apply (D.jacobianEquivAll (originalWeightedRealSource w a)).injective
  have hv := congrArg (fun L => L ((D.originalWeightedJacobianEquiv w a).symm v)) hc
  change weightedBirkhoffTargetInclusion w
      (D.originalWeightedJacobianEquiv w a ((D.originalWeightedJacobianEquiv w a).symm v)) =
    D.jacobianEquivAll (originalWeightedRealSource w a)
      (originalWeightedSourceCLM w ((D.originalWeightedJacobianEquiv w a).symm v)) at hv
  simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply] using hv.symm

/-- A two-sided complex analytic inverse germ of the actual native weighted map. -/
theorem exists_originalWeighted_complex_localInverse
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s) (w : SpectralWeight)
    (a : weightedRealSourceSubmodule (p := p) w) :
    ∃ g : WeightedCoeffPair (sourceFrequencyWeight w) p → WeightedCoeffPair (sourceFrequencyWeight w) p,
      AnalyticAt ℂ g (originalWeightedBirkhoffMap hp hp1 s w a.val) ∧
      g (originalWeightedBirkhoffMap hp hp1 s w a.val) = a.val ∧
      (∀ᶠ b in 𝓝 a.val, g (originalWeightedBirkhoffMap hp hp1 s w b) = b) ∧
      (∀ᶠ z in 𝓝 (originalWeightedBirkhoffMap hp hp1 s w a.val), originalWeightedBirkhoffMap hp hp1 s w (g z) = z) ∧
      HasStrictFDerivAt g (D.originalWeightedJacobianEquiv w a).symm.toContinuousLinearMap
        (originalWeightedBirkhoffMap hp hp1 s w a.val) := by
  have hspec := D.originalWeightedComplexDomain_spec w
  have ha := hspec.2.2.1 a.val (hspec.2.1 a)
  have hd : HasStrictFDerivAt (originalWeightedBirkhoffMap hp hp1 s w)
      (D.originalWeightedJacobianEquiv w a).toContinuousLinearMap a.val :=
    ha.contDiffAt.hasStrictFDerivAt (n := 1) one_ne_zero
  let e := hd.toOpenPartialHomeomorph (originalWeightedBirkhoffMap hp hp1 s w)
  have he : (e : WeightedCoeffPair (sourceFrequencyWeight w) p → WeightedCoeffPair (sourceFrequencyWeight w) p) =
      originalWeightedBirkhoffMap hp hp1 s w := hd.toOpenPartialHomeomorph_coe
  have hg : AnalyticAt ℂ e.symm (originalWeightedBirkhoffMap hp hp1 s w a.val) := by
    have h := e.analyticAt_symm' hd.mem_toOpenPartialHomeomorph_source
      (by rw [he]; exact ha) (i := D.originalWeightedJacobianEquiv w a) (by rw [he]; rfl)
    rw [he] at h
    exact h
  exact ⟨hd.localInverse _ _ _,hg,hd.localInverse_apply_image,
    hd.eventually_left_inverse,hd.eventually_right_inverse,hd.to_localInverse⟩
end SourceBirkhoffMapComplexData
end NLS.ZakharovShabat
