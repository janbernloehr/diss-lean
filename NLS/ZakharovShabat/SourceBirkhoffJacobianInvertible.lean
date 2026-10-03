import NLS.ZakharovShabat.SourceBirkhoffJacobianRange
import NLS.ZakharovShabat.SourceBirkhoffLemma16_3
import NLS.FunctionalAnalysis.CompactDenseRange
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-! # Birkhoff Jacobian invertibility for exponents at least two

Canonical mode preimages imply dense range. The compact perturbation
from Lemma 16.3 then gives a bounded inverse at every real source.
The complex Birkhoff map consequently has an analytic local inverse there.
-/

noncomputable section
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceBirkhoffMapComplexData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}

/-- The normalized derivative is bijective at every real source for `2 ≤ p < ∞`. -/
theorem normalizedJacobian_bijective
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (h2p : (2 : ℝ≥0∞) ≤ p) (φ : realTypeSourceSubmodule p) :
    Function.Bijective (sourceBirkhoffNormalizedJacobian hp hp1 s φ.val) := by
  apply CompactSpectrum.bijective_of_denseRange_compact_sub_id
  · exact D.isCompactOperator_normalizedJacobian_sub_id φ
  · exact (sourceBirkhoffFourierEquiv (p := p)).symm.surjective.denseRange.comp
      (D.jacobian_denseRange h2p φ) sourceBirkhoffFourierInverse.continuous

/-- Bijectivity of the actual complex derivative, with no finite-gap hypothesis. -/
theorem jacobian_bijective
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (h2p : (2 : ℝ≥0∞) ≤ p) (φ : realTypeSourceSubmodule p) :
    Function.Bijective (sourceBirkhoffJacobian hp hp1 s φ.val) :=
  (sourceBirkhoffNormalizedJacobian_bijective_iff hp hp1 s φ.val).mp
    (D.normalizedJacobian_bijective h2p φ)

/-- The actual Jacobian packaged as a bounded linear equivalence. -/
def jacobianEquiv
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (h2p : (2 : ℝ≥0∞) ≤ p) (φ : realTypeSourceSubmodule p) :
    CoeffPair p ≃L[ℂ] (Coeff p × Coeff p) :=
  ContinuousLinearEquiv.ofBijective (sourceBirkhoffJacobian hp hp1 s φ.val)
    (LinearMap.ker_eq_bot.mpr (D.jacobian_bijective h2p φ).1)
    (LinearMap.range_eq_top.mpr (D.jacobian_bijective h2p φ).2)

@[simp] theorem jacobianEquiv_toContinuousLinearMap
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (h2p : (2 : ℝ≥0∞) ≤ p) (φ : realTypeSourceSubmodule p) :
    (D.jacobianEquiv h2p φ).toContinuousLinearMap =
      sourceBirkhoffJacobian hp hp1 s φ.val := rfl

/-- An analytic local inverse of the complex Birkhoff map at every real
source in the range `2 ≤ p < ∞`, with both actual inverse identities. -/
theorem exists_complex_localInverse
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (h2p : (2 : ℝ≥0∞) ≤ p) (φ : realTypeSourceSubmodule p) :
    ∃ g : (Coeff p × Coeff p) → CoeffPair p,
      AnalyticAt ℂ g (sourceBirkhoffMap hp hp1 s φ.val) ∧
      g (sourceBirkhoffMap hp hp1 s φ.val) = φ.val ∧
      (∀ᶠ ψ in 𝓝 φ.val, g (sourceBirkhoffMap hp hp1 s ψ) = ψ) ∧
      (∀ᶠ z in 𝓝 (sourceBirkhoffMap hp hp1 s φ.val), sourceBirkhoffMap hp hp1 s (g z) = z) ∧
      HasStrictFDerivAt g (D.jacobianEquiv h2p φ).symm.toContinuousLinearMap
        (sourceBirkhoffMap hp hp1 s φ.val) := by
  have ha := D.analytic φ.val (D.real_subset φ.property)
  have hd : HasStrictFDerivAt (sourceBirkhoffMap hp hp1 s)
      (D.jacobianEquiv h2p φ).toContinuousLinearMap φ.val :=
    ha.contDiffAt.hasStrictFDerivAt (n := 1) one_ne_zero
  let e := hd.toOpenPartialHomeomorph (sourceBirkhoffMap hp hp1 s)
  have he : (e : CoeffPair p → (Coeff p × Coeff p)) = sourceBirkhoffMap hp hp1 s :=
    hd.toOpenPartialHomeomorph_coe
  have hg : AnalyticAt ℂ e.symm (sourceBirkhoffMap hp hp1 s φ.val) := by
    have h := e.analyticAt_symm' hd.mem_toOpenPartialHomeomorph_source
      (by rw [he]; exact ha) (i := D.jacobianEquiv h2p φ) (by rw [he]; rfl)
    rw [he] at h
    exact h
  exact ⟨hd.localInverse _ _ _, hg, hd.localInverse_apply_image,
    hd.eventually_left_inverse, hd.eventually_right_inverse, hd.to_localInverse⟩

end SourceBirkhoffMapComplexData
end NLS.ZakharovShabat
