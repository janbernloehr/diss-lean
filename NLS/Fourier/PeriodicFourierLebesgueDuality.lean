import NLS.Fourier.PeriodicFourierLebesgueEndpoints
/-! # Continuous duals and pseudomeasures on the original distribution spaces

At every finite source exponent, the full dual is isometrically the conjugate
Fourier–Lebesgue space. The bilinear pairing reverses one Fourier index, as
required by the unconjugated physical action. In particular, FL∞ is exactly
the continuous dual of the Wiener space FL¹.
-/
noncomputable section
open scoped ENNReal
namespace NLS.Fourier.PeriodicFourierLebesgue
open SmoothPeriodicTest
variable {L : ℝ} [Fact (0 < L)]
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [q.HolderConjugate p]

def unweightedDualEquiv (hp : p ≠ ⊤) :
    PeriodicFourierLebesgue L Weight.one q ≃L[ℂ] (PeriodicFourierLebesgue L Weight.one p →L[ℂ] ℂ) :=
  ((unweightedCoefficients q).trans Coeff.reflection).toContinuousLinearEquiv.trans
    ((Coeff.dualityIsometry (q := q) hp).toContinuousLinearEquiv.trans
      ((unweightedCoefficients p).symm.toContinuousLinearEquiv.arrowCongr (ContinuousLinearEquiv.refl ℂ ℂ)))

theorem unweightedDualEquiv_apply (hp : p ≠ ⊤) (v : PeriodicFourierLebesgue L Weight.one q)
    (u : PeriodicFourierLebesgue L Weight.one p) :
    unweightedDualEquiv hp v u = ∑' n : ℤ, v.val (mode n)*u.val (mode (-n)) := by
  change Coeff.dualPairing (Coeff.reflection (unweightedCoefficients q v)) (unweightedCoefficients p u) = _
  simp only [Coeff.dualPairing_apply,Coeff.reflection_apply,unweightedCoefficients_apply,neg_neg]

theorem norm_unweightedDualEquiv (hp : p ≠ ⊤) (v : PeriodicFourierLebesgue L Weight.one q) :
    ‖unweightedDualEquiv (p := p) hp v‖ = ‖v‖ := by
  let F := unweightedDualEquiv (p := p) hp v
  have hv : ‖Coeff.dualPairing (p := q) (q := p) (Coeff.reflection (unweightedCoefficients q v))‖ = ‖v‖ := by
    rw [Coeff.norm_dualPairing_eq hp]
    simp only [LinearIsometryEquiv.norm_map]
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro u
    have h := (Coeff.dualPairing (p := q) (q := p) (Coeff.reflection (unweightedCoefficients q v))).le_opNorm
      (unweightedCoefficients p u)
    change ‖Coeff.dualPairing (Coeff.reflection (unweightedCoefficients q v)) (unweightedCoefficients p u)‖ ≤ _
    simpa only [hv,LinearIsometryEquiv.norm_map] using h
  · rw [← hv]
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro a
    have h := F.le_opNorm ((unweightedCoefficients p).symm a)
    change ‖Coeff.dualPairing (Coeff.reflection (unweightedCoefficients q v))
      (unweightedCoefficients p ((unweightedCoefficients p).symm a))‖ ≤
      ‖F‖*‖(unweightedCoefficients p).symm a‖ at h
    simpa only [LinearIsometryEquiv.apply_symm_apply,LinearIsometryEquiv.norm_map] using h

def unweightedDualIsometry (hp : p ≠ ⊤) :
    PeriodicFourierLebesgue L Weight.one q ≃ₗᵢ[ℂ] (PeriodicFourierLebesgue L Weight.one p →L[ℂ] ℂ) where
  toLinearEquiv := (unweightedDualEquiv hp).toLinearEquiv
  norm_map' := norm_unweightedDualEquiv hp

/-- The original pseudomeasures are exactly the entire continuous dual of FL¹. -/
def pseudomeasureDualIsometry : PeriodicFourierLebesgue L Weight.one ⊤ ≃ₗᵢ[ℂ]
    (PeriodicFourierLebesgue L Weight.one 1 →L[ℂ] ℂ) := unweightedDualIsometry (by simp)

end NLS.Fourier.PeriodicFourierLebesgue
