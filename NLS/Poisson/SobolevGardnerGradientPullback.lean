import NLS.Poisson.SobolevGardnerGradient

/-! # Fourier coefficients of actual Gardner gradients under linear pullback -/
noncomputable section
open Complex NLS.ZakharovShabat
namespace NLS.Poisson.SobolevGardnerGradientAt

theorem gradient_eval_of_pullback {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    {F : ScalarDomain 2 → ℂ} {a : ScalarDomain 2} (P : SobolevGardnerGradientAt F a)
    (G : X → ℂ) (M : ScalarDomain 2 →L[ℂ] X) (hG : DifferentiableAt ℂ G (M a))
    (he : ∀ b, F b = G (M b)) (m : ℤ) :
    P.gradient.val m = (fderiv ℂ G (M a)) (M (scalarMode (-m) 1)) := by
  have hd : HasFDerivAt F ((fderiv ℂ G (M a)).comp M) a :=
    (hG.hasFDerivAt.comp a M.hasFDerivAt).congr_of_eventuallyEq (Filter.Eventually.of_forall he)
  have hv := congrArg (fun L : ScalarDomain 2 →L[ℂ] ℂ => L (scalarMode (-m) 1)) (P.hasFDerivAt.unique hd)
  change reflectedHilbertPairing (scalarInclusion P.gradient) (scalarInclusion (scalarMode (-m) 1)) = _ at hv
  rw [scalarInclusion_scalarMode,reflectedHilbertPairing_comm,reflectedHilbertPairing_single_left] at hv
  simpa only [neg_neg,one_mul,scalarInclusion_apply,ContinuousLinearMap.comp_apply] using hv

end NLS.Poisson.SobolevGardnerGradientAt
