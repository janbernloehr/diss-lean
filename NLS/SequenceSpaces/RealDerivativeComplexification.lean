import NLS.SequenceSpaces.RealGermExtensionCoordinates
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-! # Identification of the complexified real derivative

The complex extension of a real derivative is characterized by its values on
the included real subspace. Differentiating real-germ agreement identifies it
with the complex derivative of the constructed holomorphic extension.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.Coeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Real and imaginary coefficient projections decompose every complex sequence. -/
theorem complexCLM_re_add_I_im (z : Coeff p) :
    RealCoeff.complexCLM p (reCLM p z)+Complex.I • RealCoeff.complexCLM p (Complexification.imCLM p z) = z := by
  ext n
  change ((z n).re : ℂ)+Complex.I*((z n).im : ℂ) = z n
  apply Complex.ext <;> simp

/-- A complex-linear map is determined by its values on real sequences. -/
theorem Complexification.complexifyLinear_eq_of_real
    (A : RealCoeff p →L[ℝ] F) (T : Coeff p →L[ℂ] F)
    (h : ∀ x, T (RealCoeff.complexCLM p x) = A x) : complexifyLinear A = T := by
  ext z
  rw [complexifyLinear_apply]
  conv_rhs => rw [← complexCLM_re_add_I_im z]
  rw [map_add,map_smul,h,h]

/-- Complexification of a real linear map in the original coordinates. -/
def complexifyRealMap (L : E ≃L[ℂ] Coeff p)
    (A : coordinateRealSubmodule L →L[ℝ] F) : E →L[ℂ] F :=
  (Complexification.complexifyLinear (A.comp (coordinateRealEquiv L).symm.toContinuousLinearMap)).comp
    L.toContinuousLinearMap

/-- The complexified map recovers the original operator on the real subspace. -/
@[simp] theorem complexifyRealMap_real (L : E ≃L[ℂ] Coeff p)
    (A : coordinateRealSubmodule L →L[ℝ] F) (x : coordinateRealSubmodule L) :
    complexifyRealMap L A x.val = A x := by
  change Complexification.complexifyLinear (A.comp (coordinateRealEquiv L).symm.toContinuousLinearMap)
    (L x.val) = A x
  rw [← complex_coordinateRealEquiv,Complexification.complexifyLinear_real]
  change A ((coordinateRealEquiv L).symm (coordinateRealEquiv L x)) = A x
  rw [ContinuousLinearEquiv.symm_apply_apply]

/-- Complexification is unique in the original coordinates. -/
theorem complexifyRealMap_eq_of_real (L : E ≃L[ℂ] Coeff p)
    (A : coordinateRealSubmodule L →L[ℝ] F) (T : E →L[ℂ] F)
    (h : ∀ x : coordinateRealSubmodule L, T x.val = A x) : complexifyRealMap L A = T := by
  have ht : Complexification.complexifyLinear (A.comp (coordinateRealEquiv L).symm.toContinuousLinearMap) =
      T.comp L.symm.toContinuousLinearMap := by
    apply Complexification.complexifyLinear_eq_of_real
    intro x
    have hx := complex_coordinateRealEquiv L ((coordinateRealEquiv L).symm x)
    rw [ContinuousLinearEquiv.apply_symm_apply] at hx
    change T (L.symm (RealCoeff.complexCLM p x)) = A ((coordinateRealEquiv L).symm x)
    rw [hx,L.symm_apply_apply]
    exact h _
  ext z
  change Complexification.complexifyLinear (A.comp (coordinateRealEquiv L).symm.toContinuousLinearMap) (L z) = T z
  rw [ht]
  simp

/-- The complex derivative of a holomorphic extension is exactly the complexification
of the actual real derivative, not an extra derivative chosen by the atlas. -/
theorem fderiv_eq_complexifyRealMap (L : E ≃L[ℂ] Coeff p)
    {f : coordinateRealSubmodule L → F} {g : E → F} {x : coordinateRealSubmodule L}
    (hg : AnalyticAt ℂ g x.val)
    (he : (fun y : coordinateRealSubmodule L => g y.val) =ᶠ[𝓝 x] f) :
    fderiv ℂ g x.val = complexifyRealMap L (fderiv ℝ f x) := by
  have hd := (hg.differentiableAt.hasFDerivAt.restrictScalars ℝ).comp x
    (coordinateRealSubmodule L).subtypeL.hasFDerivAt
  have hdf := (hd.congr_of_eventuallyEq he.symm).fderiv
  symm
  apply complexifyRealMap_eq_of_real
  intro y
  have hh := congrArg (fun A : coordinateRealSubmodule L →L[ℝ] F => A y) hdf
  exact hh.symm

end NLS.Coeff
