import NLS.Fourier.PeriodicDistributionIdentification

/-! # Dilation of actual tempered distributions

The inverse Jacobian is kept explicitly. Algebraic identities hold for every
nonzero scale; all physical period transports use a positive scale.
-/
noncomputable section
open scoped SchwartzMap
namespace NLS.Fourier

private def realScale (c : ℝ) (hc : c ≠ 0) : ℝ ≃L[ℝ] ℝ :=
  { LinearEquiv.smulOfNeZero ℝ (M := ℝ) c hc with
    continuous_toFun := by change Continuous (fun x : ℝ => c*x); fun_prop
    continuous_invFun := by change Continuous (fun x : ℝ => c⁻¹*x); fun_prop }

/-- Composition of Schwartz tests with a nonzero real dilation. -/
def schwartzDilationCLM (c : ℝ) (hc : c ≠ 0) : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (realScale c hc)

@[simp] theorem schwartzDilationCLM_apply (c : ℝ) (hc : c ≠ 0) (g : 𝓢(ℝ, ℂ)) (x : ℝ) :
    schwartzDilationCLM c hc g x = g (c*x) := rfl

/-- Oriented distribution pullback; on positive scalars this is the usual physical dilation. -/
def distributionDilation (c : ℝ) (hc : c ≠ 0) (T : 𝓢'(ℝ, ℂ)) : 𝓢'(ℝ, ℂ) :=
  (c : ℂ)⁻¹ • T.comp (schwartzDilationCLM c⁻¹ (inv_ne_zero hc))

@[simp] theorem distributionDilation_apply (c : ℝ) (hc : c ≠ 0) (T : 𝓢'(ℝ, ℂ)) (g : 𝓢(ℝ, ℂ)) :
    distributionDilation c hc T g = (c : ℂ)⁻¹*T (schwartzDilationCLM c⁻¹ (inv_ne_zero hc) g) := rfl

/-- Continuous linear dependence of the rescaled distribution on the original one. -/
def distributionDilationCLM (c : ℝ) (hc : c ≠ 0) : 𝓢'(ℝ, ℂ) →L[ℂ] 𝓢'(ℝ, ℂ) :=
  (c : ℂ)⁻¹ • PointwiseConvergenceCLM.precomp ℂ (schwartzDilationCLM c⁻¹ (inv_ne_zero hc))

@[simp] theorem distributionDilationCLM_apply (c : ℝ) (hc : c ≠ 0) (T : 𝓢'(ℝ, ℂ)) :
    distributionDilationCLM c hc T = distributionDilation c hc T := rfl

/-- Inverse dilations recover the original distribution exactly. -/
theorem distributionDilation_inverse (c : ℝ) (hc : c ≠ 0) (T : 𝓢'(ℝ, ℂ)) :
    distributionDilation c⁻¹ (inv_ne_zero hc) (distributionDilation c hc T) = T := by
  ext g
  simp only [distributionDilation_apply,Complex.ofReal_inv,inv_inv]
  have he : schwartzDilationCLM c⁻¹ (inv_ne_zero hc) (schwartzDilationCLM c hc g) = g := by
    ext x
    simp [hc]
  rw [he]
  field_simp [Complex.ofReal_ne_zero.mpr hc]

/-- The reverse composition also recovers the original distribution. -/
theorem distributionDilation_inverse_right (c : ℝ) (hc : c ≠ 0) (T : 𝓢'(ℝ, ℂ)) :
    distributionDilation c hc (distributionDilation c⁻¹ (inv_ne_zero hc) T) = T := by
  simpa only [inv_inv] using distributionDilation_inverse c⁻¹ (inv_ne_zero hc) T

/-- Dilation is injective on actual distributions. -/
theorem distributionDilation_injective (c : ℝ) (hc : c ≠ 0) :
    Function.Injective (distributionDilation c hc) := by
  intro T U h
  have he := congrArg (distributionDilation c⁻¹ (inv_ne_zero hc)) h
  simpa only [distributionDilation_inverse] using he

/-- Actual invariance of a tempered distribution under translation by the stated period. -/
def IsPeriodicDistribution (L : ℝ) (T : 𝓢'(ℝ, ℂ)) : Prop :=
  ∀ g : 𝓢(ℝ, ℂ), T (SchwartzMap.compSubConstCLM ℂ L g) = T g

/-- Dilation rescales the actual distributional period. -/
theorem distributionDilation_periodic (c : ℝ) (hc : c ≠ 0) (L : ℝ) (T : 𝓢'(ℝ, ℂ))
    (hT : IsPeriodicDistribution L T) : IsPeriodicDistribution (L/c) (distributionDilation c hc T) := by
  intro g
  simp only [distributionDilation_apply]
  congr 1
  have he : schwartzDilationCLM c⁻¹ (inv_ne_zero hc) (SchwartzMap.compSubConstCLM ℂ (L/c) g) =
      SchwartzMap.compSubConstCLM ℂ L (schwartzDilationCLM c⁻¹ (inv_ne_zero hc) g) := by
    ext x
    simp only [schwartzDilationCLM_apply,SchwartzMap.compSubConstCLM_apply]
    congr 1
    ring
  rw [he]
  exact hT _

end NLS.Fourier
