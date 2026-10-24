import NLS.FunctionalAnalysis.CompactSmoothPrimitive
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Calculus.BumpFunction.Normed

/-! # A locally integrable function with zero weak derivative is constant

Subtract a normalized compact bump from an arbitrary test to obtain a
zero-integral test, take its compact smooth primitive, and use the
fundamental lemma for locally integrable functions.
-/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped ContDiff
namespace NLS.FunctionalAnalysis

/-- Vanishing distributional derivative on the real line forces an
almost-everywhere constant, with no global integrability assumption. -/
theorem ae_eq_const_of_integral_deriv_smul_eq_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : ℝ → E) (hf : LocallyIntegrable f volume)
    (hw : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      (∫ t : ℝ, deriv ψ t • f t) = 0) :
    ∃ c : E, f =ᵐ[volume] (fun _ => c) := by
  let B : ContDiffBump (0 : ℝ) := default
  let ρ : ℝ → ℝ := B.normed volume
  have hρ : ContDiff ℝ ∞ ρ := B.contDiff_normed (n := ⊤)
  have hρc : HasCompactSupport ρ := B.hasCompactSupport_normed (μ := volume)
  have hρi : Integrable ρ volume := B.integrable_normed (μ := volume)
  have hρ1 : (∫ t : ℝ, ρ t) = 1 := B.integral_normed (μ := volume)
  let c : E := ∫ t : ℝ, ρ t • f t
  have hconst : LocallyIntegrable (fun _ : ℝ => c) volume := continuous_const.locallyIntegrable
  refine ⟨c,ae_eq_of_integral_contDiff_smul_eq hf hconst ?_⟩
  intro χ hχ hχc
  rw [integral_smul_const]
  let d : ℝ := ∫ t : ℝ, χ t
  let ψ : ℝ → ℝ := fun t => χ t-d*ρ t
  have hψ : ContDiff ℝ ∞ ψ := hχ.sub (hρ.const_smul d)
  have hscaled : HasCompactSupport (fun t : ℝ => d*ρ t) :=
    hρc.smul_left (f := fun _ : ℝ => d)
  have hψc : HasCompactSupport ψ := hχc.sub hscaled
  have hψi : (∫ t : ℝ, ψ t) = 0 := by
    change (∫ t : ℝ, χ t-d*ρ t) = 0
    rw [integral_sub (hχ.continuous.integrable_of_hasCompactSupport hχc) (hρi.const_mul d),
      integral_const_mul,hρ1,mul_one]
    exact sub_self d
  obtain ⟨F,hF,hFc,hFd⟩ := exists_contDiff_compact_primitive_of_integral_eq_zero ψ hψ hψc hψi
  have he : deriv F = ψ := funext (fun t => (hFd t).deriv)
  have hz := hw F hF hFc
  rw [he] at hz
  have hiχ := hf.integrable_smul_left_of_hasCompactSupport hχ.continuous hχc
  have hiρ := hf.integrable_smul_left_of_hasCompactSupport hρ.continuous hρc
  change (∫ t : ℝ, (χ t-d*ρ t) • f t) = 0 at hz
  simp only [sub_smul,mul_smul] at hz
  have his : Integrable (fun t : ℝ => d • (ρ t • f t)) volume := by
    simpa only [Pi.smul_apply] using! hiρ.smul d
  have hsub : (∫ t : ℝ, χ t • f t-d • (ρ t • f t)) =
      (∫ t : ℝ, χ t • f t)-(∫ t : ℝ, d • (ρ t • f t)) := by
    convert! integral_sub hiχ his using 1
  rw [hsub,integral_smul] at hz
  exact sub_eq_zero.mp hz

end NLS.FunctionalAnalysis
