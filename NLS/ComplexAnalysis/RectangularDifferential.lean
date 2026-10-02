import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-! # Differentiating rectangular action-angle coordinates

For an analytic local amplitude whose square is twice the action,
the usual cosine and sine coordinates have explicit action-angle
differentials. Only the local amplitude must be nonzero.
-/

noncomputable section
open Complex Filter Topology
namespace NLS.ComplexAnalysis
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The derivative formulas underlying the rectangular canonical brackets. -/
theorem fderiv_rectangular_of_sq
    (A θ J X Y : E → ℂ) (ψ : E)
    (hA : DifferentiableAt ℂ A ψ) (hθ : DifferentiableAt ℂ θ ψ)
    (hJ : DifferentiableAt ℂ J ψ) (hne : A ψ ≠ 0)
    (hsq : (fun χ => A χ ^ 2) =ᶠ[𝓝 ψ] (fun χ => 2 * J χ))
    (hX : X =ᶠ[𝓝 ψ] (fun χ => A χ * Complex.cos (θ χ)))
    (hY : Y =ᶠ[𝓝 ψ] (fun χ => A χ * Complex.sin (θ χ))) :
    fderiv ℂ X ψ = (X ψ / (2 * J ψ)) • fderiv ℂ J ψ + (-Y ψ) • fderiv ℂ θ ψ ∧
      fderiv ℂ Y ψ = (Y ψ / (2 * J ψ)) • fderiv ℂ J ψ + X ψ • fderiv ℂ θ ψ := by
  have hs := hsq.eq_of_nhds
  have hx := hX.eq_of_nhds
  have hy := hY.eq_of_nhds
  have hdx := hA.hasFDerivAt.fun_mul hθ.hasFDerivAt.ccos
  have hdy := hA.hasFDerivAt.fun_mul hθ.hasFDerivAt.csin
  have hd := hsq.fderiv_eq (𝕜 := ℂ)
  rw [(hA.hasFDerivAt.pow 2).fderiv, (hJ.hasFDerivAt.const_mul 2).fderiv] at hd
  have haction (v : E) : A ψ * fderiv ℂ A ψ v = fderiv ℂ J ψ v := by
    have h := congrArg (fun L : E →L[ℂ] ℂ => L v) hd
    simp only [smul_apply,smul_eq_mul] at h
    norm_num at h
    linear_combination h/2
  rw [hX.fderiv_eq,hdx.fderiv,hY.fderiv_eq,hdy.fderiv]
  constructor <;> apply ContinuousLinearMap.ext <;> intro v
  · simp only [add_apply,smul_apply,smul_eq_mul]
    rw [hx,hy,← hs,← haction v]
    field_simp
    ring
  · simp only [add_apply,smul_apply,smul_eq_mul]
    rw [hx,hy,← hs,← haction v]
    field_simp
    ring

end NLS.ComplexAnalysis
