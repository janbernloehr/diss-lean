import NLS.ComplexAnalysis.JointSpectralDerivative
import Mathlib.Analysis.Calculus.FDeriv.Pow

/-!
# Derivative of a nonvanishing analytic square root

If `Q² = Δ² - 4` near a point and `Q` does not vanish there, its
Fréchet derivative is `Δ / Q` times the derivative of `Δ`.
-/

noncomputable section
open Set
open scoped Topology
namespace NLS.ComplexAnalysis

variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]


/-- Differentiate the defining square identity of a nonvanishing
square root in an arbitrary complex Banach direction. -/
theorem fderiv_squareRoot_of_sq_eq_discriminant_sq_sub_four
    (Q Δ : A → ℂ) (D : Set A) (hD : IsOpen D)
    (hsq : ∀ x ∈ D, Q x ^ 2 = Δ x ^ 2 - 4)
    (x : A) (hx : x ∈ D)
    (hQ : DifferentiableAt ℂ Q x)
    (hΔ : DifferentiableAt ℂ Δ x)
    (hQne : Q x ≠ 0) (v : A) :
    (fderiv ℂ Q x) v = Δ x / Q x * (fderiv ℂ Δ x) v := by
  have heq : (fun y : A => Q y ^ 2) =ᶠ[𝓝 x]
      (fun y : A => Δ y ^ 2 - 4) := by
    filter_upwards [hD.mem_nhds hx] with y hy
    exact hsq y hy
  have hderiv := congrArg (fun L : A →L[ℂ] ℂ => L v) heq.fderiv_eq
  have hqpow : fderiv ℂ (fun y : A => Q y ^ 2) x =
      (2 * Q x) • fderiv ℂ Q x := by
    simpa using fderiv_fun_pow 2 hQ
  have hdpow : fderiv ℂ (fun y : A => Δ y ^ 2) x =
      (2 * Δ x) • fderiv ℂ Δ x := by
    simpa using fderiv_fun_pow 2 hΔ
  have hsub : fderiv ℂ (fun y : A => Δ y ^ 2 - 4) x =
      fderiv ℂ (fun y : A => Δ y ^ 2) x -
        fderiv ℂ (fun _ : A => (4 : ℂ)) x := by
    exact fderiv_fun_sub (by fun_prop) (by fun_prop)
  rw [hqpow, hsub, hdpow] at hderiv
  simp only [smul_apply, fderiv_const_apply, sub_zero, smul_eq_mul] at hderiv
  apply (mul_left_cancel₀ (mul_ne_zero (by norm_num : (2:ℂ) ≠ 0) hQne))
  calc
    (2 * Q x) * (fderiv ℂ Q x) v =
        (2 * Δ x) * (fderiv ℂ Δ x) v := hderiv
    _ = (2 * Q x) * (Δ x / Q x * (fderiv ℂ Δ x) v) := by
      field_simp

end NLS.ComplexAnalysis
