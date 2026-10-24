import NLS.ZakharovShabat.L2FloquetInhomogeneous
import NLS.ZakharovShabat.L2WholeLineDiagonalInverse

/-! # A bounded physical inverse from the periodic Floquet reduction -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Matrix Module Complex
open scoped Matrix.Norms.Elementwise
namespace NLS.ZakharovShabat

/-- The original pencil forcing has signs (i*g1,-i*g2). -/
def wholeLinePencilForcing : WholeLineL2 →L[ℂ] WholeLineL2 :=
  wholeLineMatrixMulCLM (fun _ => !![I,0;0,-I]) continuous_const
    ‖(!![I,0;0,-I] : Matrix (Fin 2) (Fin 2) ℂ)‖ (fun _ => le_rfl)

theorem wholeLinePencilForcing_pair_ae (g : WholeLineL2) :
    wholeLineL2Pair (wholeLinePencilForcing g) =ᵐ[volume]
      (fun t => (I*(wholeLineL2Pair g t).1,-I*(wholeLineL2Pair g t).2)) := by
  simpa [wholeLinePencilForcing,wholeLineMatrixAction] using wholeLineMatrixMulCLM_pair_ae
    (fun _ => !![I,0;0,-I]) continuous_const
    ‖(!![I,0;0,-I] : Matrix (Fin 2) (Fin 2) ℂ)‖ (fun _ => le_rfl) g

/-- Transfer the bounded diagonal inverse through the original periodic matrix. -/
def wholeLineFloquetInverse (u : IntervalPairL2) (z : ℂ)
    (b : Basis (Fin 2) ℂ (Fin 2 → ℂ)) (μ : Fin 2 → ℂ)
    (h0 : (Complex.log (μ 0)).re ≠ 0) (h1 : (Complex.log (μ 1)).re ≠ 0)
    (C : ℝ) (hC : ∀ t, ‖l2FloquetPeriodicMatrix u z b μ t‖ ≤ C ∧
      ‖(l2FloquetPeriodicMatrix u z b μ t)⁻¹‖ ≤ C) : WholeLineL2 →L[ℂ] WholeLineL2 :=
  (wholeLineMatrixMulCLM _ (continuous_l2FloquetPeriodicMatrix u z b μ) C
    (fun t => (hC t).1)).comp
    ((wholeLineDiagonalODEInverse (Complex.log (μ 0)) (Complex.log (μ 1)) h0 h1).comp
      ((wholeLineMatrixMulCLM _ (continuous_inv_l2FloquetPeriodicMatrix u z b μ) C
        (fun t => (hC t).2)).comp wholeLinePencilForcing))

/-- The constructed bounded vector has a locally AC representative solving
the original inhomogeneous physical differential equation. -/
theorem wholeLineFloquetInverse_exists_AC_solution (u : IntervalPairL2) (z : ℂ)
    (b : Basis (Fin 2) ℂ (Fin 2 → ℂ)) (μ : Fin 2 → ℂ)
    (h0 : (Complex.log (μ 0)).re ≠ 0) (h1 : (Complex.log (μ 1)).re ≠ 0)
    (C : ℝ) (hC : ∀ t, ‖l2FloquetPeriodicMatrix u z b μ t‖ ≤ C ∧
      ‖(l2FloquetPeriodicMatrix u z b μ t)⁻¹‖ ≤ C) (g : WholeLineL2) :
    ∃ F : ℝ → ℂ × ℂ,
      wholeLineL2Pair (wholeLineFloquetInverse u z b μ h0 h1 C hC g) =ᵐ[volume] F ∧
      (∀ a c : ℝ, AbsolutelyContinuousOnInterval F a c) ∧
      physicalOperator (l2WholeLinePotential u) F =ᵐ[volume]
        (fun t => z • F t-wholeLineL2Pair g t) := by
  let B := l2FloquetPeriodicMatrix u z b μ
  let h := wholeLineMatrixMulCLM _ (continuous_inv_l2FloquetPeriodicMatrix u z b μ) C
    (fun t => (hC t).2) (wholeLinePencilForcing g)
  let yL := wholeLineDiagonalODEInverse (Complex.log (μ 0)) (Complex.log (μ 1)) h0 h1 h
  obtain ⟨y,he,_,hac,hd⟩ := wholeLineDiagonalODEInverse_exists_AC_solution
    (Complex.log (μ 0)) (Complex.log (μ 1)) h0 h1 h
  let F := l2FloquetRecombine u z b μ y
  refine ⟨F,?_,fun a c => absolutelyContinuousOnInterval_l2FloquetRecombine u z b μ y a c (hac a c),?_⟩
  · filter_upwards [wholeLineMatrixMulCLM_pair_ae B
      (continuous_l2FloquetPeriodicMatrix u z b μ) C (fun t => (hC t).1) yL,he]
      with t ht hyt
    change wholeLineL2Pair (wholeLineMatrixMulCLM B
      (continuous_l2FloquetPeriodicMatrix u z b μ) C (fun t => (hC t).1) yL) t = F t
    rw [ht,hyt]
    exact (l2FloquetRecombine_eq_matrix_action u z b μ y t).symm
  · have hF := ae_hasDerivAt_l2FloquetRecombine u z b μ y (wholeLineL2Pair h) hd
    filter_upwards [hF,wholeLineMatrixMulCLM_pair_ae (fun t => (B t)⁻¹)
      (continuous_inv_l2FloquetPeriodicMatrix u z b μ) C (fun t => (hC t).2)
        (wholeLinePencilForcing g),wholeLinePencilForcing_pair_ae g] with t ht hht hgt
    change HasDerivAt F (classicalODECoefficient (l2WholeLinePotential u t) z (F t)+
      wholeLineMatrixAction (B t) (wholeLineL2Pair h t)) t at ht
    change wholeLineL2Pair h t = _ at hht
    rw [hht,hgt,wholeLineMatrixAction_mul,
      Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp
        (isUnit_l2FloquetPeriodicMatrix u z b μ t)),wholeLineMatrixAction_one] at ht
    exact physicalOperator_of_inhomogeneous_ode _ F z (wholeLineL2Pair g t) t ht

end NLS.ZakharovShabat
