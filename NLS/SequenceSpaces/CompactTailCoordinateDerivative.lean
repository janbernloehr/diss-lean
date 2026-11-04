import NLS.SequenceSpaces.CompactGeneralTailRows
import NLS.SequenceSpaces.BoundedCoordinateDifferentiable
import NLS.ComplexAnalysis.BanachTaylorBounds

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal ComplexConjugate

namespace NLS.Coeff



variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem isCompactOperator_fderiv_of_tailCoordinateBound
    (hp : p ≠ ⊤) (f : E → Coeff p) (c : E) (R : ℝ) (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (ball c (R+R))) (b : Coeff p) (s : Finset ℤ)
    (hb : ∀ m : ℤ, m ∉ s → ∀ y ∈ ball c (R+R), ‖f y m‖ ≤ ‖b m‖) :
    IsCompactOperator (fderiv ℂ f c) := by
  have hc : DifferentiableAt ℂ f c :=
    (hf c (mem_ball_self (by linarith))).differentiableAt (isOpen_ball.mem_nhds (mem_ball_self (by linarith)))
  let b' : Coeff p := ((2/R : ℝ) : ℂ) • b
  apply isCompactOperator_of_tailRowMajorant hp (fderiv ℂ f c) b' s
  intro m hm v
  rw [fderiv_apply_of_differentiableAt f c v m hc]
  have hcoord : DifferentiableOn ℂ (fun y => f y m) (ball c (R+R)) :=
    ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) p m).differentiable.comp_differentiableOn hf)
  have hder := ComplexAnalysis.norm_fderiv_le_of_ball_bound (fun y => f y m) c c R R ‖b m‖ hR
    hcoord (hb m hm) (mem_ball_self hR)
  apply ((fderiv ℂ (fun y => f y m) c).le_opNorm v).trans
  have htwoR : (0 : ℝ) ≤ 2/R := by positivity
  have he : ‖b' m‖ = 2*‖b m‖/R := by
    simp only [b',lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,norm_mul,Complex.norm_real,
      Real.norm_eq_abs,abs_of_nonneg htwoR]
    ring
  rw [he]
  exact mul_le_mul_of_nonneg_right hder (norm_nonneg v)

end NLS.Coeff
