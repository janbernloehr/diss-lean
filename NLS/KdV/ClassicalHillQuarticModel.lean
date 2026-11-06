import NLS.KdV.ClassicalHillPhaseCoefficients
import NLS.ComplexAnalysis.LaurentQuarticRemainder

/-! # Uniform quartic bounds for the physical fifth-order Hill model -/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ContDiff
namespace NLS.KdV

theorem classicalHill_phase_five_coefficients
    (q : ℝ → ℂ) (hq : ContDiff ℝ ∞ q) (hp : Function.Periodic q 1)
    (hmean : (∫ x in (0 : ℝ)..1, q x) = 0) :
    let A := nlsHamiltonianCorrection (fun _ => -1) (-q) 5
    iteratedDeriv 1 A 0 = 0 ∧ iteratedDeriv 2 A 0 = 0 ∧
      iteratedDeriv 3 A 0 = 3*I*classicalQuadraticInvariant q/2 ∧
      iteratedDeriv 4 A 0 = 0 ∧ iteratedDeriv 5 A 0 = 15*I*classicalHamiltonian q/2 := by
  obtain ⟨h1,h2,h3,h4,h5⟩ := classicalNLSHamiltonian_const_upper_first_five q hq hp hmean
  have hc := iteratedDeriv_nlsHamiltonianCorrection (fun _ => -1) (-q) 5
  refine ⟨?_,?_,?_,?_,?_⟩
  · simpa only [h1,mul_zero,zero_div] using hc 0 (by omega)
  · simpa only [h2,mul_zero,zero_div] using hc 1 (by omega)
  · rw [hc 2 (by omega),h3]
    norm_num [Nat.factorial]
    ring
  · simpa only [h4,mul_zero,zero_div] using hc 3 (by omega)
  · rw [hc 4 (by omega),h5]
    norm_num [Nat.factorial]
    ring

theorem exists_classicalHill_phase_five_quartic_error_bound
    (q : ℝ → ℂ) (hq : ContDiff ℝ ∞ q) (hp : Function.Periodic q 1)
    (hmean : (∫ x in (0 : ℝ)..1, q x) = 0) :
    ∃ R : ℝ, 0 < R ∧ ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, R < ‖z‖ →
      ‖z‖^3*‖(nlsHamiltonianPhase (fun _ => -1) (-q) 5 z)^4-z^4+
        classicalQuadraticInvariant q+classicalHamiltonian q/(4*z^2)‖ ≤ C := by
  obtain ⟨h1,h2,h3,h4,h5⟩ := classicalHill_phase_five_coefficients q hq hp hmean
  simpa only [nlsHamiltonianPhase_eq_correction] using
    exists_phase_fourth_error_bound (nlsHamiltonianCorrection (fun _ => -1) (-q) 5)
      (analyticAt_nlsHamiltonianCorrection _ _ _ 0) (nlsHamiltonianCorrection_zero _ _ _)
      (classicalQuadraticInvariant q) (classicalHamiltonian q) h1 h2 h3 h4 h5

theorem norm_classicalHill_phase_five_le (q : ℝ → ℂ) (hq : ContDiff ℝ ∞ q)
    (hp : Function.Periodic q 1) (hmean : (∫ x in (0 : ℝ)..1, q x) = 0)
    (z : ℂ) (hz : 1 ≤ ‖z‖) :
    ‖nlsHamiltonianPhase (fun _ => -1) (-q) 5 z‖ ≤
      (1+‖I*classicalQuadraticInvariant q/4‖+‖I*classicalHamiltonian q/16‖)*‖z‖ := by
  have hz0 : z ≠ 0 := norm_pos_iff.mp (by linarith)
  have he : nlsHamiltonianPhase (fun _ => -1) (-q) 5 z =
      -I*z+(I*classicalQuadraticInvariant q/4)/z^3+(I*classicalHamiltonian q/16)/z^5 := by
    have hh := phase_const_upper_five q hq hp hmean z hz0
    have hi := congrArg (fun w : ℂ => -I*w) hh
    simp only [←mul_assoc,neg_mul,I_mul_I,neg_neg,one_mul] at hi
    rw [hi]
    ring
  rw [he]
  have ha := norm_weighted_laurent_term_le z (I*classicalQuadraticInvariant q/4) hz 0 3 (by omega)
  have hb := norm_weighted_laurent_term_le z (I*classicalHamiltonian q/16) hz 0 5 (by omega)
  simp only [pow_zero,one_mul] at ha hb
  have h1 := norm_add_le (-I*z) ((I*classicalQuadraticInvariant q/4)/z^3)
  have h2 := norm_add_le (-I*z+(I*classicalQuadraticInvariant q/4)/z^3)
    ((I*classicalHamiltonian q/16)/z^5)
  simp only [norm_mul,norm_neg,norm_I,one_mul] at h1
  nlinarith [norm_nonneg (I*classicalQuadraticInvariant q/4),norm_nonneg (I*classicalHamiltonian q/16)]

end NLS.KdV
