import NLS.Dynamics.RealComplexBirkhoffCoordinates
import NLS.ComplexAnalysis.ScalarDuhamel

/-! # Hamiltonian time orientation of complex phase trajectories

The coordinates z=(x-iy)/sqrt(2), w=(x+iy)/sqrt(2) require the signs
(-i*frequency*z,+i*frequency*w) for the source Hamiltonian convention.
This is the time reversal of the literal phase flow in equation (4.14).
-/
noncomputable section
open Complex
open scoped ENNReal
namespace NLS.Birkhoff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The phase flow with the time orientation fixed by the source Poisson bracket. -/
def hamiltonianPhaseFlow (freq : ℤ → ℝ) (t : ℝ) (z : Coeff p × Coeff p) : Coeff p × Coeff p :=
  phaseFlow freq (-t) z

@[simp] theorem hamiltonianPhaseFlow_fst (freq : ℤ → ℝ) (t : ℝ)
    (z : Coeff p × Coeff p) (n : ℤ) :
    (hamiltonianPhaseFlow freq t z).1 n = exp (((-t*freq n : ℝ) : ℂ)*I)*z.1 n := rfl

@[simp] theorem hamiltonianPhaseFlow_snd (freq : ℤ → ℝ) (t : ℝ)
    (z : Coeff p × Coeff p) (n : ℤ) :
    (hamiltonianPhaseFlow freq t z).2 n = exp (((t*freq n : ℝ) : ℂ)*I)*z.2 n := by
  simp [hamiltonianPhaseFlow]

/-- The physical first-coordinate velocity has the negative Hamiltonian phase. -/
theorem hasDerivAt_hamiltonianPhaseFlow_fst (freq : ℤ → ℝ) (z : Coeff p × Coeff p)
    (n : ℤ) (t : ℝ) :
    HasDerivAt (fun τ => (hamiltonianPhaseFlow freq τ z).1 n)
      (-I*(freq n : ℂ)*(hamiltonianPhaseFlow freq t z).1 n) t := by
  have h := (NLS.ComplexAnalysis.hasDerivAt_complex_exp_mul (-I*(freq n : ℂ)) t).mul_const (z.1 n)
  have he (τ : ℝ) : -I*(freq n : ℂ)*τ = (((-τ*freq n : ℝ) : ℂ)*I) := by push_cast; ring
  simp_rw [he] at h
  simpa only [hamiltonianPhaseFlow_fst,mul_assoc,mul_left_comm,mul_comm] using! h

/-- The physical second-coordinate velocity has the positive Hamiltonian phase. -/
theorem hasDerivAt_hamiltonianPhaseFlow_snd (freq : ℤ → ℝ) (z : Coeff p × Coeff p)
    (n : ℤ) (t : ℝ) :
    HasDerivAt (fun τ => (hamiltonianPhaseFlow freq τ z).2 n)
      (I*(freq n : ℂ)*(hamiltonianPhaseFlow freq t z).2 n) t := by
  have h := (NLS.ComplexAnalysis.hasDerivAt_complex_exp_mul (I*(freq n : ℂ)) t).mul_const (z.2 n)
  have he (τ : ℝ) : I*(freq n : ℂ)*τ = (((τ*freq n : ℝ) : ℂ)*I) := by push_cast; ring
  simp_rw [he] at h
  simpa only [hamiltonianPhaseFlow_snd,mul_assoc,mul_left_comm,mul_comm] using h

@[simp] theorem hamiltonianPhaseFlow_zero (freq : ℤ → ℝ) (z : Coeff p × Coeff p) :
    hamiltonianPhaseFlow freq 0 z = z := by simp [hamiltonianPhaseFlow]

theorem hamiltonianPhaseFlow_add (freq : ℤ → ℝ) (t u : ℝ) (z : Coeff p × Coeff p) :
    hamiltonianPhaseFlow freq t (hamiltonianPhaseFlow freq u z) =
      hamiltonianPhaseFlow freq (t+u) z := by
  simp only [hamiltonianPhaseFlow,phaseFlow_add,neg_add]

/-- The printed first-coordinate velocity has the opposite sign. -/
theorem hasDerivAt_printedPhaseFlow_fst (freq : ℤ → ℝ) (z : Coeff p × Coeff p)
    (n : ℤ) (t : ℝ) :
    HasDerivAt (fun τ => (phaseFlow freq τ z).1 n)
      (I*(freq n : ℂ)*(phaseFlow freq t z).1 n) t := by
  have h := (NLS.ComplexAnalysis.hasDerivAt_complex_exp_mul (I*(freq n : ℂ)) t).mul_const (z.1 n)
  have he (τ : ℝ) : I*(freq n : ℂ)*τ = (((τ*freq n : ℝ) : ℂ)*I) := by push_cast; ring
  simp_rw [he] at h
  simpa only [phaseFlow_fst,mul_assoc,mul_left_comm,mul_comm] using h

/-- With nonzero frequency and amplitude, the literal printed phase cannot have the Hamiltonian velocity. -/
theorem not_hasDerivAt_printedPhaseFlow_hamiltonian (freq : ℤ → ℝ) (z : Coeff p × Coeff p)
    (n : ℤ) (hf : freq n ≠ 0) (hz : z.1 n ≠ 0) :
    ¬ HasDerivAt (fun τ => (phaseFlow freq τ z).1 n) (-I*(freq n : ℂ)*z.1 n) 0 := by
  intro h
  have he := (hasDerivAt_printedPhaseFlow_fst freq z n 0).unique h
  simp only [phaseFlow_zero] at he
  have hn : I*(freq n : ℂ)*z.1 n ≠ 0 := mul_ne_zero (mul_ne_zero I_ne_zero (by exact_mod_cast hf)) hz
  apply hn
  linear_combination (1/2 : ℂ)*he

end NLS.Birkhoff
