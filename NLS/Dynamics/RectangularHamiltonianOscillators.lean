import NLS.Dynamics.HamiltonianPhaseFlow

/-! # Literal rectangular Hamiltonian oscillator equations

This implements the original dynamics statements in the introduction, printed p. 9.
-/

noncomputable section
open Complex
open scoped ENNReal
namespace NLS.Birkhoff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Decoding retains the literal first rectangular coefficient. -/
theorem decodeReal_fst (z : Coeff p × Coeff p) (n : ℤ) :
    (decodeReal z).1 n = (complexCoordinateScale*(z.1 n+z.2 n)).re := by
  change ((rectangularToComplex.symm z).1 n).re = _
  rw [rectangularToComplex_symm_fst]

/-- Decoding retains the literal second rectangular coefficient. -/
theorem decodeReal_snd (z : Coeff p × Coeff p) (n : ℤ) :
    (decodeReal z).2 n = (I*complexCoordinateScale*(z.1 n-z.2 n)).re := by
  change ((rectangularToComplex.symm z).2 n).re = _
  rw [rectangularToComplex_symm_snd]

/-- Every first rectangular coordinate has the physical oscillator velocity -omega*y. -/
theorem hasDerivAt_rectangularHamiltonianPhase_fst (freq : ℤ → ℝ)
    (z : Coeff p × Coeff p) (n : ℤ) (t : ℝ) :
    HasDerivAt (fun τ => (decodeReal (hamiltonianPhaseFlow freq τ z)).1 n)
      (-freq n*(decodeReal (hamiltonianPhaseFlow freq t z)).2 n) t := by
  have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t
    (((hasDerivAt_hamiltonianPhaseFlow_fst freq z n t).add
      (hasDerivAt_hamiltonianPhaseFlow_snd freq z n t)).const_mul complexCoordinateScale)
  simp only [decodeReal_fst,decodeReal_snd]
  convert! h using 1
  change -freq n*(I*complexCoordinateScale*((hamiltonianPhaseFlow freq t z).1 n-
      (hamiltonianPhaseFlow freq t z).2 n)).re =
    (complexCoordinateScale*(-I*(freq n:ℂ)*(hamiltonianPhaseFlow freq t z).1 n+
      I*(freq n:ℂ)*(hamiltonianPhaseFlow freq t z).2 n)).re
  rw [show -freq n*(I*complexCoordinateScale*((hamiltonianPhaseFlow freq t z).1 n-
      (hamiltonianPhaseFlow freq t z).2 n)).re =
      ((-(freq n:ℂ))*(I*complexCoordinateScale*((hamiltonianPhaseFlow freq t z).1 n-
      (hamiltonianPhaseFlow freq t z).2 n))).re by simp [Complex.mul_re]]
  congr 1
  ring

/-- Every second rectangular coordinate has the physical oscillator velocity omega*x. -/
theorem hasDerivAt_rectangularHamiltonianPhase_snd (freq : ℤ → ℝ)
    (z : Coeff p × Coeff p) (n : ℤ) (t : ℝ) :
    HasDerivAt (fun τ => (decodeReal (hamiltonianPhaseFlow freq τ z)).2 n)
      (freq n*(decodeReal (hamiltonianPhaseFlow freq t z)).1 n) t := by
  have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t
    (((hasDerivAt_hamiltonianPhaseFlow_fst freq z n t).sub
      (hasDerivAt_hamiltonianPhaseFlow_snd freq z n t)).const_mul (I*complexCoordinateScale))
  simp only [decodeReal_fst,decodeReal_snd]
  convert! h using 1
  change freq n*(complexCoordinateScale*((hamiltonianPhaseFlow freq t z).1 n+
      (hamiltonianPhaseFlow freq t z).2 n)).re =
    (I*complexCoordinateScale*(-I*(freq n:ℂ)*(hamiltonianPhaseFlow freq t z).1 n-
      I*(freq n:ℂ)*(hamiltonianPhaseFlow freq t z).2 n)).re
  rw [show freq n*(complexCoordinateScale*((hamiltonianPhaseFlow freq t z).1 n+
      (hamiltonianPhaseFlow freq t z).2 n)).re =
      ((freq n:ℂ)*(complexCoordinateScale*((hamiltonianPhaseFlow freq t z).1 n+
      (hamiltonianPhaseFlow freq t z).2 n))).re by simp [Complex.mul_re]]
  congr 1
  ring_nf
  rw [I_sq]
  ring

end NLS.Birkhoff
