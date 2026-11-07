import NLS.DifferentialPolynomial.DifferentialRiccati

/-! Low coefficients of the independently seeded scalar Hill Riccati
recurrence, and its exact twice-KdV density modulo a total derivative. -/
noncomputable section
namespace NLS.DifferentialPolynomial
variable {K A : Type*} [CommRing K] [CommRing A] [Algebra K A]

theorem differentialRiccatiSequence_scalar_two (D : Derivation K A A) (q : A) :
    differentialRiccatiSequence D 1 q 2= -D (D q)+q^2 := by
  rw [differentialRiccatiSequence_recurrence D 1 q 0]
  rw [differentialRiccatiSequence_one D (1:A) q]
  simp
  ring

theorem differentialRiccatiSequence_scalar_three (D : Derivation K A A) (q : A) :
    differentialRiccatiSequence D 1 q 3= -D (D (D q))+4*q*D q := by
  rw [differentialRiccatiSequence_recurrence D 1 q 1,differentialRiccatiSequence_scalar_two]
  simp [Finset.Nat.antidiagonal_succ,Derivation.leibniz_pow,smul_eq_mul]
  ring

theorem differentialRiccatiSequence_scalar_four (D : Derivation K A A) (q : A) :
    differentialRiccatiSequence D 1 q 4=
      -D (D (D (D q)))+5*(D q)^2+6*q*D (D q)-2*q^3 := by
  rw [differentialRiccatiSequence_recurrence D 1 q 2,differentialRiccatiSequence_scalar_three]
  have h4 : D (4:A)=0 := D.map_natCast 4
  simp [Finset.Nat.antidiagonal_succ,
    differentialRiccatiSequence_scalar_two,Derivation.leibniz,smul_eq_mul,h4]
  ring

/-- The fourth scalar Riccati coefficient is minus TWICE the physical
KdV density, plus an explicitly verified total spatial derivative. -/
theorem differentialRiccatiSequence_scalar_four_KdV (D : Derivation K A A) (q : A) :
    -differentialRiccatiSequence D 1 q 4=(D q)^2+2*q^3+
      D (D (D (D q))-6*q*D q) := by
  rw [differentialRiccatiSequence_scalar_four]
  have h6 : D (6:A)=0 := D.map_natCast 6
  simp only [map_sub,Derivation.leibniz,smul_eq_mul,h6,mul_zero]
  ring

end NLS.DifferentialPolynomial
