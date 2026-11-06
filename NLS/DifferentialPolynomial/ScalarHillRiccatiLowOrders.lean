import NLS.DifferentialPolynomial.DifferentialRiccati

/-! # Exact low scalar Hill Riccati densities in any differential algebra

The fourth and sixth coefficients reduce, by explicit total derivatives,
to the printed KdV and KdV2 densities. All constants follow from the
independently seeded scalar recurrence.
-/
noncomputable section
namespace NLS.DifferentialPolynomial
variable {K A : Type*} [CommRing K] [CommRing A] [Algebra K A]

theorem scalarHillRiccati_two (D : Derivation K A A) (q : A) :
    differentialRiccatiSequence D 1 q 2 = -D (D q)+q^2 := by
  rw [differentialRiccatiSequence_recurrence D 1 q 0]
  simp
  ring

theorem scalarHillRiccati_three (D : Derivation K A A) (q : A) :
    differentialRiccatiSequence D 1 q 3 = -D (D (D q))+4*q*D q := by
  rw [differentialRiccatiSequence_recurrence D 1 q 1]
  simp [Finset.Nat.antidiagonal_succ,scalarHillRiccati_two,Derivation.leibniz_pow,smul_eq_mul]
  ring

theorem scalarHillRiccati_four (D : Derivation K A A) (q : A) :
    differentialRiccatiSequence D 1 q 4 =
      -D (D (D (D q)))+5*(D q)^2+6*q*D (D q)-2*q^3 := by
  have h4 : D (4 : A) = 0 := D.map_natCast 4
  rw [differentialRiccatiSequence_recurrence D 1 q 2]
  simp [Finset.Nat.antidiagonal_succ,scalarHillRiccati_two,scalarHillRiccati_three,
    Derivation.leibniz,smul_eq_mul,h4]
  ring

theorem scalarHillRiccati_five (D : Derivation K A A) (q : A) :
    differentialRiccatiSequence D 1 q 5 = -D (D (D (D (D q))))+
      18*D q*D (D q)+8*q*D (D (D q))-16*q^2*D q := by
  have h5 : D (5 : A) = 0 := D.map_natCast 5
  have h6 : D (6 : A) = 0 := D.map_natCast 6
  have h2 : D (2 : A) = 0 := D.map_natCast 2
  rw [differentialRiccatiSequence_recurrence D 1 q 3]
  simp [Finset.Nat.antidiagonal_succ,scalarHillRiccati_two,scalarHillRiccati_three,
    scalarHillRiccati_four,Derivation.leibniz,Derivation.leibniz_pow,smul_eq_mul,h5,h6,h2]
  ring

theorem scalarHillRiccati_six (D : Derivation K A A) (q : A) :
    differentialRiccatiSequence D 1 q 6 = -D (D (D (D (D (D q)))))+
      19*(D (D q))^2+28*D q*D (D (D q))+10*q*D (D (D (D q)))-
      50*q*(D q)^2-30*q^2*D (D q)+5*q^4 := by
  have h18 : D (18 : A) = 0 := D.map_natCast 18
  have h8 : D (8 : A) = 0 := D.map_natCast 8
  have h16 : D (16 : A) = 0 := D.map_natCast 16
  rw [differentialRiccatiSequence_recurrence D 1 q 4]
  simp [Finset.Nat.antidiagonal_succ,scalarHillRiccati_two,scalarHillRiccati_three,
    scalarHillRiccati_four,scalarHillRiccati_five,
    Derivation.leibniz,Derivation.leibniz_pow,smul_eq_mul,h18,h8,h16]
  ring

/-- The fourth coefficient is minus twice the physical KdV density,
up to this literal total derivative. -/
theorem scalarHillRiccati_four_reduction (D : Derivation K A A) (q : A) :
    differentialRiccatiSequence D 1 q 4 = -((D q)^2+2*q^3)+
      D (-D (D (D q))+6*q*D q) := by
  have h6 : D (6 : A) = 0 := D.map_natCast 6
  rw [scalarHillRiccati_four]
  simp [Derivation.leibniz,smul_eq_mul,h6]
  ring

/-- The sixth coefficient is twice the printed physical KdV2 density,
up to this literal total derivative. -/
theorem scalarHillRiccati_six_reduction (D : Derivation K A A) (q : A) :
    differentialRiccatiSequence D 1 q 6 = (D (D q))^2+10*q*(D q)^2+5*q^4+
      D (-D (D (D (D (D q))))+18*D q*D (D q)+
        10*q*D (D (D q))-30*q^2*D q) := by
  have h18 : D (18 : A) = 0 := D.map_natCast 18
  have h10 : D (10 : A) = 0 := D.map_natCast 10
  have h30 : D (30 : A) = 0 := D.map_natCast 30
  rw [scalarHillRiccati_six]
  simp [Derivation.leibniz,Derivation.leibniz_pow,smul_eq_mul,h18,h10,h30]
  ring

end NLS.DifferentialPolynomial
