import NLS.DifferentialPolynomial.DifferentialRiccati
import NLS.DifferentialPolynomial.RiccatiResolvent
import NLS.DifferentialPolynomial.LogarithmicDerivative
import Mathlib.RingTheory.PowerSeries.Inverse

/-! # The Miura gauge transformation of the canonical Riccati series

The scalar Hill potential is independently specified as D u + u². Its
Riccati series has seed -(D u + u²) and quadratic coefficient one.
-/
noncomputable section
namespace NLS.DifferentialPolynomial
variable {K A : Type*} [CommRing K] [CommRing A] [Algebra K A]

/-- The differential-algebra form of the scalar Miura gauge transformation. -/
theorem miura_riccati_identity (D : Derivation K A A) (t u r v : A)
    (ht : D t = 0) (hr : r = -u+t*D r+u*t^2*r^2)
    (hv : (1+t*r)*v = 1) :
    u*r+D r*v = -(D u+u^2)+t*D (u*r+D r*v)+t^2*(u*r+D r*v)^2 := by
  have hdr := congrArg D hr
  simp [Derivation.leibniz, smul_eq_mul, ht, pow_two] at hdr
  have hdv : D v = -v^2*(t*D r) := by
    have he := derivation_inverse_of_mul_eq_one D (1+t*r) v hv
    simpa [Derivation.leibniz, smul_eq_mul, ht] using he
  have hd : D (u*r+D r*v) = u*D r+r*D u+D r*D v+v*D (D r) := by
    simp only [map_add, Derivation.leibniz, smul_eq_mul]
    ring
  rw [hd, hdv]
  linear_combination v*hdr + u*hr + D u*(t*r-1)*hv

def miuraRiccatiGaugeInverse (D : Derivation K A A) (u : A) : PowerSeries A :=
  PowerSeries.invOfUnit (1+PowerSeries.X*differentialRiccatiSeries D u u) 1

theorem miuraRiccatiGauge_mul_inverse (D : Derivation K A A) (u : A) :
    (1+PowerSeries.X*differentialRiccatiSeries D u u)*miuraRiccatiGaugeInverse D u = 1 :=
  PowerSeries.mul_invOfUnit _ _ (by simp)

/-- All-order scalar Hill / diagonal NLS Miura identity. The second term is
the coefficientwise logarithmic derivative of the gauge factor 1+X R. -/
theorem differentialRiccatiSeries_miura (D : Derivation K A A) (u : A) :
    differentialRiccatiSeries D 1 (D u+u^2) =
      PowerSeries.C u*differentialRiccatiSeries D u u +
        powerSeriesDerivation D (differentialRiccatiSeries D u u)*miuraRiccatiGaugeInverse D u := by
  symm
  apply differentialRiccatiSeries_unique D 1 (D u+u^2)
  have hr := differentialRiccatiSeries_equation D u u
  have he := miura_riccati_identity (powerSeriesDerivation D) PowerSeries.X (PowerSeries.C u)
    (differentialRiccatiSeries D u u) (miuraRiccatiGaugeInverse D u)
    (powerSeriesDerivation_X D) (by rw [map_neg] at hr; linear_combination hr)
    (miuraRiccatiGauge_mul_inverse D u)
  simp only [powerSeriesDerivation_C, map_add, map_pow, map_one, one_mul, map_neg] at he ⊢
  linear_combination he

/-- Scalar Hill and diagonal NLS densities differ by an explicit total
derivative. The scalar recurrence is specified independently on the left. -/
theorem differentialRiccatiSequence_miura {F : Type*} [Field F] [CharZero F]
    [Algebra F A] (D : Derivation F A A) (u : A) (n : ℕ) :
    differentialRiccatiSequence D 1 (D u+u^2) n =
      u*differentialRiccatiSequence D u u n +
        D (logarithmicPrimitiveCoefficient (K := F) (differentialRiccatiSeries D u u) n) := by
  have he := congrArg (PowerSeries.coeff n) (differentialRiccatiSeries_miura D u)
  rw [map_add, PowerSeries.coeff_C_mul, coeff_differentialRiccatiSeries,
    coeff_differentialRiccatiSeries] at he
  rw [derivation_logarithmicPrimitiveCoefficient D _ _ (miuraRiccatiGauge_mul_inverse D u)]
  exact he

end NLS.DifferentialPolynomial
