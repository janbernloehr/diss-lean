import NLS.DifferentialPolynomial.DifferentialRiccati
import NLS.DifferentialPolynomial.RiccatiResolvent
import Mathlib.RingTheory.PowerSeries.Inverse

/-! # An independently constructed all-order Riccati resolvent

Both Riccati series are given by the canonical differential recurrence. The
denominator has constant coefficient one, so its formal inverse exists over
the coefficient algebra without a division assumption on the fields.
-/
noncomputable section
namespace NLS.DifferentialPolynomial
variable {K A : Type*} [CommRing K] [CommRing A] [Algebra K A]

def riccatiResolventDenominator (D : Derivation K A A) (a b : A) : PowerSeries A :=
  1+PowerSeries.X^2*differentialRiccatiSeries D a b*differentialRiccatiSeries (-D) b a

@[simp] theorem constantCoeff_riccatiResolventDenominator (D : Derivation K A A) (a b : A) :
    PowerSeries.constantCoeff (riccatiResolventDenominator D a b) = 1 := by
  simp [riccatiResolventDenominator]

def riccatiResolventInverse (D : Derivation K A A) (a b : A) : PowerSeries A :=
  PowerSeries.invOfUnit (riccatiResolventDenominator D a b) 1

theorem riccatiResolvent_mul_inverse (D : Derivation K A A) (a b : A) :
    riccatiResolventDenominator D a b*riccatiResolventInverse D a b = 1 :=
  PowerSeries.mul_invOfUnit _ _ (constantCoeff_riccatiResolventDenominator D a b)

def riccatiResolventA (D : Derivation K A A) (a b : A) : PowerSeries A :=
  differentialRiccatiSeries D a b*riccatiResolventInverse D a b

def riccatiResolventB (D : Derivation K A A) (a b : A) : PowerSeries A :=
  differentialRiccatiSeries (-D) b a*riccatiResolventInverse D a b

def riccatiResolventCoupling (D : Derivation K A A) (a b : A) : PowerSeries A :=
  PowerSeries.X*differentialRiccatiSeries D a b*differentialRiccatiSeries (-D) b a*
    riccatiResolventInverse D a b

/-- All three all-order differential identities follow from the constructed
series. No resolvent, inverse or differential equation is a caller hypothesis. -/
theorem constructed_riccati_resolvent_identities (D : Derivation K A A) (a b : A) :
    riccatiResolventA D a b = -PowerSeries.C b+
      PowerSeries.X*powerSeriesDerivation D (riccatiResolventA D a b)+
      2*PowerSeries.C b*PowerSeries.X*riccatiResolventCoupling D a b ∧
    riccatiResolventB D a b = -PowerSeries.C a-
      PowerSeries.X*powerSeriesDerivation D (riccatiResolventB D a b)+
      2*PowerSeries.C a*PowerSeries.X*riccatiResolventCoupling D a b ∧
    powerSeriesDerivation D (riccatiResolventCoupling D a b) =
      PowerSeries.C b*riccatiResolventB D a b-PowerSeries.C a*riccatiResolventA D a b := by
  have hr := differentialRiccatiSeries_equation D a b
  have hs := differentialRiccatiSeries_equation (-D) b a
  simp only [powerSeriesDerivation_neg, map_neg] at hs hr
  exact riccati_resolvent_identities (powerSeriesDerivation D) PowerSeries.X
    (PowerSeries.C a) (PowerSeries.C b)
    (differentialRiccatiSeries D a b) (differentialRiccatiSeries (-D) b a)
    (riccatiResolventInverse D a b) (powerSeriesDerivation_X D)
    (by linear_combination hr) (by linear_combination hs)
    (riccatiResolvent_mul_inverse D a b)

/-- Extracting coefficients gives the first component's Lenard recurrence. -/
theorem coeff_riccatiResolventA_succ (D : Derivation K A A) (a b : A) (n : ℕ) :
    PowerSeries.coeff (n+1) (riccatiResolventA D a b) =
      D (PowerSeries.coeff n (riccatiResolventA D a b)) +
        2*b*PowerSeries.coeff n (riccatiResolventCoupling D a b) := by
  have he := (constructed_riccati_resolvent_identities D a b).1
  have he' : riccatiResolventA D a b = -PowerSeries.C b+
      (powerSeriesDerivation D (riccatiResolventA D a b)+
        PowerSeries.C (2*b)*riccatiResolventCoupling D a b)*PowerSeries.X := by
    rw [map_mul, map_ofNat]
    linear_combination he
  have hc := congrArg (PowerSeries.coeff (n+1)) he'
  simpa only [map_add, map_neg, PowerSeries.coeff_succ_C, neg_zero, zero_add,
    PowerSeries.coeff_succ_mul_X, coeff_powerSeriesDerivation, PowerSeries.coeff_C_mul] using hc

theorem coeff_riccatiResolventB_succ (D : Derivation K A A) (a b : A) (n : ℕ) :
    PowerSeries.coeff (n+1) (riccatiResolventB D a b) =
      -D (PowerSeries.coeff n (riccatiResolventB D a b)) +
        2*a*PowerSeries.coeff n (riccatiResolventCoupling D a b) := by
  have he := (constructed_riccati_resolvent_identities D a b).2.1
  have he' : riccatiResolventB D a b = -PowerSeries.C a+
      (-powerSeriesDerivation D (riccatiResolventB D a b)+
        PowerSeries.C (2*a)*riccatiResolventCoupling D a b)*PowerSeries.X := by
    rw [map_mul, map_ofNat]
    linear_combination he
  have hc := congrArg (PowerSeries.coeff (n+1)) he'
  simpa only [map_add, map_neg, PowerSeries.coeff_succ_C, neg_zero, zero_add,
    PowerSeries.coeff_succ_mul_X, coeff_powerSeriesDerivation, PowerSeries.coeff_C_mul] using hc

theorem deriv_coeff_riccatiResolventCoupling (D : Derivation K A A) (a b : A) (n : ℕ) :
    D (PowerSeries.coeff n (riccatiResolventCoupling D a b)) =
      b*PowerSeries.coeff n (riccatiResolventB D a b)-
        a*PowerSeries.coeff n (riccatiResolventA D a b) := by
  have he := congrArg (PowerSeries.coeff n) (constructed_riccati_resolvent_identities D a b).2.2
  simpa using he

end NLS.DifferentialPolynomial
