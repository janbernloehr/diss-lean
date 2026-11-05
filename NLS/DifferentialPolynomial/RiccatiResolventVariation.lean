import NLS.DifferentialPolynomial.ConstructedRiccatiResolvent

/-! # All-order Riccati variations modulo an explicit spatial derivative

Any perturbation derivation commuting with spatial differentiation gives the
same two constructed resolvent components as variational coefficients. The
discarded spatial derivative is explicit, coefficient by coefficient.
-/
noncomputable section
namespace NLS.DifferentialPolynomial
variable {K A : Type*} [CommRing K] [CommRing A] [Algebra K A]

theorem differentialRiccatiSeries_linearized (D E : Derivation K A A)
    (hcomm : ∀ a, E (D a) = D (E a)) (a b : A) :
    powerSeriesDerivation E (differentialRiccatiSeries D a b) =
      -PowerSeries.C (E b)+
      PowerSeries.X*powerSeriesDerivation D
        (powerSeriesDerivation E (differentialRiccatiSeries D a b))+
      PowerSeries.C (E a)*PowerSeries.X^2*(differentialRiccatiSeries D a b)^2+
      2*PowerSeries.C a*PowerSeries.X^2*differentialRiccatiSeries D a b*
        powerSeriesDerivation E (differentialRiccatiSeries D a b) := by
  have he := congrArg (powerSeriesDerivation E) (differentialRiccatiSeries_equation D a b)
  simp only [map_add, Derivation.leibniz, smul_eq_mul, powerSeriesDerivation_C,
    powerSeriesDerivation_X, Derivation.leibniz_pow, map_neg,
    powerSeriesDerivation_commute D E hcomm] at he
  linear_combination he

/-- The constructed resolvent is the coefficient of every differential
variation of the actual Riccati Hamiltonian density, modulo a total derivative. -/
theorem constructed_riccati_resolvent_variation (D E : Derivation K A A)
    (hcomm : ∀ a, E (D a) = D (E a)) (a b : A) :
    powerSeriesDerivation E (PowerSeries.C a*differentialRiccatiSeries D a b) =
      PowerSeries.C (E a)*riccatiResolventA D a b+
      PowerSeries.C (E b)*riccatiResolventB D a b-
      powerSeriesDerivation D
        (PowerSeries.X*riccatiResolventB D a b*
          powerSeriesDerivation E (differentialRiccatiSeries D a b)) := by
  have hr := differentialRiccatiSeries_equation D a b
  have hs := differentialRiccatiSeries_equation (-D) b a
  simp only [powerSeriesDerivation_neg, map_neg] at hr hs
  have hv := riccatiResolvent_mul_inverse D a b
  have hw := differentialRiccatiSeries_linearized D E hcomm a b
  have he := riccati_resolvent_variation_identity (powerSeriesDerivation D) PowerSeries.X
    (PowerSeries.C a) (PowerSeries.C b)
    (differentialRiccatiSeries D a b) (differentialRiccatiSeries (-D) b a)
    (riccatiResolventInverse D a b) (PowerSeries.C (E a)) (PowerSeries.C (E b))
    (powerSeriesDerivation E (differentialRiccatiSeries D a b))
    (powerSeriesDerivation_X D) (by linear_combination hr) (by linear_combination hs) hv hw
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, powerSeriesDerivation_C]
  dsimp only [riccatiResolventA, riccatiResolventB]
  linear_combination he

/-- Each individual Riccati density has the same variational identity, with
an explicitly specified coefficient of the total-derivative primitive. -/
theorem riccati_resolvent_coefficient_variation (D E : Derivation K A A)
    (hcomm : ∀ a, E (D a) = D (E a)) (a b : A) (n : ℕ) :
    E (a*differentialRiccatiSequence D a b n) =
      E a*PowerSeries.coeff n (riccatiResolventA D a b)+
      E b*PowerSeries.coeff n (riccatiResolventB D a b)-
      D (PowerSeries.coeff n
        (PowerSeries.X*riccatiResolventB D a b*
          powerSeriesDerivation E (differentialRiccatiSeries D a b))) := by
  have he := congrArg (PowerSeries.coeff n) (constructed_riccati_resolvent_variation D E hcomm a b)
  simpa only [coeff_powerSeriesDerivation, PowerSeries.coeff_C_mul, coeff_differentialRiccatiSeries,
    map_sub, map_add] using he

end NLS.DifferentialPolynomial
