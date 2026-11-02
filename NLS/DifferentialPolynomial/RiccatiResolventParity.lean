import NLS.DifferentialPolynomial.ConstructedRiccatiResolvent

/-! # Diagonal parity of the canonical Riccati resolvent

On equal fields the two Riccati series are related by spectral reflection.
Their product and the constructed denominator inverse are even, so the scalar
coupling is odd. Its even coefficients vanish identically, rather than merely
having zero spatial derivative.
-/
noncomputable section
namespace NLS.DifferentialPolynomial
variable {K A : Type*} [CommRing K] [CommRing A] [Algebra K A]

theorem rescale_riccatiResolventDenominator_diagonal (D : Derivation K A A) (a : A) :
    PowerSeries.rescale (-1) (riccatiResolventDenominator D a a) =
      riccatiResolventDenominator D a a := by
  have hr := (differentialRiccatiSeries_neg_derivation D a a).symm
  have hs : PowerSeries.rescale (-1) (differentialRiccatiSeries (-D) a a) =
      differentialRiccatiSeries D a a := by
    simpa using (differentialRiccatiSeries_neg_derivation (-D) a a).symm
  simp only [riccatiResolventDenominator, map_add, map_one, map_mul, map_pow,
    PowerSeries.rescale_neg_one_X, hr, hs]
  ring

theorem rescale_riccatiResolventInverse_diagonal (D : Derivation K A A) (a : A) :
    PowerSeries.rescale (-1) (riccatiResolventInverse D a a) =
      riccatiResolventInverse D a a := by
  have hu := riccatiResolvent_mul_inverse D a a
  have hr := congrArg (PowerSeries.rescale (-1)) hu
  rw [map_mul, map_one, rescale_riccatiResolventDenominator_diagonal] at hr
  calc
    PowerSeries.rescale (-1) (riccatiResolventInverse D a a) =
        PowerSeries.rescale (-1) (riccatiResolventInverse D a a) *
          (riccatiResolventDenominator D a a*riccatiResolventInverse D a a) := by rw [hu, mul_one]
    _ = (riccatiResolventDenominator D a a *
        PowerSeries.rescale (-1) (riccatiResolventInverse D a a))*riccatiResolventInverse D a a := by ring
    _ = riccatiResolventInverse D a a := by rw [hr, one_mul]

theorem riccatiResolventB_eq_rescale_A_diagonal (D : Derivation K A A) (a : A) :
    riccatiResolventB D a a = PowerSeries.rescale (-1) (riccatiResolventA D a a) := by
  simp only [riccatiResolventA, riccatiResolventB, map_mul,
    ← differentialRiccatiSeries_neg_derivation, rescale_riccatiResolventInverse_diagonal]

theorem coeff_riccatiResolventB_even_diagonal (D : Derivation K A A) (a : A) (m : ℕ) :
    PowerSeries.coeff (2*m) (riccatiResolventB D a a) =
      PowerSeries.coeff (2*m) (riccatiResolventA D a a) := by
  rw [riccatiResolventB_eq_rescale_A_diagonal, PowerSeries.coeff_rescale,
    pow_mul, neg_one_sq, one_pow, one_mul]

theorem rescale_riccatiResolventCoupling_diagonal (D : Derivation K A A) (a : A) :
    PowerSeries.rescale (-1) (riccatiResolventCoupling D a a) =
      -riccatiResolventCoupling D a a := by
  have hr := (differentialRiccatiSeries_neg_derivation D a a).symm
  have hs : PowerSeries.rescale (-1) (differentialRiccatiSeries (-D) a a) =
      differentialRiccatiSeries D a a := by
    simpa using (differentialRiccatiSeries_neg_derivation (-D) a a).symm
  simp only [riccatiResolventCoupling, map_mul, PowerSeries.rescale_neg_one_X, hr, hs,
    rescale_riccatiResolventInverse_diagonal]
  ring

/-- The correction term at every even coefficient is exactly zero. -/
theorem coeff_riccatiResolventCoupling_even_diagonal [NoZeroDivisors A] [CharZero A]
    (D : Derivation K A A) (a : A) (m : ℕ) :
    PowerSeries.coeff (2*m) (riccatiResolventCoupling D a a) = 0 := by
  have he := congrArg (PowerSeries.coeff (2*m))
    (rescale_riccatiResolventCoupling_diagonal D a)
  simp only [PowerSeries.coeff_rescale, pow_mul, neg_one_sq, one_pow, one_mul, map_neg] at he
  have ht : (2 : A)*PowerSeries.coeff (2*m) (riccatiResolventCoupling D a a) = 0 := by
    linear_combination he
  exact (mul_eq_zero.mp ht).resolve_left (by norm_num)

/-- The even/odd first-component recurrence has no coupling on the diagonal. -/
theorem coeff_riccatiResolventA_odd_diagonal [NoZeroDivisors A] [CharZero A]
    (D : Derivation K A A) (a : A) (m : ℕ) :
    PowerSeries.coeff (2*m+1) (riccatiResolventA D a a) =
      D (PowerSeries.coeff (2*m) (riccatiResolventA D a a)) := by
  rw [coeff_riccatiResolventA_succ, coeff_riccatiResolventCoupling_even_diagonal, mul_zero, add_zero]

theorem coeff_riccatiResolventB_odd_diagonal [NoZeroDivisors A] [CharZero A]
    (D : Derivation K A A) (a : A) (m : ℕ) :
    PowerSeries.coeff (2*m+1) (riccatiResolventB D a a) =
      -D (PowerSeries.coeff (2*m) (riccatiResolventB D a a)) := by
  rw [coeff_riccatiResolventB_succ, coeff_riccatiResolventCoupling_even_diagonal, mul_zero, add_zero]

end NLS.DifferentialPolynomial
