import NLS.DifferentialPolynomial.ConstructedRiccatiResolvent

/-! # Coefficient maps commuting with spatial differentiation preserve the resolvent -/
noncomputable section
namespace NLS.DifferentialPolynomial
variable {K A B : Type*} [CommRing K] [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]

theorem map_differentialRiccatiSequence (D : Derivation K A A) (D' : Derivation K B B)
    (F : A →+* B) (hF : ∀ p, F (D p) = D' (F p)) (a b : A) (n : ℕ) :
    F (differentialRiccatiSequence D a b n) = differentialRiccatiSequence D' (F a) (F b) n := by
  have he := differentialRiccatiSequence_unique D' (F a) (F b)
    (fun k => F (differentialRiccatiSequence D a b k))
    (by simp) (by simp [hF]) (by
      intro k
      rw [differentialRiccatiSequence_recurrence]
      simp only [map_add, hF, map_mul, map_sum])
  exact congrFun he n

theorem map_differentialRiccatiSeries (D : Derivation K A A) (D' : Derivation K B B)
    (F : A →+* B) (hF : ∀ p, F (D p) = D' (F p)) (a b : A) :
    PowerSeries.map F (differentialRiccatiSeries D a b) =
      differentialRiccatiSeries D' (F a) (F b) := by
  ext n
  simpa only [PowerSeries.coeff_map, coeff_differentialRiccatiSeries] using
    map_differentialRiccatiSequence D D' F hF a b n

theorem map_riccatiResolventDenominator (D : Derivation K A A) (D' : Derivation K B B)
    (F : A →+* B) (hF : ∀ p, F (D p) = D' (F p)) (a b : A) :
    PowerSeries.map F (riccatiResolventDenominator D a b) =
      riccatiResolventDenominator D' (F a) (F b) := by
  have hn (p : A) : F ((-D) p) = (-D') (F p) := by simp [hF]
  simp only [riccatiResolventDenominator, map_add, map_one, map_mul, map_pow, PowerSeries.map_X,
    map_differentialRiccatiSeries D D' F hF, map_differentialRiccatiSeries (-D) (-D') F hn]

theorem map_riccatiResolventInverse (D : Derivation K A A) (D' : Derivation K B B)
    (F : A →+* B) (hF : ∀ p, F (D p) = D' (F p)) (a b : A) :
    PowerSeries.map F (riccatiResolventInverse D a b) = riccatiResolventInverse D' (F a) (F b) := by
  have hu := congrArg (PowerSeries.map F) (riccatiResolvent_mul_inverse D a b)
  rw [map_mul, map_one, map_riccatiResolventDenominator D D' F hF] at hu
  have hv := riccatiResolvent_mul_inverse D' (F a) (F b)
  calc
    PowerSeries.map F (riccatiResolventInverse D a b) =
        PowerSeries.map F (riccatiResolventInverse D a b) *
          (riccatiResolventDenominator D' (F a) (F b)*riccatiResolventInverse D' (F a) (F b)) := by
      rw [hv, mul_one]
    _ = (riccatiResolventDenominator D' (F a) (F b)*
        PowerSeries.map F (riccatiResolventInverse D a b))*riccatiResolventInverse D' (F a) (F b) := by ring
    _ = riccatiResolventInverse D' (F a) (F b) := by rw [hu, one_mul]

theorem map_riccatiResolventA (D : Derivation K A A) (D' : Derivation K B B)
    (F : A →+* B) (hF : ∀ p, F (D p) = D' (F p)) (a b : A) :
    PowerSeries.map F (riccatiResolventA D a b) = riccatiResolventA D' (F a) (F b) := by
  simp only [riccatiResolventA, map_mul, map_differentialRiccatiSeries D D' F hF,
    map_riccatiResolventInverse D D' F hF]

theorem map_riccatiResolventB (D : Derivation K A A) (D' : Derivation K B B)
    (F : A →+* B) (hF : ∀ p, F (D p) = D' (F p)) (a b : A) :
    PowerSeries.map F (riccatiResolventB D a b) = riccatiResolventB D' (F a) (F b) := by
  have hn (p : A) : F ((-D) p) = (-D') (F p) := by simp [hF]
  simp only [riccatiResolventB, map_mul, map_differentialRiccatiSeries (-D) (-D') F hn,
    map_riccatiResolventInverse D D' F hF]

theorem map_riccatiResolventCoupling (D : Derivation K A A) (D' : Derivation K B B)
    (F : A →+* B) (hF : ∀ p, F (D p) = D' (F p)) (a b : A) :
    PowerSeries.map F (riccatiResolventCoupling D a b) =
      riccatiResolventCoupling D' (F a) (F b) := by
  have hn (p : A) : F ((-D) p) = (-D') (F p) := by simp [hF]
  simp only [riccatiResolventCoupling, map_mul, PowerSeries.map_X,
    map_differentialRiccatiSeries D D' F hF, map_differentialRiccatiSeries (-D) (-D') F hn,
    map_riccatiResolventInverse D D' F hF]

end NLS.DifferentialPolynomial
