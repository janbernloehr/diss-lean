import NLS.DifferentialPolynomial.RiccatiResolventNaturality

/-! # Spatial reflection and simultaneous field negation of the scalar coupling -/
noncomputable section
namespace NLS.DifferentialPolynomial
variable {K A : Type*} [CommRing K] [CommRing A] [Algebra K A]

theorem differentialRiccatiSequence_neg_fields (D : Derivation K A A) (a b : A) (n : ℕ) :
    differentialRiccatiSequence D (-a) (-b) n = -differentialRiccatiSequence D a b n := by
  have he := differentialRiccatiSequence_unique D (-a) (-b)
    (fun k => -differentialRiccatiSequence D a b k)
    (by simp) (by simp) (by
      intro k
      rw [differentialRiccatiSequence_recurrence]
      simp only [map_neg,neg_mul,mul_neg,neg_neg]
      ring)
  exact (congrFun he n).symm

theorem differentialRiccatiSeries_neg_fields (D : Derivation K A A) (a b : A) :
    differentialRiccatiSeries D (-a) (-b) = -differentialRiccatiSeries D a b := by
  ext n
  simp only [coeff_differentialRiccatiSeries,map_neg,differentialRiccatiSequence_neg_fields]

theorem riccatiResolventDenominator_neg_fields (D : Derivation K A A) (a b : A) :
    riccatiResolventDenominator D (-a) (-b) = riccatiResolventDenominator D a b := by
  simp only [riccatiResolventDenominator,differentialRiccatiSeries_neg_fields]
  ring

theorem riccatiResolventCoupling_neg_fields (D : Derivation K A A) (a b : A) :
    riccatiResolventCoupling D (-a) (-b) = riccatiResolventCoupling D a b := by
  simp only [riccatiResolventCoupling,differentialRiccatiSeries_neg_fields,
    riccatiResolventInverse,riccatiResolventDenominator_neg_fields]
  ring

theorem rescale_riccatiResolventDenominator (D : Derivation K A A) (a b : A) :
    PowerSeries.rescale (-1) (riccatiResolventDenominator D a b) =
      riccatiResolventDenominator (-D) a b := by
  have hr := (differentialRiccatiSeries_neg_derivation D a b).symm
  have hs := (differentialRiccatiSeries_neg_derivation (-D) b a).symm
  simp only [neg_neg] at hs
  simp only [riccatiResolventDenominator,map_add,map_one,map_mul,map_pow,
    PowerSeries.rescale_neg_one_X,hr,hs,neg_neg]
  ring

theorem rescale_riccatiResolventInverse (D : Derivation K A A) (a b : A) :
    PowerSeries.rescale (-1) (riccatiResolventInverse D a b) =
      riccatiResolventInverse (-D) a b := by
  have hu := congrArg (PowerSeries.rescale (-1)) (riccatiResolvent_mul_inverse D a b)
  rw [map_mul,map_one,rescale_riccatiResolventDenominator] at hu
  have hv := riccatiResolvent_mul_inverse (-D) a b
  calc
    PowerSeries.rescale (-1) (riccatiResolventInverse D a b) =
        PowerSeries.rescale (-1) (riccatiResolventInverse D a b)*
          (riccatiResolventDenominator (-D) a b*riccatiResolventInverse (-D) a b) := by rw [hv,mul_one]
    _ = (riccatiResolventDenominator (-D) a b*
        PowerSeries.rescale (-1) (riccatiResolventInverse D a b))*riccatiResolventInverse (-D) a b := by ring
    _ = riccatiResolventInverse (-D) a b := by rw [hu,one_mul]

theorem rescale_riccatiResolventCoupling (D : Derivation K A A) (a b : A) :
    PowerSeries.rescale (-1) (riccatiResolventCoupling D a b) =
      -riccatiResolventCoupling (-D) a b := by
  have hr := (differentialRiccatiSeries_neg_derivation D a b).symm
  have hs := (differentialRiccatiSeries_neg_derivation (-D) b a).symm
  simp only [neg_neg] at hs
  simp only [riccatiResolventCoupling,map_mul,PowerSeries.rescale_neg_one_X,hr,hs,
    rescale_riccatiResolventInverse,neg_neg]
  ring

theorem coeff_riccatiResolventCoupling_even_neg_derivation (D : Derivation K A A) (a b : A) (m : ℕ) :
    PowerSeries.coeff (2*m) (riccatiResolventCoupling (-D) a b) =
      -PowerSeries.coeff (2*m) (riccatiResolventCoupling D a b) := by
  have he := congrArg (PowerSeries.coeff (2*m)) (rescale_riccatiResolventCoupling D a b)
  simp only [PowerSeries.coeff_rescale,pow_mul,neg_one_sq,one_pow,one_mul,map_neg] at he
  exact neg_eq_iff_eq_neg.mp he.symm

end NLS.DifferentialPolynomial
