import NLS.ZakharovShabat.CanonicalParityProductsAnalytic

/-!
# The intrinsic discriminant from the even spectral product

The corrected even product plus two defines an intrinsic entire function.
It is jointly analytic on the even-supported potential space at every finite
exponent greater than one. Compatibility with the odd and full products is
proved separately, without incorporating that identity into the definition.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The intrinsic discriminant, normalized by the corrected even spectral product. -/
def canonicalDiscriminant (hp : p ≠ ⊤) (φ : PairSpace p) (z : ℂ) : ℂ :=
  canonicalParityProduct hp φ 0 z+2

/-- The even product is the intrinsic discriminant minus two. -/
theorem canonicalEven_eq_discriminant_sub_two (hp : p ≠ ⊤) (φ : PairSpace p) (z : ℂ) :
    canonicalParityProduct hp φ 0 z = canonicalDiscriminant hp φ z-2 := by
  simp only [canonicalDiscriminant, add_sub_cancel_right]

/-- The intrinsic discriminant is entire in the spectral parameter. -/
theorem analyticOnNhd_canonicalDiscriminant (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (hφ : φ ∈ pairParitySubspace 0) :
    AnalyticOnNhd ℂ (canonicalDiscriminant hp φ) univ := by
  intro z hz
  exact ((canonicalParityProduct_spec hp hp1 φ hφ 0 (Or.inl rfl)).1 z hz).add analyticAt_const

/-- The intrinsic discriminant is jointly analytic in parameter and even potential. -/
theorem analyticOnNhd_canonicalDiscriminant_joint (hp : p ≠ ⊤) (hp1 : 1 < p) :
    AnalyticOnNhd ℂ (fun t : ℂ × pairParitySubspace (p := p) 0 =>
      canonicalDiscriminant hp t.2.val t.1) univ := by
  intro t ht
  exact (analyticOnNhd_canonicalParityProduct_joint hp hp1 0 (Or.inl rfl) t ht).add analyticAt_const

/-- Joint analyticity also holds in the source period-one coefficient convention. -/
theorem analyticOnNhd_canonicalDiscriminant_periodOne (hp : p ≠ ⊤) (hp1 : 1 < p) :
    AnalyticOnNhd ℂ (fun t : ℂ × CoeffPair p =>
      canonicalDiscriminant hp (periodOnePotential t.2) t.1) univ := by
  intro t ht
  exact (analyticOnNhd_canonicalParityProduct_periodOne hp hp1 0 (Or.inl rfl) t ht).add analyticAt_const

end NLS.ZakharovShabat
