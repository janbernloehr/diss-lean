import NLS.ZakharovShabat.SourceRealGapArcoshPrimitive

/-! # The actual arcosh profile on the entire closed real gap

Endpoint values and strict interior trace separation give nonnegativity
and the exact signed complex-cosh identity, including collapsed gaps.
-/
noncomputable section
set_option autoImplicit false
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem sourceRealGapArcoshProfile_closed_properties (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ)) (n : ℤ)
    (x : ℝ) (hx : x ∈ Icc
      (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem _) n).re
      (canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem _) n).re) :
    0 ≤ sourceRealGapArcoshProfile hp φ n x ∧
      cosh (sourceRealGapArcoshProfile hp φ n x : ℂ) =
        (if n%2 = 0 then canonicalDiscriminant hp (periodOnePotential φ) x
          else -canonicalDiscriminant hp (periodOnePotential φ) x)/2 := by
  obtain ⟨_,_,_,ha,hb,hgt⟩ := realGapHalfDiscriminant_arcosh_gap_data hp hp1
    (periodOnePotential φ) (periodOnePotential_mem _) (isRealType_periodOnePotential φ hreal) n
  have hge : 1 ≤ realGapHalfDiscriminant hp (periodOnePotential φ) n x := by
    rcases eq_or_lt_of_le hx.1 with he | he
    · rw [← he,ha]
    rcases eq_or_lt_of_le hx.2 with he' | he'
    · rw [he',hb]
    · exact (hgt x ⟨he,he'⟩).le
  refine ⟨Real.arcosh_nonneg hge,?_⟩
  change cosh (Real.arcosh _ : ℂ) = _
  rw [← ofReal_cosh,Real.cosh_arcosh hge]
  have him := canonicalDiscriminant_im_eq_zero_of_realType hp hp1
    (periodOnePotential φ) (periodOnePotential_mem _) (isRealType_periodOnePotential φ hreal) x
  have he : (((canonicalDiscriminant hp (periodOnePotential φ) x).re : ℝ) : ℂ) =
      canonicalDiscriminant hp (periodOnePotential φ) x := Complex.ext rfl him.symm
  by_cases hn : n%2 = 0
  · simp only [realGapHalfDiscriminant,if_pos hn,ofReal_div,ofReal_ofNat,he]
  · simp only [realGapHalfDiscriminant,if_neg hn,ofReal_div,ofReal_ofNat,ofReal_neg,he]

end NLS.ZakharovShabat
