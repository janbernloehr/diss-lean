import NLS.ZakharovShabat.SourceHigherActionOneNormalized

/-! Reality of the ACTUAL filled higher-action quotient, including
closed gaps. No limiting open-gap sequence or density assumption is used. -/
noncomputable section
open Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem sourceHigherActionOneNormalized_im_eq_zero_of_realType
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) :
    (sourceHigherActionOneNormalized hp hp1 n φ).im = 0 := by
  have he := canonicalPeriodicEndpoints_im_eq_zero_of_realType hp hp1
    (periodOnePotential φ) (periodOnePotential_mem _) (isRealType_periodOnePotential _ hφ) n
  have hmid : (sourceStandardRootMidpoint hp hp1 φ n).im = 0 := by
    simp only [sourceStandardRootMidpoint,canonicalPeriodicMidpoint,Complex.div_im,Complex.add_im,he.1,he.2,zero_add,zero_mul]
    norm_num

  have hgap : (sourcePeriodicGapDisplacement hp hp1 φ n).im = 0 := by
    simp only [sourcePeriodicGapDisplacement_apply,canonicalPeriodicGap,Complex.sub_im,he.1,he.2,sub_self]
  by_cases hg : sourcePeriodicGapDisplacement hp hp1 φ n = 0
  · rw [sourceHigherActionOneNormalized_eq_midpoint_mul_of_gap_zero hp hp1 n φ hg,
      Complex.mul_im,hmid,sourceNormalizedActionComplexExtension_im_eq_zero_of_realType hp hp1 n φ hφ]
    ring
  · rw [sourceHigherActionOneNormalized_eq_quotient_of_gap_ne_zero hp hp1 n φ hg]
    have ha := sourceIndexedHigherAction_real hp hp1 ⟨φ,hφ⟩ n 1
    have hsq : ((sourcePeriodicGapDisplacement hp hp1 φ n)^2).im = 0 := by
      simp only [pow_two,Complex.mul_im,hgap,mul_zero,zero_mul,zero_add]
    simp only [Complex.div_im,ha,hsq,mul_zero,zero_mul,sub_zero,zero_div]

end NLS.ZakharovShabat
