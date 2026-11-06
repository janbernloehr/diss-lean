import NLS.ZakharovShabat.SourceNormalizedWeightedActionCalibration

/-! # Positivity of the first normalized weighted action

The real mean-value comparison extends through collapsed gaps using the
calibrated midpoint value. A strictly positive gap location therefore
gives a strictly positive normalized first moment even at a closed gap.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceFullAbelianUniformCauchyFamily
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}

theorem normalizedWeightedAction_one_mean_value
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (φ : realTypeSourceSubmodule p)
    (hφ : φ.val ∈ ball C.discs.source.val C.discs.sourceRadius) (n : ℤ) :
    ∃ ζ ∈ Icc
      (canonicalPeriodicLeft hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n).re
      (canonicalPeriodicRight hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n).re,
      C.normalizedWeightedAction n 1 φ.val = (ζ : ℂ)*C.normalizedWeightedAction n 0 φ.val := by
  by_cases hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n = 0
  · let L := canonicalPeriodicLeft hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n
    let R := canonicalPeriodicRight hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n
    have hle : L.re ≤ R.re := re_le_of_complexLexLE
      ((canonicalPeriodicEndpoints_spec hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val)).2.1 n)
    obtain ⟨hLi,hRi⟩ := canonicalPeriodicEndpoints_im_eq_zero_of_realType hp hp1
      (periodOnePotential φ.val) (periodOnePotential_mem φ.val)
      (isRealType_periodOnePotential φ.val φ.property) n
    have hL : L = (L.re : ℂ) := Complex.ext rfl hLi
    have hR : R = (R.re : ℂ) := Complex.ext rfl hRi
    have hτ : sourceStandardRootMidpoint hp hp1 φ.val n = ((L.re+R.re)/2 : ℝ) := by
      change (L+R)/2 = _
      rw [hL,hR]
      push_cast
      rfl
    refine ⟨(L.re+R.re)/2,⟨by linarith,by linarith⟩,?_⟩
    rw [C.normalizedWeightedAction_collapsed n 1 φ.val hgap,pow_one,hτ]
  · obtain ⟨ζ,hζ,he⟩ := sourceRealHigherAction_eq_power_mul_action hp hp1 φ n 1
    refine ⟨ζ,hζ,?_⟩
    let A := sourceHigherActionAtlas hp hp1
    obtain ⟨r,hr,_,hf⟩ := C.exists_ball_normalizedWeightedActions A φ hφ
    have hF₁ := (hf n 1).2 φ.val (mem_ball_self hr)
    have hF₀ := (hf n 0).2 φ.val (mem_ball_self hr)
    have ha : A.action n 1 φ.val = (ζ : ℂ)*A.action n 0 φ.val := by
      rw [A.action_eq_real φ n 1,A.action_eq_real φ n 0,sourceRealHigherAction_zero,he,pow_one,ofReal_mul]
    apply mul_left_cancel₀ (pow_ne_zero 2 hgap)
    calc
      _ = A.action n 1 φ.val := hF₁.symm
      _ = (ζ : ℂ)*A.action n 0 φ.val := ha
      _ = _ := by rw [hF₀]; ring

theorem normalizedWeightedAction_one_real_positive
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (φ : realTypeSourceSubmodule p)
    (hφ : φ.val ∈ ball C.discs.source.val C.discs.sourceRadius) (n : ℤ)
    (hleft : 0 < (canonicalPeriodicLeft hp hp1 (periodOnePotential φ.val)
      (periodOnePotential_mem φ.val) n).re) :
    0 < (C.normalizedWeightedAction n 1 φ.val).re ∧
      (C.normalizedWeightedAction n 1 φ.val).im = 0 := by
  obtain ⟨ζ,hζ,he⟩ := C.normalizedWeightedAction_one_mean_value φ hφ n
  have hζpos : 0 < ζ := hleft.trans_le hζ.1
  rw [he,C.normalizedWeightedAction_zero_eq_canonical φ hφ n]
  constructor
  · simp only [mul_re,ofReal_re,ofReal_im,zero_mul,sub_zero]
    exact mul_pos hζpos
      (sourceNormalizedActionComplexExtension_re_pos_of_realType hp hp1 n φ.val φ.property)
  · simp only [mul_im,ofReal_re,ofReal_im,zero_mul,add_zero,
      sourceNormalizedActionComplexExtension_im_eq_zero_of_realType hp hp1 n φ.val φ.property,mul_zero]

end SourceFullAbelianUniformCauchyFamily
end NLS.ZakharovShabat
