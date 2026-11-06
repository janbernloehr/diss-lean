import NLS.ZakharovShabat.SourceFullAbelianInverseMoment
import NLS.ZakharovShabat.SourceRealHigherAction
import NLS.ZakharovShabat.CanonicalCriticalInterlacing

/-! # A real gap estimate with the exact inverse-frequency moment

The elementary inequality t+1/t >= 2 is applied with t=pi*n/x.
The gap index and spectral variable have the same strict sign when the
central gap is collapsed at zero. Both signs of the index are retained.
-/
noncomputable section
open Set Complex Metric MeasureTheory NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def sourceRealGapMassDensity (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (n : ℤ) (θ : ℝ) : ℝ :=
  (canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n).re/2*
    (Real.sin θ*sourceRealGapCosineProfile hp hp1 φ.val n θ)

def sourceRealGapInverseMoment (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (n : ℤ) : ℝ :=
  ∫ θ in (0 : ℝ)..Real.pi, sourceRealGapMassDensity hp hp1 φ n θ/
    realGapAffinePoint hp hp1 φ.val n (Real.cos θ)

theorem sourceRealGapMassDensity_continuous (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (n : ℤ) : Continuous (sourceRealGapMassDensity hp hp1 φ n) :=
  continuous_const.mul (Real.continuous_sin.mul (sourceRealGapCosineProfile_continuous hp hp1 φ n))

theorem sourceRealGapMassDensity_nonneg (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (n : ℤ) (θ : ℝ) (hθ : θ ∈ Icc 0 Real.pi) :
    0 ≤ sourceRealGapMassDensity hp hp1 φ n θ := by
  have hg := re_le_of_complexLexLE ((canonicalPeriodicEndpoints_spec hp hp1
    (periodOnePotential φ.val) (periodOnePotential_mem φ.val)).2.1 n)
  exact mul_nonneg (div_nonneg (sub_nonneg.mpr hg) (by norm_num))
    (mul_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 hθ.2)
      (sourceRealGapCosineProfile_nonneg hp hp1 φ n θ))

theorem sourceRealAction_eq_massDensity_integral (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (n : ℤ) :
    (sourceRealAction hp hp1 φ.val φ.property n).re = (2/Real.pi)*
      ∫ θ in (0 : ℝ)..Real.pi, sourceRealGapMassDensity hp hp1 φ n θ := by
  rw [←sourceRealHigherAction_zero hp hp1 φ n]
  simp only [sourceRealHigherAction,pow_zero,one_mul,sourceRealGapMassDensity,
    intervalIntegral.integral_const_mul]
  ring

theorem sourceRealHigherAction_one_eq_massDensity_integral (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (n : ℤ) :
    sourceRealHigherAction hp hp1 φ n 1 = (2/Real.pi)*
      ∫ θ in (0 : ℝ)..Real.pi,
        realGapAffinePoint hp hp1 φ.val n (Real.cos θ)*sourceRealGapMassDensity hp hp1 φ n θ := by
  simp only [sourceRealHigherAction,pow_one,sourceRealGapMassDensity]
  have he : (fun θ => realGapAffinePoint hp hp1 φ.val n (Real.cos θ)*
      ((canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n).re/2*
        (Real.sin θ*sourceRealGapCosineProfile hp hp1 φ.val n θ))) =
      (fun θ => (canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n).re/2*
        (realGapAffinePoint hp hp1 φ.val n (Real.cos θ)*(Real.sin θ*sourceRealGapCosineProfile hp hp1 φ.val n θ))) := by
    funext θ
    ring
  rw [he,intervalIntegral.integral_const_mul]
  ring

theorem index_mul_realGapAffinePoint_pos_of_central_zero (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p)
    (hl : canonicalPeriodicLeft hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) 0 = 0)
    (hr : canonicalPeriodicRight hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) 0 = 0)
    (n : ℤ) (hn : n ≠ 0) (θ : ℝ) :
    0 < (n : ℝ)*realGapAffinePoint hp hp1 φ.val n (Real.cos θ) := by
  have hθ := realGapAffinePoint_cos_mem_Icc hp hp1 φ n θ
  rcases lt_or_gt_of_ne hn with hn | hn
  · have h := canonicalPeriodicRight_re_lt_left_of_lt hp hp1 (periodOnePotential φ.val)
      (periodOnePotential_mem φ.val) (isRealType_periodOnePotential φ.val φ.property) hn
    rw [hl,zero_re] at h
    exact mul_pos_of_neg_of_neg (by exact_mod_cast hn) (hθ.2.trans_lt h)
  · have h := canonicalPeriodicRight_re_lt_left_of_lt hp hp1 (periodOnePotential φ.val)
      (periodOnePotential_mem φ.val) (isRealType_periodOnePotential φ.val φ.property) hn
    rw [hr,zero_re] at h
    exact mul_pos (by exact_mod_cast hn) (h.trans_le hθ.1)

/-- A single actual noncentral action is bounded by its inverse-frequency
moment and its first weighted action, with the original pi normalization. -/
theorem sourceRealAction_le_inverseMoment_add_higherAction (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p)
    (hl : canonicalPeriodicLeft hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) 0 = 0)
    (hr : canonicalPeriodicRight hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) 0 = 0)
    (n : ℤ) (hn : n ≠ 0) :
    (sourceRealAction hp hp1 φ.val φ.property n).re ≤
      (n : ℝ)*sourceRealGapInverseMoment hp hp1 φ n+
        sourceRealHigherAction hp hp1 φ n 1/(2*Real.pi*(n : ℝ)) := by
  let x : ℝ → ℝ := fun θ => realGapAffinePoint hp hp1 φ.val n (Real.cos θ)
  let v := sourceRealGapMassDensity hp hp1 φ n
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hx (θ : ℝ) : 0 < (n : ℝ)*x θ := index_mul_realGapAffinePoint_pos_of_central_zero hp hp1 φ hl hr n hn θ
  have hx0 (θ : ℝ) : x θ ≠ 0 := (mul_pos_iff.mp (hx θ)).elim (fun h => h.2.ne') (fun h => h.2.ne)
  have hc : Continuous x := by dsimp [x,realGapAffinePoint]; fun_prop
  have hv := sourceRealGapMassDensity_continuous hp hp1 φ n
  have hvi := (hv.div hc hx0).intervalIntegrable (μ := volume) 0 Real.pi
  have hxvi := (hc.mul hv).intervalIntegrable (μ := volume) 0 Real.pi
  have hpoint (θ : ℝ) (hθ : θ ∈ Icc 0 Real.pi) :
      2*v θ ≤ (Real.pi*(n : ℝ))*(v θ/x θ)+(x θ*v θ)/(Real.pi*(n : ℝ)) := by
    have hden : 0 < Real.pi*(n : ℝ)*x θ := by nlinarith [Real.pi_pos,hx θ]
    have hnon := div_nonneg (mul_nonneg (sourceRealGapMassDensity_nonneg hp hp1 φ n θ hθ)
      (sq_nonneg (x θ-Real.pi*(n : ℝ)))) hden.le
    have he : (Real.pi*(n : ℝ))*(v θ/x θ)+(x θ*v θ)/(Real.pi*(n : ℝ))-2*v θ =
        v θ*(x θ-Real.pi*(n : ℝ))^2/(Real.pi*(n : ℝ)*x θ) := by
      field_simp [Real.pi_ne_zero,hn0,hx0 θ]
      ring
    exact sub_nonneg.mp (he.symm ▸ hnon)
  have hi := intervalIntegral.integral_mono_on Real.pi_pos.le
    ((hv.const_mul 2).intervalIntegrable (μ := volume) 0 Real.pi)
    ((hvi.const_mul (Real.pi*(n : ℝ))).add (hxvi.div_const (Real.pi*(n : ℝ)))) hpoint
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add (hvi.const_mul (Real.pi*(n : ℝ)))
      (hxvi.div_const (Real.pi*(n : ℝ))),intervalIntegral.integral_const_mul,
    intervalIntegral.integral_div] at hi
  rw [sourceRealAction_eq_massDensity_integral,sourceRealHigherAction_one_eq_massDensity_integral,
    sourceRealGapInverseMoment]
  have hh := mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr Real.pi_pos.le)
  dsimp only [x,v,Pi.div_apply,Pi.mul_apply] at hh
  convert! hh using 1 <;> field_simp [Real.pi_ne_zero,hn0]

end NLS.ZakharovShabat
