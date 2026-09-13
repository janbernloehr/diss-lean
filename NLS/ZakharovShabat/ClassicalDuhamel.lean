import NLS.ZakharovShabat.ClassicalFundamentalSolution
import NLS.ComplexAnalysis.ScalarDuhamel

/-!
# Free-propagator formulas for the actual classical solution

A common exponential weight permits either half-plane normalization. The
coordinate formulas retain the off-diagonal potential and its original signs.
-/

noncomputable section
open Set Complex intervalIntegral
open NLS.LinearVolterra NLS.ComplexAnalysis
namespace NLS.ZakharovShabat

/-- Both coordinates multiplied by the same scalar exponential. -/
def classicalWeightedSolution (φ : Curve (ℂ × ℂ)) (z c : ℂ) (v : ℂ × ℂ)
    (t : ℝ) : ℂ × ℂ :=
  exp (c * t) • classicalSolution φ z v t

@[simp] theorem classicalWeightedSolution_zero (φ : Curve (ℂ × ℂ))
    (z c : ℂ) (v : ℂ × ℂ) : classicalWeightedSolution φ z c v 0 = v := by
  simp [classicalWeightedSolution]

@[simp] theorem classicalWeightedSolution_zero_weight (φ : Curve (ℂ × ℂ))
    (z : ℂ) (v : ℂ × ℂ) : classicalWeightedSolution φ z 0 v = classicalSolution φ z v := by
  funext t
  simp [classicalWeightedSolution]

theorem continuous_classicalWeightedSolution (φ : Curve (ℂ × ℂ))
    (z c : ℂ) (v : ℂ × ℂ) : Continuous (classicalWeightedSolution φ z c v) := by
  have hu := continuous_classicalSolution φ z v
  unfold classicalWeightedSolution
  fun_prop

theorem hasDerivAt_classicalWeightedSolution (φ : Curve (ℂ × ℂ))
    (z c : ℂ) (v : ℂ × ℂ) (t : Icc (0 : ℝ) 1) :
    HasDerivAt (classicalWeightedSolution φ z c v)
      ((c - I*z) * (classicalWeightedSolution φ z c v t).1 +
          I * (φ t).1 * (classicalWeightedSolution φ z c v t).2,
       (c + I*z) * (classicalWeightedSolution φ z c v t).2 +
          (-I) * (φ t).2 * (classicalWeightedSolution φ z c v t).1) t := by
  have hu := hasDerivAt_classicalSolution φ z v t
  have he := hasDerivAt_complex_exp_mul c t
  have hd := (he.mul (HasFDerivAt.hasDerivAt hu.fst)).prodMk
    (he.mul (HasFDerivAt.hasDerivAt hu.snd))
  convert! hd using 1
  apply Prod.ext <;>
    simp only [classicalWeightedSolution, classicalODECoefficient_apply,
      Prod.smul_fst, Prod.smul_snd, smul_eq_mul, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.toSpanSingleton_apply, one_smul] <;> dsimp <;> ring

/-- Variation of constants for the first weighted coordinate. -/
theorem classicalWeightedSolution_fst_duhamel (φ : Curve (ℂ × ℂ))
    (z c : ℂ) (v : ℂ × ℂ) (t : Icc (0 : ℝ) 1) :
    (classicalWeightedSolution φ z c v t).1 = exp ((c - I*z) * t.val) * v.1 +
      ∫ s in 0..t.val, exp ((c - I*z) * (t.val - s)) *
        (I * (NLS.LinearVolterra.extend φ s).1 * (classicalWeightedSolution φ z c v s).2) := by
  have hc := continuous_classicalWeightedSolution φ z c v
  have hφ := continuous_extend φ
  have h := scalar_duhamel (c - I*z) (fun s => (classicalWeightedSolution φ z c v s).1)
    (fun s => I * (NLS.LinearVolterra.extend φ s).1 * (classicalWeightedSolution φ z c v s).2)
    t.val t.property.1 hc.fst ((continuous_const.mul hφ.fst).mul hc.snd) (by
      intro s hs
      have ht : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1.le, hs.2.le.trans t.property.2⟩
      simpa only [extend, projIcc_of_mem _ ht, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.toSpanSingleton_apply, one_smul] using!
        (HasFDerivAt.hasDerivAt (hasDerivAt_classicalWeightedSolution φ z c v ⟨s, ht⟩).fst))
  simpa only [classicalWeightedSolution_zero] using h

/-- Variation of constants for the second weighted coordinate. -/
theorem classicalWeightedSolution_snd_duhamel (φ : Curve (ℂ × ℂ))
    (z c : ℂ) (v : ℂ × ℂ) (t : Icc (0 : ℝ) 1) :
    (classicalWeightedSolution φ z c v t).2 = exp ((c + I*z) * t.val) * v.2 +
      ∫ s in 0..t.val, exp ((c + I*z) * (t.val - s)) *
        ((-I) * (NLS.LinearVolterra.extend φ s).2 * (classicalWeightedSolution φ z c v s).1) := by
  have hc := continuous_classicalWeightedSolution φ z c v
  have hφ := continuous_extend φ
  have h := scalar_duhamel (c + I*z) (fun s => (classicalWeightedSolution φ z c v s).2)
    (fun s => (-I) * (NLS.LinearVolterra.extend φ s).2 * (classicalWeightedSolution φ z c v s).1)
    t.val t.property.1 hc.snd ((continuous_const.mul hφ.snd).mul hc.fst) (by
      intro s hs
      have ht : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1.le, hs.2.le.trans t.property.2⟩
      simpa only [extend, projIcc_of_mem _ ht, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.toSpanSingleton_apply, one_smul] using!
        (HasFDerivAt.hasDerivAt (hasDerivAt_classicalWeightedSolution φ z c v ⟨s, ht⟩).snd))
  simpa only [classicalWeightedSolution_zero] using h

/-- The upper-half-plane first coordinate has no diagonal coefficient. -/
theorem classicalWeightedSolution_upper_fst (φ : Curve (ℂ × ℂ))
    (z : ℂ) (v : ℂ × ℂ) (t : Icc (0 : ℝ) 1) :
    (classicalWeightedSolution φ z (I*z) v t).1 = v.1 +
      ∫ s in 0..t.val, I * (NLS.LinearVolterra.extend φ s).1 *
        (classicalWeightedSolution φ z (I*z) v s).2 := by
  simpa only [sub_self, zero_mul, exp_zero, one_mul] using
    classicalWeightedSolution_fst_duhamel φ z (I*z) v t

/-- The upper-half-plane second coordinate has a decaying free kernel. -/
theorem classicalWeightedSolution_upper_snd (φ : Curve (ℂ × ℂ))
    (z : ℂ) (v : ℂ × ℂ) (t : Icc (0 : ℝ) 1) :
    (classicalWeightedSolution φ z (I*z) v t).2 = exp ((2*I*z) * t.val) * v.2 +
      ∫ s in 0..t.val, exp ((2*I*z) * (t.val - s)) *
        ((-I) * (NLS.LinearVolterra.extend φ s).2 * (classicalWeightedSolution φ z (I*z) v s).1) := by
  simpa only [show I*z + I*z = 2*I*z by ring] using
    classicalWeightedSolution_snd_duhamel φ z (I*z) v t

/-- The lower-half-plane first coordinate has a decaying free kernel. -/
theorem classicalWeightedSolution_lower_fst (φ : Curve (ℂ × ℂ))
    (z : ℂ) (v : ℂ × ℂ) (t : Icc (0 : ℝ) 1) :
    (classicalWeightedSolution φ z (-I*z) v t).1 = exp ((-2*I*z) * t.val) * v.1 +
      ∫ s in 0..t.val, exp ((-2*I*z) * (t.val - s)) *
        (I * (NLS.LinearVolterra.extend φ s).1 * (classicalWeightedSolution φ z (-I*z) v s).2) := by
  simpa only [show -I*z - I*z = -2*I*z by ring] using
    classicalWeightedSolution_fst_duhamel φ z (-I*z) v t

/-- The lower-half-plane second coordinate has no diagonal coefficient. -/
theorem classicalWeightedSolution_lower_snd (φ : Curve (ℂ × ℂ))
    (z : ℂ) (v : ℂ × ℂ) (t : Icc (0 : ℝ) 1) :
    (classicalWeightedSolution φ z (-I*z) v t).2 = v.2 +
      ∫ s in 0..t.val, (-I) * (NLS.LinearVolterra.extend φ s).2 *
        (classicalWeightedSolution φ z (-I*z) v s).1 := by
  simpa only [show -I*z + I*z = 0 by ring, zero_mul, exp_zero, one_mul] using
    classicalWeightedSolution_snd_duhamel φ z (-I*z) v t

end NLS.ZakharovShabat
