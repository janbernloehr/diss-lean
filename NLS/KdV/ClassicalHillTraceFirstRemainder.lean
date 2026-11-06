import NLS.KdV.ClassicalHillWeightedStateError

noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory
open NLS.LinearVolterra
namespace NLS.KdV

def classicalHillCosineStateError (q : Curve ℂ) (z : ℂ) (s : ℝ) : ℂ :=
  (classicalHillFlow q (z^2) (1,0) s).1 - cos (z*s)

def classicalHillSineStateError (q : Curve ℂ) (z : ℂ) (s : ℝ) : ℂ :=
  (classicalHillFlow q (z^2) (0,1) s).1 - sin (z*s)/z

theorem continuous_classicalHillCosineStateError (q : Curve ℂ) (z : ℂ) :
    Continuous (classicalHillCosineStateError q z) :=
  (continuous_classicalHillFlow q (z^2) (1,0)).fst.sub (by fun_prop)

theorem continuous_classicalHillSineStateError (q : Curve ℂ) (z : ℂ) :
    Continuous (classicalHillSineStateError q z) :=
  (continuous_classicalHillFlow q (z^2) (0,1)).fst.sub (by fun_prop)

/-- The ACTUAL first trace term is PLUS sin(z)/z times the original
potential mean. The remainder contains one state error in each kernel,
with no extra exponential or lost endpoint term. -/
theorem classicalHillDiscriminant_first_order_remainder (q : Curve ℂ) (z : ℂ) (hz : z ≠ 0) :
    classicalHillDiscriminant q (z^2) - 2*cos z -
        sin z/z * (∫ s in (0:ℝ)..1, NLS.LinearVolterra.extend q s) =
      (∫ s in (0:ℝ)..1, sin (z*((1-s:ℝ):ℂ))/z * NLS.LinearVolterra.extend q s *
        classicalHillCosineStateError q z s) +
      (∫ s in (0:ℝ)..1, cos (z*((1-s:ℝ):ℂ)) * NLS.LinearVolterra.extend q s *
        classicalHillSineStateError q z s) := by
  let f := fun s : ℝ => sin (z*((1-s:ℝ):ℂ))/z * NLS.LinearVolterra.extend q s
  let g := fun s : ℝ => cos (z*((1-s:ℝ):ℂ)) * NLS.LinearVolterra.extend q s
  let C := fun s : ℝ => (classicalHillFlow q (z^2) (1,0) s).1
  let S := fun s : ℝ => (classicalHillFlow q (z^2) (0,1) s).1
  have hq := continuous_extend q
  have hf : Continuous f := by fun_prop
  have hg : Continuous g := by fun_prop
  have hC : Continuous C := (continuous_classicalHillFlow q (z^2) (1,0)).fst
  have hS : Continuous S := (continuous_classicalHillFlow q (z^2) (0,1)).fst
  have heC := continuous_classicalHillCosineStateError q z
  have heS := continuous_classicalHillSineStateError q z
  have hce : C 1 - cos z = ∫ s in (0:ℝ)..1, f s * C s := by
    have h := classicalHillFlow_sine_duhamel q z hz (1,0) (⟨1,by norm_num⟩ : Icc (0:ℝ) 1)
    simpa only [C,f,ofReal_one,mul_one,mul_zero,add_zero,add_sub_cancel_left] using
      congrArg (fun x : ℂ => x-cos z) h
  have hse : (classicalHillFlow q (z^2) (0,1) 1).2 - cos z = ∫ s in (0:ℝ)..1, g s * S s := by
    have h := classicalHillFlow_cosine_duhamel q z (0,1) (⟨1,by norm_num⟩ : Icc (0:ℝ) 1)
    simpa only [S,g,ofReal_one,mul_one,mul_zero,zero_add,add_sub_cancel_left] using
      congrArg (fun x : ℂ => x-cos z) h
  have hpoint (s : ℝ) : f s * classicalHillCosineStateError q z s +
      g s * classicalHillSineStateError q z s =
        (f s * C s + g s * S s) - sin z/z * NLS.LinearVolterra.extend q s := by
    have htrig : sin (z*((1-s:ℝ):ℂ)) * cos (z*s) +
        cos (z*((1-s:ℝ):ℂ)) * sin (z*s) = sin z := by
      rw [←Complex.sin_add,show z*((1-s:ℝ):ℂ) + z*(s:ℂ) = z by push_cast; ring]
    dsimp only [f,g,C,S,classicalHillCosineStateError,classicalHillSineStateError]
    linear_combination -(NLS.LinearVolterra.extend q s/z) * htrig
  have hsplit : (∫ s in (0:ℝ)..1, f s * classicalHillCosineStateError q z s) +
      (∫ s in (0:ℝ)..1, g s * classicalHillSineStateError q z s) =
      (∫ s in (0:ℝ)..1, f s * C s) + (∫ s in (0:ℝ)..1, g s * S s) -
        sin z/z * (∫ s in (0:ℝ)..1, NLS.LinearVolterra.extend q s) := by
    rw [←intervalIntegral.integral_add
      (f := fun s : ℝ => f s * classicalHillCosineStateError q z s)
      (g := fun s : ℝ => g s * classicalHillSineStateError q z s)
      ((hf.mul heC).intervalIntegrable 0 1)
      ((hg.mul heS).intervalIntegrable 0 1)]
    calc
      _ = ∫ s in (0:ℝ)..1, (f s * C s + g s * S s) - sin z/z * NLS.LinearVolterra.extend q s :=
        intervalIntegral.integral_congr (fun s _ => hpoint s)
      _ = _ := by
        rw [intervalIntegral.integral_sub
          (f := fun s : ℝ => f s * C s + g s * S s)
          (g := fun s : ℝ => sin z/z * NLS.LinearVolterra.extend q s)
          (((hf.mul hC).add (hg.mul hS)).intervalIntegrable 0 1)
          ((hq.const_mul _).intervalIntegrable 0 1),
          intervalIntegral.integral_add (f := fun s : ℝ => f s * C s)
            (g := fun s : ℝ => g s * S s) ((hf.mul hC).intervalIntegrable 0 1)
            ((hg.mul hS).intervalIntegrable 0 1),intervalIntegral.integral_const_mul]
  rw [←hce,←hse] at hsplit
  rw [←classicalHillFlow_trace]
  change (C 1 + (classicalHillFlow q (z^2) (0,1) 1).2) - 2*cos z -
    sin z/z * (∫ s in (0:ℝ)..1, NLS.LinearVolterra.extend q s) = _
  linear_combination -hsplit

end NLS.KdV
