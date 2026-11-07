import NLS.ZakharovShabat.ClassicalComponentSwap
import NLS.ZakharovShabat.ClassicalSpatialReflection

/-! # Actual normalized fundamental matrix identities at every unit time -/
noncomputable section
open Set Complex NLS.LinearVolterra
namespace NLS.ZakharovShabat

theorem classicalFundamentalMatrix_componentSwap (Φ : Curve (ℂ × ℂ)) (z : ℂ) (t : Icc (0:ℝ) 1) :
    classicalFundamentalMatrix (classicalComponentSwap Φ) (-z) t =
      !![(classicalFundamentalMatrix Φ z t) 1 1,-(classicalFundamentalMatrix Φ z t) 1 0;
        -(classicalFundamentalMatrix Φ z t) 0 1,(classicalFundamentalMatrix Φ z t) 0 0] := by
  have h₁ := classicalSolution_componentSwap Φ z (1,0) t
  have h₂ := classicalSolution_componentSwap Φ z (0,1) t
  have h₁' : classicalSolution Φ z (0,-1) t =
      componentSwapVector (classicalSolution (classicalComponentSwap Φ) (-z) (1,0) t) := h₁
  have h₂' : classicalSolution Φ z (1,0) t =
      componentSwapVector (classicalSolution (classicalComponentSwap Φ) (-z) (0,1) t) := by
    simpa [componentSwapVector] using h₂
  rw [classicalSolution_eq_columns Φ z (0,-1) t] at h₁'
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [classicalFundamentalMatrix,componentSwapVector] using
      (congrArg Prod.snd h₁').symm
  · simpa [classicalFundamentalMatrix,componentSwapVector] using
      (neg_eq_iff_eq_neg.mp (congrArg Prod.snd h₂').symm)
  · simpa [classicalFundamentalMatrix,componentSwapVector] using
      (congrArg Prod.fst h₁').symm
  · simpa [classicalFundamentalMatrix,componentSwapVector] using
      (congrArg Prod.fst h₂').symm


theorem classicalFundamentalMatrix_spatialReflection (Φ : Curve (ℂ × ℂ)) (z : ℂ)
    (t : Icc (0:ℝ) 1) :
    classicalFundamentalMatrix (classicalSpatialReflection Φ) z t =
      !![(classicalFundamentalMatrix Φ z (1-t.val)) 1 1*(classicalMonodromy Φ z) 0 0-
          (classicalFundamentalMatrix Φ z (1-t.val)) 1 0*(classicalMonodromy Φ z) 0 1,
        (classicalFundamentalMatrix Φ z (1-t.val)) 1 0*(classicalMonodromy Φ z) 1 1-
          (classicalFundamentalMatrix Φ z (1-t.val)) 1 1*(classicalMonodromy Φ z) 1 0;
        (classicalFundamentalMatrix Φ z (1-t.val)) 0 1*(classicalMonodromy Φ z) 0 0-
          (classicalFundamentalMatrix Φ z (1-t.val)) 0 0*(classicalMonodromy Φ z) 0 1,
        (classicalFundamentalMatrix Φ z (1-t.val)) 0 0*(classicalMonodromy Φ z) 1 1-
          (classicalFundamentalMatrix Φ z (1-t.val)) 0 1*(classicalMonodromy Φ z) 1 0] := by
  let T := classicalMonodromy Φ z
  let S := classicalFundamentalMatrix Φ z (1-t.val)
  let M := classicalFundamentalMatrix (classicalSpatialReflection Φ) z t
  have h₁ := classicalSolution_spatialReflection Φ z (1,0) t
  have h₂ := classicalSolution_spatialReflection Φ z (0,1) t
  rw [classicalSolution_eq_columns _ _ _ t] at h₁ h₂
  have ha : M 0 0*T 1 0+M 0 1*T 0 0 = S 1 0 := by
    simpa [M,S,T,classicalMonodromy,classicalFundamentalMatrix,smul_eq_mul,mul_comm] using congrArg Prod.fst h₁
  have hb : M 1 0*T 1 0+M 1 1*T 0 0 = S 0 0 := by
    simpa [M,S,T,classicalMonodromy,classicalFundamentalMatrix,smul_eq_mul,mul_comm] using congrArg Prod.snd h₁
  have hc : M 0 0*T 1 1+M 0 1*T 0 1 = S 1 1 := by
    simpa [M,S,T,classicalMonodromy,classicalFundamentalMatrix,smul_eq_mul,mul_comm] using congrArg Prod.fst h₂
  have hd : M 1 0*T 1 1+M 1 1*T 0 1 = S 0 1 := by
    simpa [M,S,T,classicalMonodromy,classicalFundamentalMatrix,smul_eq_mul,mul_comm] using congrArg Prod.snd h₂
  have he : T 0 0*T 1 1-T 0 1*T 1 0 = 1 := by
    simpa [T,Matrix.det_fin_two] using det_classicalMonodromy Φ z
  change M = !![S 1 1*T 0 0-S 1 0*T 0 1,S 1 0*T 1 1-S 1 1*T 1 0;
    S 0 1*T 0 0-S 0 0*T 0 1,S 0 0*T 1 1-S 0 1*T 1 0]
  ext i j
  fin_cases i <;> fin_cases j
  · change M 0 0 = S 1 1*T 0 0-S 1 0*T 0 1
    linear_combination T 0 0*hc-T 0 1*ha-M 0 0*he
  · change M 0 1 = S 1 0*T 1 1-S 1 1*T 1 0
    linear_combination T 1 1*ha-T 1 0*hc-M 0 1*he
  · change M 1 0 = S 0 1*T 0 0-S 0 0*T 0 1
    linear_combination T 0 0*hd-T 0 1*hb-M 1 0*he
  · change M 1 1 = S 0 0*T 1 1-S 0 1*T 1 0
    linear_combination T 1 1*hb-T 1 0*hd-M 1 1*he

end NLS.ZakharovShabat
