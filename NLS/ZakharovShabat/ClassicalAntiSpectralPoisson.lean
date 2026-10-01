import NLS.ZakharovShabat.ClassicalEndpointPoisson
import NLS.ZakharovShabat.ClassicalAntiDiscriminantGradient

/-! # Remaining actual physical anti-discriminant spectral brackets

The endpoint bracket law applies to the two actual off-diagonal endpoint
gradients. Its sum gives the characteristic/anti-discriminant bracket
and the mutual anti-discriminant cancellation, with the original signs.
-/

noncomputable section
set_option maxHeartbeats 800000
open Set Complex MeasureTheory intervalIntegral NLS.LinearVolterra
namespace NLS.ZakharovShabat
open BoundaryCondition

def classicalGradientPoissonBracket (g h : ℝ → ℂ × ℂ) : ℂ :=
  -I*(∫ s in (0 : ℝ)..1, (g s).1*(h s).2-(g s).2*(h s).1)

theorem classicalGradientPoissonBracket_add_left (g k h : ℝ → ℂ × ℂ)
    (hg : Continuous g) (hk : Continuous k) (hh : Continuous h) :
    classicalGradientPoissonBracket (g+k) h =
      classicalGradientPoissonBracket g h+classicalGradientPoissonBracket k h := by
  have hi (f : ℝ → ℂ × ℂ) (hf : Continuous f) :
      IntervalIntegrable (fun s : ℝ => (f s).1*(h s).2-(f s).2*(h s).1) volume 0 1 :=
    ((hf.fst.mul hh.snd).sub (hf.snd.mul hh.fst)).intervalIntegrable 0 1
  unfold classicalGradientPoissonBracket
  rw [← mul_add,← intervalIntegral.integral_add (hi g hg) (hi k hk)]
  congr 1
  apply intervalIntegral.integral_congr
  intro s _
  simp only [Pi.add_apply,Prod.fst_add,Prod.snd_add]
  ring

theorem classicalGradientPoissonBracket_add_right (g h k : ℝ → ℂ × ℂ)
    (hg : Continuous g) (hh : Continuous h) (hk : Continuous k) :
    classicalGradientPoissonBracket g (h+k) =
      classicalGradientPoissonBracket g h+classicalGradientPoissonBracket g k := by
  have hi (f : ℝ → ℂ × ℂ) (hf : Continuous f) :
      IntervalIntegrable (fun s : ℝ => (g s).1*(f s).2-(g s).2*(f s).1) volume 0 1 :=
    ((hg.fst.mul hf.snd).sub (hg.snd.mul hf.fst)).intervalIntegrable 0 1
  unfold classicalGradientPoissonBracket
  rw [← mul_add,← intervalIntegral.integral_add (hi h hh) (hi k hk)]
  congr 1
  apply intervalIntegral.integral_congr
  intro s _
  simp only [Pi.add_apply,Prod.fst_add,Prod.snd_add]
  ring

@[simp] theorem classicalGradientPoissonBracket_self (g : ℝ → ℂ × ℂ) :
    classicalGradientPoissonBracket g g = 0 := by
  simp [classicalGradientPoissonBracket,mul_comm]

theorem classicalSolution_one_eq_monodromy (Φ : Curve (ℂ × ℂ)) (z : ℂ) (v : ℂ × ℂ) :
    classicalSolution Φ z v 1 =
      (classicalMonodromy Φ z 0 0*v.1+classicalMonodromy Φ z 0 1*v.2,
        classicalMonodromy Φ z 1 0*v.1+classicalMonodromy Φ z 1 1*v.2) := by
  rw [classicalSolution_eq_columns Φ z v ⟨1,by constructor <;> norm_num⟩]
  apply Prod.ext <;> simp only [classicalMonodromy,classicalFundamentalMatrix,
    Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,smul_eq_mul,
    Matrix.of_apply,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one] <;> ring

/-- The actual physical characteristic/anti-discriminant bracket is the
signed characteristic/discriminant determinant divided by twice the
spectral difference, here retained as a factor. -/
theorem classicalGradientPoissonBracket_separated_anti_mul
    (b : BoundaryCondition) (Φ : Curve (ℂ × ℂ)) (z w : ℂ) :
    2*(z-w)*classicalGradientPoissonBracket
      (classicalSeparatedGradient b Φ z) (classicalAntiDiscriminantGradient Φ w) =
        extensionSign b*(classicalSeparatedCharacteristic b Φ z*classicalDiscriminant Φ w-
          classicalDiscriminant Φ z*classicalSeparatedCharacteristic b Φ w) := by
  change 2*(z-w)*classicalGradientPoissonBracket
    (classicalEndpointGradient Φ z (1,extensionSign b) (classicalSeparatedEndpointCLM b))
    (classicalEndpointGradient Φ w (0,1) (ContinuousLinearMap.fst ℂ ℂ ℂ)+
      classicalEndpointGradient Φ w (1,0) (ContinuousLinearMap.snd ℂ ℂ ℂ)) = _
  rw [classicalGradientPoissonBracket_add_right _ _ _
    (continuous_classicalEndpointGradient _ _ _ _)
    (continuous_classicalEndpointGradient _ _ _ _) (continuous_classicalEndpointGradient _ _ _ _)]
  change 2*(z-w)*(classicalEndpointPoissonBracket Φ z w
    (1,extensionSign b) (classicalSeparatedEndpointCLM b) (0,1) (ContinuousLinearMap.fst ℂ ℂ ℂ)+
      classicalEndpointPoissonBracket Φ z w
        (1,extensionSign b) (classicalSeparatedEndpointCLM b) (1,0) (ContinuousLinearMap.snd ℂ ℂ ℂ)) = _
  rw [mul_add,classicalEndpointPoissonBracket_mul,classicalEndpointPoissonBracket_mul]
  simp only [classicalCrossWronskian,classicalSolution_one_eq_monodromy,
    classicalSeparatedEndpointCLM_apply,ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd',
    classicalSeparatedCharacteristic,classicalDiscriminant,Matrix.trace,Matrix.diag,Fin.sum_univ_two]
  cases b <;> simp only [extensionSign] <;> ring

/-- All actual anti-discriminant physical gradients mutually commute.
The off-diagonal endpoint terms cancel at both Wronskian-product endpoints. -/
theorem classicalGradientPoissonBracket_anti_eq_zero
    (Φ : Curve (ℂ × ℂ)) (z w : ℂ) :
    classicalGradientPoissonBracket (classicalAntiDiscriminantGradient Φ z)
      (classicalAntiDiscriminantGradient Φ w) = 0 := by
  by_cases hzw : z = w
  · subst w
    exact classicalGradientPoissonBracket_self _
  have hzA := continuous_classicalEndpointGradient Φ z (0,1) (ContinuousLinearMap.fst ℂ ℂ ℂ)
  have hzB := continuous_classicalEndpointGradient Φ z (1,0) (ContinuousLinearMap.snd ℂ ℂ ℂ)
  have hwA := continuous_classicalEndpointGradient Φ w (0,1) (ContinuousLinearMap.fst ℂ ℂ ℂ)
  have hwB := continuous_classicalEndpointGradient Φ w (1,0) (ContinuousLinearMap.snd ℂ ℂ ℂ)
  have hmul : 2*(z-w)*classicalGradientPoissonBracket
      (classicalAntiDiscriminantGradient Φ z) (classicalAntiDiscriminantGradient Φ w) = 0 := by
    change 2*(z-w)*classicalGradientPoissonBracket
      (classicalEndpointGradient Φ z (0,1) (ContinuousLinearMap.fst ℂ ℂ ℂ)+
        classicalEndpointGradient Φ z (1,0) (ContinuousLinearMap.snd ℂ ℂ ℂ))
      (classicalEndpointGradient Φ w (0,1) (ContinuousLinearMap.fst ℂ ℂ ℂ)+
        classicalEndpointGradient Φ w (1,0) (ContinuousLinearMap.snd ℂ ℂ ℂ)) = _
    rw [classicalGradientPoissonBracket_add_left _ _ _ hzA hzB (hwA.add hwB),
      classicalGradientPoissonBracket_add_right _ _ _ hzA hwA hwB,
      classicalGradientPoissonBracket_add_right _ _ _ hzB hwA hwB]
    change 2*(z-w)*((classicalEndpointPoissonBracket Φ z w
      (0,1) (ContinuousLinearMap.fst ℂ ℂ ℂ) (0,1) (ContinuousLinearMap.fst ℂ ℂ ℂ)+
        classicalEndpointPoissonBracket Φ z w (0,1) (ContinuousLinearMap.fst ℂ ℂ ℂ) (1,0) (ContinuousLinearMap.snd ℂ ℂ ℂ))+
      (classicalEndpointPoissonBracket Φ z w (1,0) (ContinuousLinearMap.snd ℂ ℂ ℂ) (0,1) (ContinuousLinearMap.fst ℂ ℂ ℂ)+
        classicalEndpointPoissonBracket Φ z w (1,0) (ContinuousLinearMap.snd ℂ ℂ ℂ) (1,0) (ContinuousLinearMap.snd ℂ ℂ ℂ))) = _
    rw [mul_add,mul_add,mul_add,classicalEndpointPoissonBracket_mul,classicalEndpointPoissonBracket_mul,
      classicalEndpointPoissonBracket_mul,classicalEndpointPoissonBracket_mul]
    simp only [classicalCrossWronskian,classicalSolution_one_eq_monodromy,
      ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd']
    ring
  exact (mul_eq_zero.mp hmul).resolve_left (mul_ne_zero (by norm_num) (sub_ne_zero.mpr hzw))

end NLS.ZakharovShabat
