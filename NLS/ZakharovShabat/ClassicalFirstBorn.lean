import NLS.ZakharovShabat.ClassicalDuhamel
import NLS.ZakharovShabat.ClassicalFreeDiscriminant
import NLS.ComplexAnalysis.OscillatoryIntegralParts

/-! # The first Born term in the actual fundamental solution

Subtracting the free solution from the original Duhamel equations
gives the oscillatory first iterate plus an integral of the actual
remainder. This is the identity used in Appendix G.1–G.3.
-/

noncomputable section
open Set Complex MeasureTheory
open NLS.LinearVolterra NLS.ComplexAnalysis
namespace NLS.ZakharovShabat

/-- The free evolution, with the original two component signs. -/
def classicalFreeVector (z : ℂ) (v : ℂ × ℂ) (t : ℝ) : ℂ × ℂ :=
  (exp (-I*z*t)*v.1,exp (I*z*t)*v.2)

/-- The error of the actual solution relative to its free evolution. -/
def classicalSolutionRemainder (φ : Curve (ℂ × ℂ)) (z : ℂ) (v : ℂ × ℂ) (t : ℝ) : ℂ × ℂ :=
  classicalSolution φ z v t-classicalFreeVector z v t

/-- The first oscillatory correction, before any estimate is applied. -/
def classicalFirstBornVector (φ : Curve (ℂ × ℂ)) (z : ℂ) (v : ℂ × ℂ) (t : ℝ) : ℂ × ℂ :=
  (I*oscillatoryIntegral (-I*z) t (fun s => (extend φ s).1)*v.2,
    (-I)*oscillatoryIntegral (I*z) t (fun s => (extend φ s).2)*v.1)

@[simp] theorem classicalSolutionRemainder_zero (φ : Curve (ℂ × ℂ)) (z : ℂ) (v : ℂ × ℂ) :
    classicalSolutionRemainder φ z v 0 = 0 := by
  simp [classicalSolutionRemainder,classicalFreeVector]

@[simp] theorem classicalSolutionRemainder_free (z : ℂ) (v : ℂ × ℂ) (t : Icc (0 : ℝ) 1) :
    classicalSolutionRemainder 0 z v t = 0 := by
  simp [classicalSolutionRemainder,classicalFreeVector,classicalSolution_free]

theorem continuous_classicalSolutionRemainder (φ : Curve (ℂ × ℂ)) (z : ℂ) (v : ℂ × ℂ) :
    Continuous (classicalSolutionRemainder φ z v) := by
  unfold classicalSolutionRemainder classicalFreeVector
  exact (continuous_classicalSolution φ z v).sub (by fun_prop)

private theorem firstBorn_kernel_product (c : ℂ) (t s : ℝ) :
    exp (c*(t-s))*exp (-c*s) = oscillatoryKernel c t s := by
  rw [← exp_add]
  unfold oscillatoryKernel
  congr 1
  push_cast
  ring

/-- The first actual remainder coordinate equals the first Born term
plus the original free propagator applied to the opposite remainder. -/
theorem classicalSolutionRemainder_fst_duhamel
    (φ : Curve (ℂ × ℂ)) (z : ℂ) (v : ℂ × ℂ) (t : Icc (0 : ℝ) 1) :
    (classicalSolutionRemainder φ z v t).1 = (classicalFirstBornVector φ z v t).1 +
      ∫ s in (0 : ℝ)..t.val, exp (-I*z*(t.val-s))*
        (I*(extend φ s).1*(classicalSolutionRemainder φ z v s).2) := by
  have hd := classicalWeightedSolution_fst_duhamel φ z 0 v t
  simp only [classicalWeightedSolution_zero_weight,zero_sub,← neg_mul] at hd
  have hkernel (s : ℝ) : exp (-I*z*(t.val-s))*exp (I*z*s) = oscillatoryKernel (-I*z) t s := by
    simpa only [neg_neg,neg_mul] using firstBorn_kernel_product (-I*z) t s
  have hsplit : (fun s : ℝ => exp (-I*z*(t.val-s))*(I*(extend φ s).1*(classicalSolution φ z v s).2)) =
      fun s => (I*v.2)*(oscillatoryKernel (-I*z) t s*(extend φ s).1) +
        exp (-I*z*(t.val-s))*(I*(extend φ s).1*(classicalSolutionRemainder φ z v s).2) := by
    funext s
    dsimp only [classicalSolutionRemainder,classicalFreeVector,Prod.snd_sub]
    linear_combination (I*(extend φ s).1*v.2)*hkernel s
  rw [hsplit,intervalIntegral.integral_add] at hd
  · rw [intervalIntegral.integral_const_mul] at hd
    change (classicalSolution φ z v t).1 = exp (-I*z*t.val)*v.1+
      ((I*v.2)*oscillatoryIntegral (-I*z) t (fun s => (extend φ s).1)+_) at hd
    change (classicalSolution φ z v t).1-exp (-I*z*t.val)*v.1 =
      I*oscillatoryIntegral (-I*z) t (fun s => (extend φ s).1)*v.2+_
    linear_combination hd
  · exact (show Continuous (fun s : ℝ => (I*v.2)*(oscillatoryKernel (-I*z) t s*(extend φ s).1)) by
      unfold oscillatoryKernel; have hφ := continuous_extend φ; fun_prop).intervalIntegrable _ _
  · exact (show Continuous (fun s : ℝ => exp (-I*z*(t.val-s))*
      (I*(extend φ s).1*(classicalSolutionRemainder φ z v s).2)) by
      have hφ := continuous_extend φ
      have hr := continuous_classicalSolutionRemainder φ z v
      exact (show Continuous (fun s : ℝ => exp (-I*z*(t.val-s))) by fun_prop).mul
        ((continuous_const.mul hφ.fst).mul hr.snd)).intervalIntegrable _ _

/-- The second remainder coordinate retains the opposite potential
sign and the opposite free exponential. -/
theorem classicalSolutionRemainder_snd_duhamel
    (φ : Curve (ℂ × ℂ)) (z : ℂ) (v : ℂ × ℂ) (t : Icc (0 : ℝ) 1) :
    (classicalSolutionRemainder φ z v t).2 = (classicalFirstBornVector φ z v t).2 +
      ∫ s in (0 : ℝ)..t.val, exp (I*z*(t.val-s))*
        ((-I)*(extend φ s).2*(classicalSolutionRemainder φ z v s).1) := by
  have hd := classicalWeightedSolution_snd_duhamel φ z 0 v t
  simp only [classicalWeightedSolution_zero_weight,zero_add] at hd
  have hkernel (s : ℝ) : exp (I*z*(t.val-s))*exp (-I*z*s) = oscillatoryKernel (I*z) t s := by
    simpa only [neg_mul] using firstBorn_kernel_product (I*z) t s
  have hsplit : (fun s : ℝ => exp (I*z*(t.val-s))*((-I)*(extend φ s).2*(classicalSolution φ z v s).1)) =
      fun s => ((-I)*v.1)*(oscillatoryKernel (I*z) t s*(extend φ s).2) +
        exp (I*z*(t.val-s))*((-I)*(extend φ s).2*(classicalSolutionRemainder φ z v s).1) := by
    funext s
    dsimp only [classicalSolutionRemainder,classicalFreeVector,Prod.fst_sub]
    linear_combination ((-I)*(extend φ s).2*v.1)*hkernel s
  rw [hsplit,intervalIntegral.integral_add] at hd
  · rw [intervalIntegral.integral_const_mul] at hd
    change (classicalSolution φ z v t).2 = exp (I*z*t.val)*v.2+
      (((-I)*v.1)*oscillatoryIntegral (I*z) t (fun s => (extend φ s).2)+_) at hd
    change (classicalSolution φ z v t).2-exp (I*z*t.val)*v.2 =
      (-I)*oscillatoryIntegral (I*z) t (fun s => (extend φ s).2)*v.1+_
    linear_combination hd
  · exact (show Continuous (fun s : ℝ => ((-I)*v.1)*(oscillatoryKernel (I*z) t s*(extend φ s).2)) by
      unfold oscillatoryKernel; have hφ := continuous_extend φ; fun_prop).intervalIntegrable _ _
  · exact (show Continuous (fun s : ℝ => exp (I*z*(t.val-s))*
      ((-I)*(extend φ s).2*(classicalSolutionRemainder φ z v s).1)) by
      have hφ := continuous_extend φ
      have hr := continuous_classicalSolutionRemainder φ z v
      exact (show Continuous (fun s : ℝ => exp (I*z*(t.val-s))) by fun_prop).mul
        ((continuous_const.mul hφ.snd).mul hr.fst)).intervalIntegrable _ _

end NLS.ZakharovShabat
