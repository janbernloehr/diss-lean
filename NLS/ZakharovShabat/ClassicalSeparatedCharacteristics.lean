import NLS.ZakharovShabat.ClassicalMonodromyAnalytic
import NLS.ZakharovShabat.ClassicalFreeDiscriminant
import NLS.ZakharovShabat.IntervalExtension

/-! # Classical Dirichlet and Neumann characteristic functions
The literal endpoint formulas have the source sine normalization. They
vanish exactly when the solution with normalized separated initial data
satisfies the same condition at the other endpoint.
-/

noncomputable section
open Set Complex Matrix
open NLS.LinearVolterra
namespace NLS.ZakharovShabat
open BoundaryCondition

/-- The source-normalized separated endpoint characteristic. -/
def classicalSeparatedCharacteristic (b : BoundaryCondition) (Φ : Curve (ℂ × ℂ)) (z : ℂ) : ℂ :=
  ((classicalMonodromy Φ z) 1 1 - (classicalMonodromy Φ z) 0 0 +
    extensionSign b * ((classicalMonodromy Φ z) 1 0 - (classicalMonodromy Φ z) 0 1))/(2*I)

/-- The classical anti-discriminant is the sum of the two off-diagonal monodromy entries. -/
def classicalAntiDiscriminant (Φ : Curve (ℂ × ℂ)) (z : ℂ) : ℂ :=
  (classicalMonodromy Φ z) 0 1 + (classicalMonodromy Φ z) 1 0

/-- Both separated characteristics are jointly analytic for continuous potentials. -/
theorem analyticOnNhd_classicalSeparatedCharacteristic_joint (b : BoundaryCondition) :
    AnalyticOnNhd ℂ (fun q : ℂ × Curve (ℂ × ℂ) => classicalSeparatedCharacteristic b q.2 q.1) univ := by
  intro q _
  have h₁ := analyticOnNhd_classicalSolution_joint (1,0) ⟨1,by constructor <;> norm_num⟩ q (mem_univ _)
  have h₂ := analyticOnNhd_classicalSolution_joint (0,1) ⟨1,by constructor <;> norm_num⟩ q (mem_univ _)
  simp only [classicalSeparatedCharacteristic,classicalMonodromy,classicalFundamentalMatrix]
  exact (((analyticAt_snd.comp h₂).sub (analyticAt_fst.comp h₁)).add
    (analyticAt_const.mul ((analyticAt_snd.comp h₁).sub (analyticAt_fst.comp h₂)))).div
      analyticAt_const (mul_ne_zero (by norm_num) I_ne_zero)

/-- The off-diagonal anti-discriminant is jointly analytic on the same domain. -/
theorem analyticOnNhd_classicalAntiDiscriminant_joint :
    AnalyticOnNhd ℂ (fun q : ℂ × Curve (ℂ × ℂ) => classicalAntiDiscriminant q.2 q.1) univ := by
  intro q _
  have h₁ := analyticOnNhd_classicalSolution_joint (1,0) ⟨1,by constructor <;> norm_num⟩ q (mem_univ _)
  have h₂ := analyticOnNhd_classicalSolution_joint (0,1) ⟨1,by constructor <;> norm_num⟩ q (mem_univ _)
  exact (analyticAt_fst.comp h₂).add (analyticAt_snd.comp h₁)

/-- A zero is exactly the original separated endpoint condition for normalized initial data. -/
theorem classicalSeparatedCharacteristic_eq_zero_iff (b : BoundaryCondition) (Φ : Curve (ℂ × ℂ)) (z : ℂ) :
    classicalSeparatedCharacteristic b Φ z = 0 ↔
      (classicalSolution Φ z (1,extensionSign b) 1).1 =
        extensionSign b * (classicalSolution Φ z (1,extensionSign b) 1).2 := by
  rw [classicalSeparatedCharacteristic,div_eq_zero_iff]
  simp only [mul_eq_zero,OfNat.ofNat_ne_zero,I_ne_zero,or_self,or_false]
  rw [classicalSolution_eq_columns Φ z (1,extensionSign b) ⟨1,by constructor <;> norm_num⟩]
  simp only [classicalMonodromy,classicalFundamentalMatrix,Prod.fst_add,Prod.snd_add,
    Prod.smul_fst,Prod.smul_snd,smul_eq_mul,one_mul,Matrix.of_apply,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
  cases b <;> simp only [extensionSign,one_mul,neg_one_mul] <;> constructor <;> intro h <;> linear_combination -h

/-- Both free separated characteristics are exactly sine, with no unspecified scalar factor. -/
@[simp] theorem classicalSeparatedCharacteristic_free (b : BoundaryCondition) (z : ℂ) :
    classicalSeparatedCharacteristic b 0 z = sin z := by
  have hf := classicalFundamentalMatrix_free z ⟨1,by constructor <;> norm_num⟩
  unfold classicalSeparatedCharacteristic classicalMonodromy
  rw [hf]
  change (exp (I*z*1)-exp (-I*z*1)+extensionSign b*(0-0))/(2*I) = sin z
  simp only [mul_one,sub_self,mul_zero,add_zero]
  rw [Complex.sin]
  simp only [div_eq_mul_inv,_root_.mul_inv_rev,Complex.inv_I]
  ring_nf

/-- The free anti-discriminant vanishes identically. -/
@[simp] theorem classicalAntiDiscriminant_free (z : ℂ) : classicalAntiDiscriminant 0 z = 0 := by
  have hf := classicalFundamentalMatrix_free z ⟨1,by constructor <;> norm_num⟩
  unfold classicalAntiDiscriminant classicalMonodromy
  rw [hf]
  simp

/-- The unimodular monodromy gives the global characteristic and anti-discriminant identity. -/
theorem classicalDiscriminant_sq_sub_four (Φ : Curve (ℂ × ℂ)) (z : ℂ) :
    (classicalDiscriminant Φ z)^2-4 = (classicalAntiDiscriminant Φ z)^2 -
      4*classicalSeparatedCharacteristic .dirichlet Φ z*classicalSeparatedCharacteristic .neumann Φ z := by
  have hd := det_classicalMonodromy Φ z
  simp only [Matrix.det_fin_two] at hd
  simp only [classicalDiscriminant,Matrix.trace_fin_two,classicalAntiDiscriminant,
    classicalSeparatedCharacteristic,extensionSign,one_mul,neg_one_mul]
  simp only [div_eq_mul_inv,_root_.mul_inv_rev,Complex.inv_I]
  linear_combination (norm := (ring_nf; simp [I_sq])) 4 * hd

/-- At either separated eigenvalue the discriminant square minus four is the anti-discriminant square. -/
theorem classicalDiscriminant_sq_sub_four_of_separated_zero (b : BoundaryCondition)
    (Φ : Curve (ℂ × ℂ)) (z : ℂ) (hz : classicalSeparatedCharacteristic b Φ z = 0) :
    (classicalDiscriminant Φ z)^2-4 = (classicalAntiDiscriminant Φ z)^2 := by
  rw [classicalDiscriminant_sq_sub_four]
  cases b <;> simp [hz]

end NLS.ZakharovShabat
