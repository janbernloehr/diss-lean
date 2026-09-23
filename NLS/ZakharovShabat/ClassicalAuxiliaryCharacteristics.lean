import NLS.ZakharovShabat.ClassicalSeparatedCharacteristics

/-! # Classical characteristics of the actual auxiliary endpoint domains

The auxiliary Dirichlet domain requires `f₋ + i f₊ = 0` at both endpoints;
the auxiliary Neumann domain requires `f₋ - i f₊ = 0`. Their monodromy
characteristics differ by the classical anti-discriminant. The printed
starred D/N formulas on page 53 use the opposite signs from these domains;
the sign comparison is stated explicitly below.
-/

noncomputable section
open Set Complex Matrix
open NLS.LinearVolterra
namespace NLS.ZakharovShabat
open BoundaryCondition

/-- The sine-normalized characteristic of the actual auxiliary endpoint condition. -/
def classicalAuxiliaryCharacteristic (b : BoundaryCondition) (Φ : Curve (ℂ × ℂ)) (z : ℂ) : ℂ :=
  ((classicalMonodromy Φ z) 1 1 - (classicalMonodromy Φ z) 0 0 -
    extensionSign b * I * ((classicalMonodromy Φ z) 1 0 + (classicalMonodromy Φ z) 0 1))/(2*I)

/-- The difference of the actual auxiliary Neumann and Dirichlet characteristics is the anti-discriminant. -/
theorem classicalAntiDiscriminant_eq_auxiliary_sub (Φ : Curve (ℂ × ℂ)) (z : ℂ) :
    classicalAntiDiscriminant Φ z =
      classicalAuxiliaryCharacteristic .neumann Φ z -
        classicalAuxiliaryCharacteristic .dirichlet Φ z := by
  simp only [classicalAuxiliaryCharacteristic, classicalAntiDiscriminant, extensionSign]
  field_simp
  ring

/-- The source's printed starred Dirichlet formula has the actual auxiliary Neumann sign. -/
theorem printed_starredDirichlet_eq_actualNeumann (Φ : Curve (ℂ × ℂ)) (z : ℂ) :
    ((classicalMonodromy Φ z) 1 1 + I*(classicalMonodromy Φ z) 1 0 +
      I*(classicalMonodromy Φ z) 0 1 - (classicalMonodromy Φ z) 0 0)/(2*I) =
        classicalAuxiliaryCharacteristic .neumann Φ z := by
  simp only [classicalAuxiliaryCharacteristic, extensionSign]
  ring

/-- The source's printed starred Neumann formula has the actual auxiliary Dirichlet sign. -/
theorem printed_starredNeumann_eq_actualDirichlet (Φ : Curve (ℂ × ℂ)) (z : ℂ) :
    ((classicalMonodromy Φ z) 1 1 - I*(classicalMonodromy Φ z) 1 0 -
      I*(classicalMonodromy Φ z) 0 1 - (classicalMonodromy Φ z) 0 0)/(2*I) =
        classicalAuxiliaryCharacteristic .dirichlet Φ z := by
  simp only [classicalAuxiliaryCharacteristic, extensionSign]
  ring

/-- Each actual auxiliary characteristic is an average of ordinary ones plus an anti-trace term. -/
theorem classicalAuxiliaryCharacteristic_eq_ordinary (b : BoundaryCondition)
    (Φ : Curve (ℂ × ℂ)) (z : ℂ) :
    classicalAuxiliaryCharacteristic b Φ z =
      (classicalSeparatedCharacteristic .dirichlet Φ z +
        classicalSeparatedCharacteristic .neumann Φ z)/2 -
        extensionSign b * classicalAntiDiscriminant Φ z/2 := by
  cases b <;> simp [classicalAuxiliaryCharacteristic, classicalSeparatedCharacteristic,
    classicalAntiDiscriminant, extensionSign] <;> ring_nf <;> simp [Complex.inv_I] <;> ring_nf <;> simp [I_sq] <;> ring

/-- A zero is precisely the actual auxiliary endpoint equation for normalized initial data. -/
theorem classicalAuxiliaryCharacteristic_eq_zero_iff (b : BoundaryCondition)
    (Φ : Curve (ℂ × ℂ)) (z : ℂ) :
    classicalAuxiliaryCharacteristic b Φ z = 0 ↔
      (classicalSolution Φ z (1,I*extensionSign b) 1).1 =
        -I*extensionSign b*(classicalSolution Φ z (1,I*extensionSign b) 1).2 := by
  rw [classicalAuxiliaryCharacteristic, div_eq_zero_iff]
  simp only [mul_eq_zero, OfNat.ofNat_ne_zero, I_ne_zero, or_self, or_false]
  rw [classicalSolution_eq_columns Φ z (1,I*extensionSign b) ⟨1,by constructor <;> norm_num⟩]
  simp only [classicalMonodromy,classicalFundamentalMatrix,Prod.fst_add,Prod.snd_add,
    Prod.smul_fst,Prod.smul_snd,smul_eq_mul,one_mul,Matrix.of_apply,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
  cases b <;> simp only [extensionSign,one_mul,neg_one_mul] <;>
    constructor <;> intro h <;> linear_combination (norm := (ring_nf; simp [I_sq])) -h

/-- The actual auxiliary characteristic is jointly complex analytic for continuous potentials. -/
theorem analyticOnNhd_classicalAuxiliaryCharacteristic_joint (b : BoundaryCondition) :
    AnalyticOnNhd ℂ (fun q : ℂ × Curve (ℂ × ℂ) => classicalAuxiliaryCharacteristic b q.2 q.1) univ := by
  intro q _
  have h₁ := analyticOnNhd_classicalSolution_joint (1,0) ⟨1,by constructor <;> norm_num⟩ q (mem_univ _)
  have h₂ := analyticOnNhd_classicalSolution_joint (0,1) ⟨1,by constructor <;> norm_num⟩ q (mem_univ _)
  simp only [classicalAuxiliaryCharacteristic,classicalMonodromy,classicalFundamentalMatrix]
  exact (((analyticAt_snd.comp h₂).sub (analyticAt_fst.comp h₁)).sub
    (analyticAt_const.mul ((analyticAt_snd.comp h₁).add (analyticAt_fst.comp h₂)))).div
      analyticAt_const (mul_ne_zero (by norm_num) I_ne_zero)

/-- Both actual auxiliary characteristics have the source's signed free sine normalization. -/
@[simp] theorem classicalAuxiliaryCharacteristic_free (b : BoundaryCondition) (z : ℂ) :
    classicalAuxiliaryCharacteristic b 0 z = sin z := by
  rw [classicalAuxiliaryCharacteristic_eq_ordinary]
  simp [classicalSeparatedCharacteristic_free, classicalAntiDiscriminant_free]

end NLS.ZakharovShabat
