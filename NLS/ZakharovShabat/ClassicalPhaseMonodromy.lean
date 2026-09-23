import NLS.ZakharovShabat.ClassicalAuxiliaryCharacteristics
import NLS.ZakharovShabat.ClassicalAuxiliaryPhase
import NLS.ZakharovShabat.ClassicalBoundaryMonodromy

/-! # Phase conjugation of classical initial-value solutions and monodromy

The physical phase of a solution at the rotated potential solves the
original initial-value problem. Uniqueness then gives exact matrix-entry
identities, allowing the actual auxiliary endpoint characteristics to be
compared with ordinary separated characteristics without an asserted
product-normalization identity.
-/

noncomputable section
open Set Complex Matrix
open NLS.LinearVolterra
namespace NLS.ZakharovShabat
open BoundaryCondition

/-- Rotate a continuous physical potential by opposite phases in its two components. -/
def classicalSourcePhase (Φ : Curve (ℂ × ℂ)) : Curve (ℂ × ℂ) :=
  ⟨fun t => (I*(Φ t).1,-I*(Φ t).2), by fun_prop⟩

@[simp] theorem classicalSourcePhase_apply (Φ : Curve (ℂ × ℂ)) (t : Icc (0 : ℝ) 1) :
    classicalSourcePhase Φ t = (I*(Φ t).1,-I*(Φ t).2) := rfl

/-- The first-order ODE coefficients intertwine with the physical phase. -/
theorem classicalODECoefficient_auxiliaryPhase (v y : ℂ × ℂ) (z : ℂ) :
    classicalODECoefficient v z (auxiliaryPhase ℂ y) =
      auxiliaryPhase ℂ (classicalODECoefficient (I*v.1,-I*v.2) z y) := by
  apply Prod.ext <;>
    simp only [classicalODECoefficient_apply, auxiliaryPhase_apply, smul_eq_mul]
  · ring
  · ring_nf
    simp only [I_sq, I_pow_three]
    ring

/-- Phase conjugation holds for every initial vector and every point of the closed interval. -/
theorem classicalSolution_auxiliaryPhase (Φ : Curve (ℂ × ℂ)) (z : ℂ)
    (v : ℂ × ℂ) (t : Icc (0 : ℝ) 1) :
    classicalSolution Φ z (auxiliaryPhase ℂ v) t =
      auxiliaryPhase ℂ (classicalSolution (classicalSourcePhase Φ) z v t) := by
  let u : ℝ → ℂ × ℂ := fun s =>
    auxiliaryPhase ℂ (classicalSolution (classicalSourcePhase Φ) z v s)
  have hu : ContinuousOn u (Icc 0 1) :=
    ((auxiliaryPhase ℂ).continuous.comp
      (continuous_classicalSolution (classicalSourcePhase Φ) z v)).continuousOn
  have h0 : u 0 = auxiliaryPhase ℂ v := by simp [u]
  have hd (s : Icc (0 : ℝ) 1) (_ : s.val ∈ Ioo (0 : ℝ) 1) :
      HasDerivAt u (classicalODECoefficient (Φ s) z (u s)) s := by
    have hs := hasDerivAt_classicalSolution (classicalSourcePhase Φ) z v s
    have hprod := (HasFDerivAt.hasDerivAt hs.fst).prodMk
      ((HasFDerivAt.hasDerivAt hs.snd).const_mul I)
    convert! hprod using 1
    apply Prod.ext <;> simp only [u, classicalSourcePhase_apply, auxiliaryPhase_apply,
      classicalODECoefficient_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.toSpanSingleton_apply, one_smul] <;>
      dsimp <;> ring_nf <;> simp only [I_sq, I_pow_three] <;> ring
  exact (classicalSolution_unique Φ z (auxiliaryPhase ℂ v) u hu h0 hd t.property).symm

private theorem phase_first_column (Φ : Curve (ℂ × ℂ)) (z : ℂ) :
    classicalSolution Φ z (1,0) 1 =
      auxiliaryPhase ℂ (classicalSolution (classicalSourcePhase Φ) z (1,0) 1) := by
  simpa using classicalSolution_auxiliaryPhase Φ z (1,0)
    ⟨1, by constructor <;> norm_num⟩

private theorem phase_second_column (Φ : Curve (ℂ × ℂ)) (z : ℂ) :
    I • classicalSolution Φ z (0,1) 1 =
      auxiliaryPhase ℂ (classicalSolution (classicalSourcePhase Φ) z (0,1) 1) := by
  have h := classicalSolution_auxiliaryPhase Φ z (0,1)
    ⟨1, by constructor <;> norm_num⟩
  have hi : auxiliaryPhase ℂ (0,1) = I • (0,1) := by simp
  rw [hi, classicalSolution_smul] at h
  exact h

/-- Phase rotation preserves the upper-left monodromy entry. -/
theorem classicalMonodromy_phase_zero_zero (Φ : Curve (ℂ × ℂ)) (z : ℂ) :
    classicalMonodromy (classicalSourcePhase Φ) z 0 0 = classicalMonodromy Φ z 0 0 := by
  have h := congrArg Prod.fst (phase_first_column Φ z)
  simpa [classicalMonodromy, classicalFundamentalMatrix] using h.symm

/-- Phase rotation multiplies the upper-right monodromy entry by `i`. -/
theorem classicalMonodromy_phase_zero_one (Φ : Curve (ℂ × ℂ)) (z : ℂ) :
    classicalMonodromy (classicalSourcePhase Φ) z 0 1 = I * classicalMonodromy Φ z 0 1 := by
  have h := congrArg Prod.fst (phase_second_column Φ z)
  simpa [classicalMonodromy, classicalFundamentalMatrix, Prod.smul_fst, smul_eq_mul]
    using h.symm

/-- Phase rotation multiplies the lower-left monodromy entry by `-i`. -/
theorem classicalMonodromy_phase_one_zero (Φ : Curve (ℂ × ℂ)) (z : ℂ) :
    classicalMonodromy (classicalSourcePhase Φ) z 1 0 = -I * classicalMonodromy Φ z 1 0 := by
  have h := congrArg Prod.snd (phase_first_column Φ z)
  have he : classicalMonodromy Φ z 1 0 =
      I * classicalMonodromy (classicalSourcePhase Φ) z 1 0 := by
    simpa [classicalMonodromy, classicalFundamentalMatrix, auxiliaryPhase_apply, smul_eq_mul] using h
  calc
    _ = -I * (I * classicalMonodromy (classicalSourcePhase Φ) z 1 0) := by
      simp [← mul_assoc]
    _ = -I * classicalMonodromy Φ z 1 0 := by rw [he]

/-- Phase rotation preserves the lower-right monodromy entry. -/
theorem classicalMonodromy_phase_one_one (Φ : Curve (ℂ × ℂ)) (z : ℂ) :
    classicalMonodromy (classicalSourcePhase Φ) z 1 1 = classicalMonodromy Φ z 1 1 := by
  have h := congrArg Prod.snd (phase_second_column Φ z)
  have he : I * classicalMonodromy Φ z 1 1 =
      I * classicalMonodromy (classicalSourcePhase Φ) z 1 1 := by
    simpa [classicalMonodromy, classicalFundamentalMatrix, auxiliaryPhase_apply,
      Prod.smul_snd, smul_eq_mul] using h
  exact mul_left_cancel₀ I_ne_zero he.symm

/-- The actual auxiliary characteristic is the ordinary separated characteristic of the rotated potential. -/
theorem classicalAuxiliaryCharacteristic_eq_separated_phase (b : BoundaryCondition)
    (Φ : Curve (ℂ × ℂ)) (z : ℂ) :
    classicalAuxiliaryCharacteristic b Φ z =
      classicalSeparatedCharacteristic b (classicalSourcePhase Φ) z := by
  rw [classicalAuxiliaryCharacteristic, classicalSeparatedCharacteristic,
    classicalMonodromy_phase_zero_zero, classicalMonodromy_phase_zero_one,
    classicalMonodromy_phase_one_zero, classicalMonodromy_phase_one_one]
  cases b <;> simp only [extensionSign, one_mul, neg_one_mul] <;> ring

/-- The classical discriminant is unchanged by the auxiliary phase rotation. -/
theorem classicalDiscriminant_phase (Φ : Curve (ℂ × ℂ)) (z : ℂ) :
    classicalDiscriminant (classicalSourcePhase Φ) z = classicalDiscriminant Φ z := by
  simp only [classicalDiscriminant, Matrix.trace_fin_two,
    classicalMonodromy_phase_zero_zero, classicalMonodromy_phase_one_one]

/-- The actual starred-characteristic difference equals the ordinary characteristic difference after phase rotation. -/
theorem classicalAntiDiscriminant_eq_separated_phase_sub
    (Φ : Curve (ℂ × ℂ)) (z : ℂ) :
    classicalAntiDiscriminant Φ z =
      classicalSeparatedCharacteristic .neumann (classicalSourcePhase Φ) z -
        classicalSeparatedCharacteristic .dirichlet (classicalSourcePhase Φ) z := by
  rw [classicalAntiDiscriminant_eq_auxiliary_sub,
    classicalAuxiliaryCharacteristic_eq_separated_phase,
    classicalAuxiliaryCharacteristic_eq_separated_phase]

end NLS.ZakharovShabat
