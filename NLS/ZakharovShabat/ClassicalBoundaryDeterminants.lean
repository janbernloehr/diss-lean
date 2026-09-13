import NLS.ZakharovShabat.ClassicalFundamentalSolution
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Classical endpoint characteristic determinants

The fundamental matrix propagates every initial vector. Its characteristic
roots are exactly the multipliers of nonzero classical solutions. In particular,
periodic and antiperiodic solutions correspond to discriminant values two and
minus two. Identification with the coefficient spectral products is still needed.
-/

noncomputable section
open Set Complex Matrix
open NLS.LinearVolterra
namespace NLS.ZakharovShabat

/-- The two normalized fundamental columns span every initial-value solution. -/
theorem classicalSolution_eq_columns (φ : Curve (ℂ × ℂ)) (z : ℂ) (v : ℂ × ℂ)
    (t : Icc (0 : ℝ) 1) :
    classicalSolution φ z v t = v.1 • classicalSolution φ z (1,0) t +
      v.2 • classicalSolution φ z (0,1) t := by
  have h := classicalSolution_unique φ z v
    (fun s => v.1 • classicalSolution φ z (1,0) s + v.2 • classicalSolution φ z (0,1) s)
    (((continuous_classicalSolution φ z (1,0)).const_smul v.1).add
      ((continuous_classicalSolution φ z (0,1)).const_smul v.2)).continuousOn
    (by simp [Prod.smul_mk,smul_eq_mul]) (by
      intro s _
      have hd := ((hasDerivAt_classicalSolution φ z (1,0) s).const_smul v.1).add
        ((hasDerivAt_classicalSolution φ z (0,1) s).const_smul v.2)
      simp only [map_add,map_smul]
      convert! hd using 1)
  exact (h t.property).symm

/-- The fundamental matrix propagates arbitrary complex initial coordinates. -/
theorem classicalFundamentalMatrix_mulVec (φ : Curve (ℂ × ℂ)) (z : ℂ) (v : Fin 2 → ℂ)
    (t : Icc (0 : ℝ) 1) :
    classicalFundamentalMatrix φ z t *ᵥ v =
      ![(classicalSolution φ z (v 0,v 1) t).1,(classicalSolution φ z (v 0,v 1) t).2] := by
  rw [classicalSolution_eq_columns]
  ext i
  fin_cases i <;> simp [classicalFundamentalMatrix,Matrix.mulVec,Matrix.vecHead,Matrix.vecTail,smul_eq_mul] <;> ring

/-- The endpoint matrix kernel is exactly the boundary multiplier condition. -/
theorem classicalMonodromy_kernel_iff (φ : Curve (ℂ × ℂ)) (z σ : ℂ) (v : Fin 2 → ℂ) :
    (classicalMonodromy φ z - σ • 1) *ᵥ v = 0 ↔
      classicalSolution φ z (v 0,v 1) 1 = σ • (v 0,v 1) := by
  rw [Matrix.sub_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,sub_eq_zero]
  rw [show classicalMonodromy φ z *ᵥ v =
      ![(classicalSolution φ z (v 0,v 1) 1).1,(classicalSolution φ z (v 0,v 1) 1).2] from
    classicalFundamentalMatrix_mulVec φ z v ⟨1,by constructor <;> norm_num⟩]
  constructor
  · intro h
    exact Prod.ext (congrFun h 0) (congrFun h 1)
  · intro h
    ext i
    fin_cases i
    · exact congrArg Prod.fst h
    · exact congrArg Prod.snd h

/-- A characteristic determinant vanishes exactly when a nonzero solution has the prescribed endpoint multiplier. -/
theorem det_classicalMonodromy_sub_scalar_eq_zero_iff (φ : Curve (ℂ × ℂ)) (z σ : ℂ) :
    (classicalMonodromy φ z - σ • 1).det = 0 ↔
      ∃ v : ℂ × ℂ, v ≠ 0 ∧ classicalSolution φ z v 1 = σ • v := by
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  constructor
  · rintro ⟨v,hv,he⟩
    refine ⟨(v 0,v 1),?_,(classicalMonodromy_kernel_iff φ z σ v).mp he⟩
    intro h
    apply hv
    ext i
    fin_cases i
    · exact congrArg Prod.fst h
    · exact congrArg Prod.snd h
  · rintro ⟨v,hv,he⟩
    refine ⟨![v.1,v.2],?_,(classicalMonodromy_kernel_iff φ z σ _).mpr he⟩
    intro h
    apply hv
    exact Prod.ext (congrFun h 0) (congrFun h 1)

/-- Periodic classical solutions occur exactly at discriminant value two. -/
theorem classicalDiscriminant_eq_two_iff (φ : Curve (ℂ × ℂ)) (z : ℂ) :
    classicalDiscriminant φ z = 2 ↔
      ∃ v : ℂ × ℂ, v ≠ 0 ∧ classicalSolution φ z v 1 = v := by
  have h := det_classicalMonodromy_sub_scalar_eq_zero_iff φ z 1
  rw [det_classicalMonodromy_sub_scalar] at h
  rw [show (1 : ℂ)^2-1*classicalDiscriminant φ z+1 = 2-classicalDiscriminant φ z by ring] at h
  rw [sub_eq_zero,eq_comm] at h
  simpa only [one_smul] using h

/-- Antiperiodic classical solutions occur exactly at discriminant value minus two. -/
theorem classicalDiscriminant_eq_neg_two_iff (φ : Curve (ℂ × ℂ)) (z : ℂ) :
    classicalDiscriminant φ z = -2 ↔
      ∃ v : ℂ × ℂ, v ≠ 0 ∧ classicalSolution φ z v 1 = -v := by
  have h := det_classicalMonodromy_sub_scalar_eq_zero_iff φ z (-1)
  rw [det_classicalMonodromy_sub_scalar] at h
  have he : (-1 : ℂ)^2-(-1)*classicalDiscriminant φ z+1 = classicalDiscriminant φ z+2 := by ring
  simpa only [he,add_eq_zero_iff_eq_neg,neg_one_smul] using h

/-- The two normalized classical boundary determinants give the same discriminant. -/
theorem classicalBoundaryDeterminants_compatible (φ : Curve (ℂ × ℂ)) (z : ℂ) :
    -(classicalMonodromy φ z - 1).det + 2 = classicalDiscriminant φ z ∧
      (classicalMonodromy φ z + 1).det - 2 = classicalDiscriminant φ z := by
  have h₁ := det_classicalMonodromy_sub_scalar φ z 1
  have h₂ := det_classicalMonodromy_sub_scalar φ z (-1)
  simp only [one_smul,one_pow,one_mul] at h₁
  simp only [neg_one_smul,sub_neg_eq_add,neg_one_sq,neg_mul,one_mul,sub_neg_eq_add] at h₂
  constructor
  · linear_combination -h₁
  · linear_combination h₂

end NLS.ZakharovShabat
