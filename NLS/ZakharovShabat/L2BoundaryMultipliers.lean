import NLS.ZakharovShabat.L2FundamentalInitialValue
import NLS.ZakharovShabat.L2Discriminant
import NLS.ZakharovShabat.FloquetQuadratic

/-! # Endpoint multipliers of the actual physical L2 initial-value problem

The determinant-one monodromy propagates every initial vector. Its
characteristic polynomial is exactly the nonzero endpoint-multiplier
condition, including the periodic and antiperiodic cases.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Matrix
open NLS.LinearVolterra
namespace NLS.ZakharovShabat

theorem l2FundamentalMatrix_mulVec (u : IntervalPairL2) (z : ℂ) (v : Fin 2 → ℂ)
    (t : Icc (0 : ℝ) 1) :
    l2FundamentalMatrix u z t *ᵥ v =
      ![(l2SolutionCurve u z (v 0,v 1) t).1,(l2SolutionCurve u z (v 0,v 1) t).2] := by
  rw [l2SolutionCurve_linearCombination]
  ext i
  fin_cases i <;> simp [l2FundamentalMatrix,Matrix.mulVec,Matrix.vecHead,Matrix.vecTail,smul_eq_mul] <;> ring

theorem l2Monodromy_kernel_iff (u : IntervalPairL2) (z σ : ℂ) (v : Fin 2 → ℂ) :
    (l2Monodromy u z-σ • 1) *ᵥ v = 0 ↔
      l2SolutionCurve u z (v 0,v 1) ⟨1,by constructor <;> norm_num⟩ = σ • (v 0,v 1) := by
  rw [Matrix.sub_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,sub_eq_zero]
  rw [l2Monodromy,l2FundamentalMatrix_mulVec]
  constructor
  · intro h
    exact Prod.ext (congrFun h 0) (congrFun h 1)
  · intro h
    ext i
    fin_cases i
    · exact congrArg Prod.fst h
    · exact congrArg Prod.snd h

theorem det_l2Monodromy_sub_scalar_eq_zero_iff (u : IntervalPairL2) (z σ : ℂ) :
    (l2Monodromy u z-σ • 1).det = 0 ↔
      ∃ v : ℂ × ℂ, v ≠ 0 ∧ l2SolutionCurve u z v ⟨1,by constructor <;> norm_num⟩ = σ • v := by
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  constructor
  · rintro ⟨v,hv,he⟩
    refine ⟨(v 0,v 1),?_,(l2Monodromy_kernel_iff u z σ v).mp he⟩
    intro h
    apply hv
    ext i
    fin_cases i
    · exact congrArg Prod.fst h
    · exact congrArg Prod.snd h
  · rintro ⟨v,hv,he⟩
    refine ⟨![v.1,v.2],?_,(l2Monodromy_kernel_iff u z σ _).mpr he⟩
    intro h
    apply hv
    exact Prod.ext (congrFun h 0) (congrFun h 1)

/-- The multiplier criterion retains the exact full trace and determinant
one normalization, with no reality restriction on potential or energy. -/
theorem l2Discriminant_multiplier_iff (u : IntervalPairL2) (z σ : ℂ) :
    σ^2-l2Discriminant u z*σ+1 = 0 ↔
      ∃ v : ℂ × ℂ, v ≠ 0 ∧ l2SolutionCurve u z v ⟨1,by constructor <;> norm_num⟩ = σ • v := by
  rw [← det_l2Monodromy_sub_scalar_eq_zero_iff,
    det_sub_smul_one_eq_floquet_quadratic _ (det_l2Monodromy u z)]
  rfl

end NLS.ZakharovShabat
