import NLS.MKdV.L2QuasiHillDiscriminant
import NLS.ZakharovShabat.L2BoundaryMultipliers

/-! # Actual rough Hill endpoint multipliers and characteristic roots

The fixed invertible state map preserves every complex multiplier.
The discriminant's exact unimodular quadratic therefore characterizes
nonzero rough initial-value states, including at zero energy.
-/
noncomputable section
set_option autoImplicit false
open Set Complex
open NLS.LinearVolterra NLS.ZakharovShabat
namespace NLS.MKdV

theorem exists_l2QuasiHill_multiplier_iff (u : IntervalL2) (μ σ : ℂ) :
    (∃ v : ℂ × ℂ, v ≠ 0 ∧ l2QuasiHillSolution u μ v ⟨1,by constructor <;> norm_num⟩ = σ • v) ↔
      ∃ w : ℂ × ℂ, w ≠ 0 ∧ l2SolutionCurve (l2QuasiHillPotential u μ) (quasiHillAffineFrequency μ)
        w ⟨1,by constructor <;> norm_num⟩ = σ • w := by
  have hinj : Function.Injective quasiHillFixedState := miuraStateMap_injective 0 1 one_ne_zero
  constructor
  · rintro ⟨v,hv,he⟩
    refine ⟨quasiHillFixedStateInv v,?_,?_⟩
    · intro hz
      apply hv
      rw [← quasiHillFixedState_right_inv v,hz,map_zero]
    · apply hinj
      rw [map_smul,quasiHillFixedState_right_inv]
      exact (l2QuasiHillSolution_apply u μ v _).symm.trans he
  · rintro ⟨w,hw,he⟩
    refine ⟨quasiHillFixedState w,?_,?_⟩
    · intro hz
      exact hw (hinj (hz.trans (map_zero _).symm))
    · rw [l2QuasiHillSolution_apply,quasiHillFixedState_left_inv,he,map_smul]

theorem l2QuasiHillDiscriminant_multiplier_iff (u : IntervalL2) (μ σ : ℂ) :
    σ^2-l2QuasiHillDiscriminant u μ*σ+1 = 0 ↔
      ∃ v : ℂ × ℂ, v ≠ 0 ∧ l2QuasiHillSolution u μ v ⟨1,by constructor <;> norm_num⟩ = σ • v := by
  rw [l2QuasiHillDiscriminant_eq_affine_AKNS,l2Discriminant_multiplier_iff,
    exists_l2QuasiHill_multiplier_iff]

theorem l2QuasiHillDiscriminant_eq_two_iff (u : IntervalL2) (μ : ℂ) :
    l2QuasiHillDiscriminant u μ = 2 ↔
      ∃ v : ℂ × ℂ, v ≠ 0 ∧ l2QuasiHillSolution u μ v ⟨1,by constructor <;> norm_num⟩ = v := by
  have h := l2QuasiHillDiscriminant_multiplier_iff u μ 1
  have hp : (1 : ℂ)^2-l2QuasiHillDiscriminant u μ*1+1 = 2-l2QuasiHillDiscriminant u μ := by ring
  rw [hp,sub_eq_zero,eq_comm] at h
  simpa only [one_smul] using h

theorem l2QuasiHillDiscriminant_eq_neg_two_iff (u : IntervalL2) (μ : ℂ) :
    l2QuasiHillDiscriminant u μ = -2 ↔
      ∃ v : ℂ × ℂ, v ≠ 0 ∧ l2QuasiHillSolution u μ v ⟨1,by constructor <;> norm_num⟩ = -v := by
  have h := l2QuasiHillDiscriminant_multiplier_iff u μ (-1)
  have hp : (-1 : ℂ)^2-l2QuasiHillDiscriminant u μ*(-1)+1 = l2QuasiHillDiscriminant u μ+2 := by ring
  rw [hp,add_eq_zero_iff_eq_neg] at h
  simpa only [neg_one_smul] using h

end NLS.MKdV
