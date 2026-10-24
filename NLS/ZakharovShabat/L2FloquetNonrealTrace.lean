import NLS.ZakharovShabat.L2FloquetNonrealBasis

/-! # The actual stable and unstable multipliers sum to the physical trace -/
noncomputable section
set_option autoImplicit false
open Matrix Module
namespace NLS.ZakharovShabat

/-- One nonzero eigenvector and reciprocal multipliers determine the trace
of a unimodular two-dimensional matrix. -/
theorem trace_eq_sum_of_reciprocal_eigenvalue (M : Matrix (Fin 2) (Fin 2) ℂ)
    (hM : M.det = 1) (μ ν : ℂ) (hprod : μ*ν = 1)
    (v : Fin 2 → ℂ) (hv0 : v ≠ 0) (hv : M *ᵥ v = μ • v) : M.trace = μ+ν := by
  have hd : (M-μ • 1).det = 0 := Matrix.exists_mulVec_eq_zero_iff.mp ⟨v,hv0,by
    simp only [Matrix.sub_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,hv,sub_self]⟩
  rw [det_sub_smul_one_eq_floquet_quadratic M hM] at hd
  have hμ : μ ≠ 0 := by intro h; simp [h] at hprod
  apply (mul_left_inj' hμ).mp
  linear_combination -hd-hprod

/-- At each nonreal parameter the actual ordered Floquet basis also satisfies
the trace identity needed for the uniform projection estimates. -/
theorem l2Monodromy_nonreal_exists_stable_unstable_basis_with_trace (u : IntervalPairL2)
    (hu : IsClassicalRealType (intervalL2Representative u)) (z : ℂ) (hz : z.im ≠ 0) :
    ∃ (μ ν : ℂ) (b : Basis (Fin 2) ℂ (Fin 2 → ℂ)),
      (l2Monodromy u z).trace = μ+ν ∧ μ*ν = 1 ∧
      0 < ‖μ‖ ∧ ‖μ‖ < 1 ∧ 1 < ‖ν‖ ∧
      l2Monodromy u z *ᵥ b 0 = μ • b 0 ∧ l2Monodromy u z *ᵥ b 1 = ν • b 1 := by
  obtain ⟨μ,ν,b,hprod,hpos,hstable,hunstable,hμ,hν⟩ :=
    l2Monodromy_nonreal_exists_stable_unstable_eigenbasis u hu z hz
  exact ⟨μ,ν,b,trace_eq_sum_of_reciprocal_eigenvalue _ (det_l2Monodromy u z)
    μ ν hprod (b 0) (b.ne_zero 0) hμ,hprod,hpos,hstable,hunstable,hμ,hν⟩

end NLS.ZakharovShabat
