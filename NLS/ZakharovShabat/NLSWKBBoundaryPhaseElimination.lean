import NLS.ZakharovShabat.NLSWKBSinglePhaseModels

/-! # Exact elimination of the boundary WKB phase

Combining the separated and anti-discriminant models eliminates the phase. The leading integrals and initial-coordinate factors remain explicit.
-/

noncomputable section
open Set Complex
open scoped ContDiff
namespace NLS.ZakharovShabat
open BoundaryCondition

/-- Small WKB initial coordinates keep the separated phase coefficient
uniformly invertible for either boundary condition. -/
theorem norm_inv_wkb_boundary_phase_factor_le_four (θ : BoundaryCondition) (p q : ℂ)
    (hp : ‖p‖ ≤ 1/2) (hq : ‖q‖ ≤ 1/2) :
    1+p*q-extensionSign θ*(p+q) ≠ 0 ∧
      ‖(1+p*q-extensionSign θ*(p+q))⁻¹‖ ≤ 4 := by
  have hη : ‖extensionSign θ‖ = 1 := by cases θ <;> norm_num [extensionSign]
  have hp' : ‖extensionSign θ*p‖ ≤ 1/2 := by simpa only [norm_mul,hη,one_mul] using hp
  have hq' : ‖extensionSign θ*q‖ ≤ 1/2 := by simpa only [norm_mul,hη,one_mul] using hq
  obtain ⟨hp0,hpi⟩ := norm_inv_one_sub_mul_le_two (extensionSign θ) p hp'
  obtain ⟨hq0,hqi⟩ := norm_inv_one_sub_mul_le_two (extensionSign θ) q hq'
  have he : 1+p*q-extensionSign θ*(p+q) = (1-extensionSign θ*p)*(1-extensionSign θ*q) := by
    cases θ <;> simp only [extensionSign] <;> ring
  rw [he]
  refine ⟨mul_ne_zero hp0 hq0,?_⟩
  rw [mul_inv,norm_mul]
  exact (mul_le_mul hpi hqi (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)

/-- Combining the actual WKB characteristic models eliminates the
Hamiltonian phase exactly. The remaining terms are the two original
density samples and the separated characteristic error. -/
theorem nlsWKB_anti_boundary_phase_elimination (a b : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1) (N : ℕ) (z : ℂ)
    (hd : 1-nlsWKBInitialLower a b N z*nlsWKBInitialUpper a b N z ≠ 0)
    (θ : BoundaryCondition) :
    let p := nlsWKBInitialLower a b N z
    let q := nlsWKBInitialUpper a b N z
    let η := extensionSign θ
    let d := 1-p*q
    let A := 1+p*q-η*(p+q)
    let S := nlsWKBLeadingTerm a b N z 1
    let T := nlsWKBLeadingTerm (-b) (-a) N (-z) 1
    A*d*nlsWKBAntiDiscriminantModel a b N z+(1-η*q)^2*S+(1-η*p)^2*T =
      -2*I*(p-q)*d*nlsWKBSeparatedCharacteristicModel θ a b N z := by
  obtain ⟨_,hA,hS⟩ := nlsWKB_endpoint_single_phase_models_eq a b ha hb hpa hpb N z hd
  dsimp only at hA hS ⊢
  rw [hA,hS θ]
  field_simp
  cases θ <;> simp only [extensionSign] <;> ring

end NLS.ZakharovShabat
