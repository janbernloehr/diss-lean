import NLS.ZakharovShabat.NLSHamiltonianPhaseReflection
import NLS.ZakharovShabat.SobolevWKBEndpointFormulas

/-! # Endpoint characteristic models with one phase

Exact formulas express the trace, anti-discriminant, and separated models using one Hamiltonian phase and the two actual leading integrals.
-/

noncomputable section
open Set Complex
open scoped ContDiff
namespace NLS.ZakharovShabat
open BoundaryCondition

/-- The exact WKB endpoint models use a single original Hamiltonian
phase. The trace correction and both leading density integrals remain
explicit, with the exact initial-basis determinant. -/
theorem nlsWKB_endpoint_single_phase_models_eq (a b : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1) (N : ℕ) (z : ℂ)
    (hd : 1-nlsWKBInitialLower a b N z*nlsWKBInitialUpper a b N z ≠ 0) :
    let p := nlsWKBInitialLower a b N z
    let q := nlsWKBInitialUpper a b N z
    let σ := nlsHamiltonianPhase a b N z
    let S := nlsWKBLeadingTerm a b N z 1
    let T := nlsWKBLeadingTerm (-b) (-a) N (-z) 1
    nlsWKBDiscriminantModel a b N z = 2*cos (I*σ)+(p*T+q*S)/(1-p*q) ∧
    nlsWKBAntiDiscriminantModel a b N z = (2*(p-q)*sinh σ-S-T)/(1-p*q) ∧
    ∀ θ : BoundaryCondition,
      nlsWKBSeparatedCharacteristicModel θ a b N z =
        (-2*(1+ p*q-extensionSign θ*(p+q))*sinh σ+
          (q-extensionSign θ)*S+(extensionSign θ-p)*T)/(2*I*(1-p*q)) := by
  obtain ⟨hD,hA,hS⟩ := nlsWKB_endpoint_characteristic_models_eq a b ha hb hpa hpb N z
  dsimp only at hD hA hS ⊢
  rw [nlsHamiltonianPhase_signedSwap a b ha hb hpa hpb] at hD hA hS
  have hplus : exp (nlsHamiltonianPhase a b N z)+exp (-nlsHamiltonianPhase a b N z) =
      2*cos (I*nlsHamiltonianPhase a b N z) := by
    rw [mul_comm I,cos_mul_I,two_cosh]
  have hminus : exp (nlsHamiltonianPhase a b N z)-exp (-nlsHamiltonianPhase a b N z) =
      2*sinh (nlsHamiltonianPhase a b N z) := by rw [two_sinh]
  refine ⟨?_,?_,?_⟩
  · rw [hD,hplus]
    field_simp
    ring
  · rw [hA,hminus]
    ring
  · intro θ
    rw [hS θ]
    rw [show exp (-nlsHamiltonianPhase a b N z)-exp (nlsHamiltonianPhase a b N z) =
      -(exp (nlsHamiltonianPhase a b N z)-exp (-nlsHamiltonianPhase a b N z)) by ring,hminus]
    field_simp
    ring

end NLS.ZakharovShabat
