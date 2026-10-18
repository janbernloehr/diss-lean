import NLS.ZakharovShabat.SobolevWKBCharacteristicModels

/-! # Exact WKB endpoint characteristic formulas

Both Hamiltonian phases, both leading density integrals, and the inverse initial-basis determinant remain explicit.
-/

noncomputable section
open Set Complex NLS.Fourier
open scoped ContDiff
namespace NLS.ZakharovShabat
open BoundaryCondition

/-- The second endpoint uses the Hamiltonian phase of the signed swapped
potential at the reflected spectral parameter. -/
theorem nlsWKBSecondVector_one (a b : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1) (N : ℕ) (z : ℂ) :
    nlsWKBSecondVector a b N z 1 =
      exp (nlsHamiltonianPhase (-b) (-a) N (-z)) • nlsWKBSecondVector a b N z 0 := by
  have h := nlsWKBVector_one (-b) (-a) hb.neg ha.neg
    (by intro x; change -b (x+1) = -b x; rw [hpb x])
    (by intro x; change -a (x+1) = -a x; rw [hpa x]) N (-z)
  change nlsWKBVector (-b) (-a) N (-z) 1 =
    exp (nlsHamiltonianPhase (-b) (-a) N (-z)) • nlsWKBVector (-b) (-a) N (-z) 0 at h
  unfold nlsWKBSecondVector
  rw [h]
  rfl

/-- Exact endpoint formulas retain both phases, both sampled leading
terms, and the inverse initial-basis determinant. No symmetry of the two
Hamiltonian phases is assumed. -/
theorem nlsWKB_endpoint_characteristic_models_eq (a b : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1) (N : ℕ) (z : ℂ) :
    let p := nlsWKBInitialLower a b N z
    let q := nlsWKBInitialUpper a b N z
    let u := exp (nlsHamiltonianPhase a b N z)
    let v := exp (nlsHamiltonianPhase (-b) (-a) N (-z))
    let S := nlsWKBLeadingTerm a b N z 1
    let T := nlsWKBLeadingTerm (-b) (-a) N (-z) 1
    nlsWKBDiscriminantModel a b N z =
      (1-p*q)⁻¹*((1-p*q)*(u+v)+p*T+q*S) ∧
    nlsWKBAntiDiscriminantModel a b N z =
      (1-p*q)⁻¹*((p-q)*(u-v)-S-T) ∧
    ∀ θ : BoundaryCondition,
      nlsWKBSeparatedCharacteristicModel θ a b N z =
        (1-p*q)⁻¹*((1+p*q)*(v-u)+q*S-p*T+
          extensionSign θ*((p+q)*(u-v)-S+T))/(2*I) := by
  dsimp only
  have hfirst : nlsWKBVector a b N z 1 =
      exp (nlsHamiltonianPhase a b N z) • (1,nlsWKBInitialLower a b N z) := by
    rw [nlsWKBVector_one a b ha hb hpa hpb,nlsWKBVector_initial]
    rfl
  have hsecond : nlsWKBSecondVector a b N z 1 =
      exp (nlsHamiltonianPhase (-b) (-a) N (-z)) • (nlsWKBInitialUpper a b N z,1) := by
    rw [nlsWKBSecondVector_one a b ha hb hpa hpb,nlsWKBSecondVector_initial]
  simp only [nlsWKBDiscriminantModel,nlsWKBAntiDiscriminantModel,
    nlsWKBSeparatedCharacteristicModel,nlsWKBFirstColumnModel,nlsWKBSecondColumnModel,
    hfirst,hsecond,Prod.smul_fst,Prod.smul_snd,Prod.fst_sub,Prod.snd_sub,smul_eq_mul]
  refine ⟨by ring,by ring,?_⟩
  intro θ
  ring

end NLS.ZakharovShabat
