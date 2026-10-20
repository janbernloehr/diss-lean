import NLS.ZakharovShabat.NLSWKBTraceErrorDecomposition
import NLS.ZakharovShabat.NLSHamiltonianPhaseIncrement

/-! # The exact next-phase separated characteristic

The actual characteristic retains corrected diagonal and full off-diagonal remainders, exact leading integrals, and a scalar correction.
-/

noncomputable section
open Set Complex Matrix NLS.LinearVolterra
open scoped ContDiff
namespace NLS.ZakharovShabat
open BoundaryCondition

/-- The separated characteristic retains the signs of the two diagonal
remainders and the full off-diagonal remainders. -/
theorem classicalSeparatedCharacteristic_sub_wkb_model_exact
    (θ : BoundaryCondition) (a b : ℝ → ℂ) (ha : Continuous a) (hb : Continuous b)
    (N : ℕ) (z : ℂ)
    (hd : 1-nlsWKBInitialLower a b N z*nlsWKBInitialUpper a b N z ≠ 0) :
    let p := nlsWKBInitialLower a b N z
    let q := nlsWKBInitialUpper a b N z
    let η := extensionSign θ
    let E := nlsWKBFirstRemainder a b ha hb N z 1
    let F := nlsWKBSecondRemainder a b ha hb N z 1
    2*I*(1-p*q)*(classicalSeparatedCharacteristic θ
      (classicalPotentialOfFunctions a b ha hb) z-
      nlsWKBSeparatedCharacteristicModel θ a b N z) =
      (1-η*q)*E.1-(1-η*p)*F.2+(q-η)*E.2+(η-p)*F.1 := by
  dsimp only
  simp only [classicalSeparatedCharacteristic,classicalMonodromy,classicalFundamentalMatrix,
    Matrix.of_apply,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
  rw [classicalSolution_from_basis_left _ z _ _ hd ⟨1,by constructor <;> norm_num⟩,
    classicalSolution_from_basis_right _ z _ _ hd ⟨1,by constructor <;> norm_num⟩]
  simp only [nlsWKBSeparatedCharacteristicModel,nlsWKBFirstColumnModel,nlsWKBSecondColumnModel,
    nlsWKBFirstRemainder,nlsWKBSecondRemainder,nlsWKBVector_initial,nlsWKBSecondVector_initial,
    Prod.fst_sub,Prod.snd_sub,Prod.smul_fst,Prod.smul_snd,smul_eq_mul,Set.Icc.coe_one]
  field_simp [hd]
  ring

/-- The separated characteristic at the original Hamiltonian phase,
with the two leading integrals and all four exact remainders. -/
theorem classicalSeparatedCharacteristic_wkb_phase_exact
    (θ : BoundaryCondition) (a b : ℝ → ℂ) (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1) (N : ℕ) (z : ℂ)
    (hd : 1-nlsWKBInitialLower a b N z*nlsWKBInitialUpper a b N z ≠ 0) :
    let p := nlsWKBInitialLower a b N z
    let q := nlsWKBInitialUpper a b N z
    let η := extensionSign θ
    let E := nlsWKBFirstRemainder a b ha.continuous hb.continuous N z 1
    let F := nlsWKBSecondRemainder a b ha.continuous hb.continuous N z 1
    2*I*(1-p*q)*classicalSeparatedCharacteristic θ
      (classicalPotentialOfFunctions a b ha.continuous hb.continuous) z+
      2*(1+p*q-η*(p+q))*sinh (nlsHamiltonianPhase a b N z)-
      (q-η)*nlsWKBLeadingTerm a b N z 1-(η-p)*nlsWKBLeadingTerm (-b) (-a) N (-z) 1 =
      (1-η*q)*E.1-(1-η*p)*F.2+(q-η)*E.2+(η-p)*F.1 := by
  have he := classicalSeparatedCharacteristic_sub_wkb_model_exact θ a b ha.continuous hb.continuous N z hd
  have hm := (nlsWKB_endpoint_single_phase_models_eq a b ha hb hpa hpb N z hd).2.2 θ
  dsimp only at he hm ⊢
  rw [hm] at he
  field_simp [hd] at he
  linear_combination he

/-- The scalar error left by including the signed diagonal primitives
in the next hyperbolic sine phase. -/
def nlsHamiltonianSinhIncrementError (a b : ℝ → ℂ) (N : ℕ) (z : ℂ) : ℂ :=
  2*sinh (nlsHamiltonianPhase a b (N+1) z)-2*sinh (nlsHamiltonianPhase a b N z)+
    nlsWKBDiagonalPhasePrimitive a b N z 1-nlsWKBDiagonalPhasePrimitive (-b) (-a) N (-z) 1

/-- The separated next-phase correction preserves the small initial
factors multiplying the two diagonal primitives. -/
def nlsWKBNextSeparatedCorrectionError (θ : BoundaryCondition)
    (a b : ℝ → ℂ) (N : ℕ) (z : ℂ) : ℂ :=
  let p := nlsWKBInitialLower a b N z
  let q := nlsWKBInitialUpper a b N z
  let η := extensionSign θ
  (1+p*q-η*(p+q))*nlsHamiltonianSinhIncrementError a b N z+
    p*(η-q)*nlsWKBDiagonalPhasePrimitive a b N z 1+
    q*(p-η)*nlsWKBDiagonalPhasePrimitive (-b) (-a) N (-z) 1

/-- The actual separated characteristic at the next Hamiltonian phase
is expressed by corrected diagonals, off-diagonals, and a scalar correction. -/
theorem classicalSeparatedCharacteristic_next_wkb_phase_exact
    (θ : BoundaryCondition) (a b : ℝ → ℂ) (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1) (N : ℕ) (z : ℂ)
    (hd : 1-nlsWKBInitialLower a b N z*nlsWKBInitialUpper a b N z ≠ 0) :
    let p := nlsWKBInitialLower a b N z
    let q := nlsWKBInitialUpper a b N z
    let η := extensionSign θ
    let E := nlsWKBFirstRemainder a b ha.continuous hb.continuous N z 1
    let F := nlsWKBSecondRemainder a b ha.continuous hb.continuous N z 1
    2*I*(1-p*q)*classicalSeparatedCharacteristic θ
      (classicalPotentialOfFunctions a b ha.continuous hb.continuous) z+
      2*(1+p*q-η*(p+q))*sinh (nlsHamiltonianPhase a b (N+1) z)-
      (q-η)*nlsWKBLeadingTerm a b N z 1-(η-p)*nlsWKBLeadingTerm (-b) (-a) N (-z) 1 =
      (1-η*q)*(E.1-nlsWKBDiagonalPhasePrimitive a b N z 1)-
      (1-η*p)*(F.2-nlsWKBDiagonalPhasePrimitive (-b) (-a) N (-z) 1)+
      (q-η)*E.2+(η-p)*F.1+nlsWKBNextSeparatedCorrectionError θ a b N z := by
  have h := classicalSeparatedCharacteristic_wkb_phase_exact θ a b ha hb hpa hpb N z hd
  dsimp only at h ⊢
  dsimp only [nlsWKBNextSeparatedCorrectionError,nlsHamiltonianSinhIncrementError]
  linear_combination h

end NLS.ZakharovShabat
