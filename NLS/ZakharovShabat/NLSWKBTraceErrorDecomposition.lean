import NLS.ZakharovShabat.NLSWKBAntiErrorDecomposition
import NLS.ZakharovShabat.NLSWKBSinglePhaseModels

/-! # Exact WKB trace errors

The actual discriminant error retains its diagonal remainders and the small factors on its off-diagonal remainders.
-/

noncomputable section
open Set Complex Matrix NLS.LinearVolterra
open scoped ContDiff
namespace NLS.ZakharovShabat

/-- The trace error retains both diagonal remainders; its off-diagonal
remainders carry the small initial-coordinate factors. -/
theorem classicalDiscriminant_sub_wkb_model_exact
    (a b : ℝ → ℂ) (ha : Continuous a) (hb : Continuous b) (N : ℕ) (z : ℂ)
    (hd : 1-nlsWKBInitialLower a b N z*nlsWKBInitialUpper a b N z ≠ 0) :
    let p := nlsWKBInitialLower a b N z
    let q := nlsWKBInitialUpper a b N z
    let E := nlsWKBFirstRemainder a b ha hb N z 1
    let F := nlsWKBSecondRemainder a b ha hb N z 1
    (1-p*q)*(classicalDiscriminant (classicalPotentialOfFunctions a b ha hb) z-
      nlsWKBDiscriminantModel a b N z) = p*F.1+q*E.2-E.1-F.2 := by
  dsimp only
  simp only [classicalDiscriminant,classicalMonodromy,classicalFundamentalMatrix,
    Matrix.trace_fin_two,Matrix.of_apply,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
  rw [classicalSolution_from_basis_left _ z _ _ hd ⟨1,by constructor <;> norm_num⟩,
    classicalSolution_from_basis_right _ z _ _ hd ⟨1,by constructor <;> norm_num⟩]
  simp only [nlsWKBDiscriminantModel,nlsWKBFirstColumnModel,nlsWKBSecondColumnModel,
    nlsWKBFirstRemainder,nlsWKBSecondRemainder,nlsWKBVector_initial,nlsWKBSecondVector_initial,
    Prod.fst_sub,Prod.snd_sub,Prod.smul_fst,Prod.smul_snd,smul_eq_mul,Set.Icc.coe_one]
  field_simp [hd]
  ring

/-- The actual trace is the single Hamiltonian phase plus an exact
componentwise error. No diagonal cancellation is assumed. -/
theorem classicalDiscriminant_sub_wkb_phase_exact
    (a b : ℝ → ℂ) (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1) (N : ℕ) (z : ℂ)
    (hd : 1-nlsWKBInitialLower a b N z*nlsWKBInitialUpper a b N z ≠ 0) :
    let p := nlsWKBInitialLower a b N z
    let q := nlsWKBInitialUpper a b N z
    let E := nlsWKBFirstRemainder a b ha.continuous hb.continuous N z 1
    let F := nlsWKBSecondRemainder a b ha.continuous hb.continuous N z 1
    let S := nlsWKBLeadingTerm a b N z 1
    let T := nlsWKBLeadingTerm (-b) (-a) N (-z) 1
    (1-p*q)*(classicalDiscriminant (classicalPotentialOfFunctions a b ha.continuous hb.continuous) z-
      2*cos (I*nlsHamiltonianPhase a b N z)) = p*(T+F.1)+q*(S+E.2)-E.1-F.2 := by
  have he := classicalDiscriminant_sub_wkb_model_exact a b ha.continuous hb.continuous N z hd
  have hm := (nlsWKB_endpoint_single_phase_models_eq a b ha hb hpa hpb N z hd).1
  dsimp only at he hm ⊢
  rw [hm] at he
  field_simp [hd] at he ⊢
  linear_combination he

end NLS.ZakharovShabat
