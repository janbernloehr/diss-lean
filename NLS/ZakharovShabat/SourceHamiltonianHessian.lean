import NLS.ZakharovShabat.SourceHamiltonianRealGradient
import NLS.ZakharovShabat.SourceFrequencyDerivativeOrigin
import NLS.SequenceSpaces.HilbertScalarGradient

/-! # The actual action Hamiltonian's Hessian at zero

The analytic Hilbert gradient recovers every actual frequency. The already
proved frequency derivative at zero therefore computes the full Hessian,
including mixed and infinite-support Hilbert directions.
-/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
local instance : Fact ((1:ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩
local instance : (4:ℝ≥0∞).HolderTriple 4 2 := (ENNReal.holderTriple_iff _ _ _).mpr (by
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_add])
variable {W W₀ B X Y P : Set (CoeffPair 4)}
variable {t u : (k : ℤ) → CoeffPair 4 → DeletedCoeff 4 k}

/-- The actual analytic gradient has derivative minus twice the identity;
the scalar Hessian is minus twice the full bilinear Hilbert pairing. -/
theorem sourceHamiltonian_gradient_derivative_and_hessian_zero
    (A : SourcePrimitivePowerAtlas (by simp) (by norm_num) W)
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B X t)
    (C : SourceAbelianMomentAtlas (by simp) (by norm_num) Y u)
    (hs : SourcePsiSquaredGapComplexExtension (by simp) (by norm_num) P u)
    (hP : IsOpen P) (hrealP : realTypeSourceLocus 4 ⊆ P)
    (H : Coeff 2 → ℂ) (V : Set (Coeff 2)) (hH : AnalyticOnNhd ℂ H V)
    (hcenter : ∀ ψ : realTypeSourceSubmodule 4,
      sourceActionSequence (q := 2) (by simp) (by norm_num) t ψ.val ∈ V)
    (hrec : ∀ ψ : realTypeSourceSubmodule 4,
      H (sourceActionSequence (q := 2) (by simp) (by norm_num) t ψ.val) = A.renormalizedHamiltonian ψ.val) :
    fderiv ℂ (Coeff.scalarGradient H) 0 = (-2:ℂ) • ContinuousLinearMap.id ℂ (Coeff 2) ∧
      ∀ v w : Coeff 2, fderiv ℂ (fderiv ℂ H) 0 v w = -2 * Coeff.dualPairing v w := by
  have h0 : (0:Coeff 2) ∈ V := by
    simpa only [ZeroMemClass.coe_zero,D.actionSequence_zero] using hcenter 0
  have hG := Coeff.analyticOnNhd_scalarGradient H hH
  have hGrec (ψ : realTypeSourceSubmodule 4) (n : ℤ) :
      Coeff.scalarGradient H (sourceActionSequence (q := 2) (by simp) (by norm_num) t ψ.val) n =
        C.renormalizedFrequency n ψ.val := by
    rw [Coeff.scalarGradient_apply]
    exact sourceHamiltonian_fderiv_real A D C hs hP hrealP H V hH hcenter hrec ψ n
  have hG0 : Coeff.scalarGradient H 0 = 0 := by
    ext n
    change Coeff.scalarGradient H 0 n = 0
    simpa only [ZeroMemClass.coe_zero,D.actionSequence_zero,C.renormalizedFrequency_eq_zero_at_zero] using hGrec 0 n
  have hd := sourceFrequency_fderiv_zero C hs.toSourcePsiIsolatingComplexExtension D
    (by norm_num) (Coeff.scalarGradient H) (hG 0 h0).differentiableAt hG0 hGrec
  refine ⟨hd,?_⟩
  intro v w
  rw [Coeff.hessian_eq_dualPairing_gradient_derivative H 0 (hH 0 h0),hd]
  simp only [smul_apply,ContinuousLinearMap.id_apply,map_smul,smul_eq_mul]

end NLS.ZakharovShabat
