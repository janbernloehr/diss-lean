import NLS.ZakharovShabat.SourceHamiltonianHessian
import NLS.SequenceSpaces.HilbertScalarConcavity

/-! # The analytic action Hamiltonian, its gradient, and strict concavity

The cubic-moment extension has the actual renormalized frequency as its
analytic ℓ² gradient. Its Hessian at zero is minus twice Hilbert bilinear
duality, and continuity gives the quantitative local concavity estimate.
The physical normalization used here is proved on finite-gap sources.
-/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
local instance : Fact ((1:ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩
local instance : (4:ℝ≥0∞).HolderTriple 4 2 := (ENNReal.holderTriple_iff _ _ _).mpr (by
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_add])

/-- Construct the actual action Hamiltonian and frequency gradient, including
all real sources, nonnegative-domain sign, the Hessian, and strict concavity. -/
theorem exists_sourceHamiltonian_action_extension_with_concavity :
    ∃ W : Set (CoeffPair 4), ∃ A : SourcePrimitivePowerAtlas (by simp) (by norm_num) W,
    ∃ W₀ B X : Set (CoeffPair 4), ∃ t : (k : ℤ) → CoeffPair 4 → DeletedCoeff 4 k,
    ∃ _D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B X t,
    ∃ Y P : Set (CoeffPair 4), ∃ u : (k : ℤ) → CoeffPair 4 → DeletedCoeff 4 k,
    ∃ C : SourceAbelianMomentAtlas (by simp) (by norm_num) Y u,
      SourcePsiSquaredGapComplexExtension (by simp) (by norm_num) P u ∧ IsOpen P ∧ realTypeSourceLocus 4 ⊆ P ∧
    ∃ V : Set (Coeff 2), ∃ H : Coeff 2 → ℂ, IsOpen V ∧ (0:Coeff 2) ∈ V ∧
      (∀ φ : realTypeSourceSubmodule 4, sourceActionSequence (q := 2) (by simp) (by norm_num) t φ.val ∈ V) ∧
      (∀ b : RealCoeff 1, (∀ n, 0 ≤ b n) →
        Coeff.exponentInclusion (by norm_num : (1:ℝ≥0∞) ≤ 2) (RealCoeff.complexCLM 1 b) ∈ V) ∧
      AnalyticOnNhd ℂ H V ∧
      (∀ φ : realTypeSourceSubmodule 4,
        H (sourceActionSequence (q := 2) (by simp) (by norm_num) t φ.val) = A.renormalizedHamiltonian φ.val) ∧
      (∀ b ∈ V, b ∈ Coeff.nonnegativeLocus 2 → (H b).re ≤ 0 ∧ (H b).im = 0 ∧ (H b = 0 ↔ b = 0)) ∧
      AnalyticOnNhd ℂ (Coeff.scalarGradient H) V ∧
      (∀ φ : realTypeSourceSubmodule 4, ∀ n,
        Coeff.scalarGradient H (sourceActionSequence (q := 2) (by simp) (by norm_num) t φ.val) n =
          C.renormalizedFrequency n φ.val) ∧
      fderiv ℂ (Coeff.scalarGradient H) 0 = (-2:ℂ) • ContinuousLinearMap.id ℂ (Coeff 2) ∧
      (∀ v w : Coeff 2, fderiv ℂ (fderiv ℂ H) 0 v w = -2 * Coeff.dualPairing v w) ∧
      ∃ r : ℝ, 0 < r ∧ ball (0:Coeff 2) r ⊆ V ∧
        ∀ b ∈ ball (0:Coeff 2) r, ∀ J : RealCoeff 2,
          (fderiv ℂ (fderiv ℂ H) b (RealCoeff.complexCLM 2 J) (RealCoeff.complexCLM 2 J)).re ≤ -‖J‖^2 := by
  obtain ⟨W,_,_,⟨A⟩⟩ := exists_sourcePrimitivePowerAtlas (p := 4) (by simp) (by norm_num)
  obtain ⟨W₀,B,X,t,D,V,H,hV,hcenter,hcone,_,_,hH,hrec,hsign,_⟩ := A.exists_hamiltonian_action_extension
  obtain ⟨Y,P,_,_,hP,hrealP,u,hs,⟨C⟩⟩ :=
    exists_sourceAbelianMoment_squaredGapAtlas (p := 4) (by simp) (by norm_num)
  have h0 : (0:Coeff 2) ∈ V := by
    simpa only [ZeroMemClass.coe_zero,D.actionSequence_zero] using hcenter 0
  obtain ⟨hd,hess⟩ := sourceHamiltonian_gradient_derivative_and_hessian_zero A D C hs hP hrealP H V hH hcenter hrec
  refine ⟨W,A,W₀,B,X,t,D,Y,P,u,C,hs,hP,hrealP,V,H,hV,h0,hcenter,hcone,hH,hrec,hsign,
    Coeff.analyticOnNhd_scalarGradient H hH,?_,hd,hess,?_⟩
  · intro φ n
    rw [Coeff.scalarGradient_apply]
    exact sourceHamiltonian_fderiv_real A D C hs hP hrealP H V hH hcenter hrec φ n
  · exact Coeff.exists_ball_hessian_le_negative_norm_sq H V hV h0 hH hd

end NLS.ZakharovShabat
