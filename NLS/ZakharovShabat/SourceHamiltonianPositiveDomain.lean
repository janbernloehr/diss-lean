import NLS.ZakharovShabat.SourceHamiltonianActionConcavity
import NLS.SequenceSpaces.NonnegativeActionDensity

/-! # The open dense positive domain in the remark following Theorem 0.2

The actual analytic Hamiltonian retains all source, gradient, sign and concavity
properties. Its domain restricted to the positive Hilbert cone is open and dense.
-/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
local instance : Fact ((1:ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩
local instance : (4:ℝ≥0∞).HolderTriple 4 2 := (ENNReal.holderTriple_iff _ _ _).mpr (by
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_add])

/-- The same actual Hamiltonian has an open dense positive action domain. -/
theorem exists_sourceHamiltonian_open_dense_positive_domain :
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
      IsOpen {b : Coeff.nonnegativeLocus 2 | b.val ∈ V} ∧
      Dense {b : Coeff.nonnegativeLocus 2 | b.val ∈ V} ∧
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
  obtain ⟨W,A,W₀,B,X,t,D,Y,P,u,C,hs,hP,hrealP,V,H,hV,h0,hcenter,hcone,hH,hrec,
    hsign,hG,hGrec,hd,hess,hball⟩ := exists_sourceHamiltonian_action_extension_with_concavity
  obtain ⟨hopen,hdense⟩ := Coeff.isOpen_dense_nonnegative_domain (by simp) V hV hcone
  exact ⟨W,A,W₀,B,X,t,D,Y,P,u,C,hs,hP,hrealP,V,H,hV,h0,hcenter,hcone,hopen,hdense,
    hH,hrec,hsign,hG,hGrec,hd,hess,hball⟩

end NLS.ZakharovShabat
