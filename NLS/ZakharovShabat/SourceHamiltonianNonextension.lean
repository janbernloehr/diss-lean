import NLS.ZakharovShabat.SourceHamiltonianActionConcavity
import NLS.ZakharovShabat.SourceSobolevHamiltonianIdentification
import NLS.SequenceSpaces.HilbertHamiltonianNonextension

/-! # Optimal action exponent for the renormalized Hamiltonian

The consequence following Theorem 0.2 holds already with continuity in place of C¹:
no extension agreeing on nonnegative summable actions is continuous at zero on the
positive cone of any finite ℓ^q with q > 2. The Hamiltonian here is the actual source
Hamiltonian, with its physical H¹ identification retained.
-/
noncomputable section
open Set Metric Filter Topology Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
local instance : Fact ((1:ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩
local instance : (4:ℝ≥0∞).HolderTriple 4 2 := (ENNReal.holderTriple_iff _ _ _).mpr (by
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_add])

/-- The actual analytic Hamiltonian has optimal finite action exponent two, even
for continuous extensions relative to the nonnegative cone. -/
theorem exists_sourceHamiltonian_no_continuous_extension :
    ∃ W : Set (CoeffPair 4), ∃ A : SourcePrimitivePowerAtlas (by simp) (by norm_num) W,
    ∃ W₀ B X : Set (CoeffPair 4), ∃ t : (k : ℤ) → CoeffPair 4 → DeletedCoeff 4 k,
    ∃ _D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B X t,
    ∃ V : Set (Coeff 2), ∃ H : Coeff 2 → ℂ,
      IsOpen V ∧ (0:Coeff 2) ∈ V ∧ AnalyticOnNhd ℂ H V ∧ H 0 = 0 ∧
      (∀ b : RealCoeff 1, (∀ n, 0 ≤ b n) →
        Coeff.exponentInclusion (by norm_num : (1:ℝ≥0∞) ≤ 2) (RealCoeff.complexCLM 1 b) ∈ V) ∧
      (∀ φ : realTypeSourceSubmodule 4,
        H (sourceActionSequence (q := 2) (by simp) (by norm_num) t φ.val) = A.renormalizedHamiltonian φ.val) ∧
      (∀ a : realTypeSobolevSourceLocus,
        H (sourceActionSequence (q := 2) (by simp) (by norm_num) t (sobolevSourceFL4 a.val)) =
          sourceSobolevPhysicalCorrection a.val) ∧
      (∃ r : ℝ, 0 < r ∧ ∀ b ∈ Coeff.nonnegativeLocus 2,
        ‖b‖ < r → (H b).re ≤ -‖b‖^2/2) ∧
      ∀ (q : ℝ≥0∞) [Fact (1 ≤ q)] (_hq : q ≠ ⊤) (h2q : 2 < q)
        (G : Coeff q → ℂ) (U : Set (Coeff q)), U ∈ 𝓝 (0:Coeff q) →
        (∀ a : Coeff 1, a ∈ Coeff.nonnegativeLocus 1 →
          Coeff.exponentInclusion (le_trans (by norm_num : (1:ℝ≥0∞) ≤ 2) h2q.le) a ∈ U →
          G (Coeff.exponentInclusion (le_trans (by norm_num : (1:ℝ≥0∞) ≤ 2) h2q.le) a) =
            H (Coeff.exponentInclusion (by norm_num : (1:ℝ≥0∞) ≤ 2) a)) →
        ¬ ContinuousWithinAt G (Coeff.nonnegativeLocus q) 0 ∧
          ¬ ContDiffWithinAt ℝ 1 G (Coeff.nonnegativeLocus q) 0 := by
  obtain ⟨W,A,W₀,B,X,t,D,Y,P,u,C,hs,hP,hrealP,V,H,hV,h0,hcenter,hcone,hH,hrec,
    hsign,hG,hGrec,hd,hess,r,hr,hball,he⟩ :=
    exists_sourceHamiltonian_action_extension_with_concavity
  have hzero : H 0 = 0 := (hsign 0 h0 (Coeff.zero_mem_nonnegativeLocus 2)).2.2.mpr rfl
  have hG0 : Coeff.scalarGradient H 0 = 0 := by
    ext n
    change Coeff.scalarGradient H 0 n = 0
    simpa only [ZeroMemClass.coe_zero,D.actionSequence_zero,
      C.renormalizedFrequency_eq_zero_at_zero] using hGrec 0 n
  have hb : ∀ b ∈ Coeff.nonnegativeLocus 2, ‖b‖ < r → (H b).re ≤ -‖b‖^2/2 := by
    intro b hpos hnorm
    let J := Coeff.reCLM 2 b
    have hJ : RealCoeff.complexCLM 2 J = b :=
      RealCoeff.complexCLM_reCLM 2 b (fun n => (hpos n).1)
    have hn : ‖J‖ = ‖b‖ := by rw [← Coeff.norm_real_hilbert_inclusion J,hJ]
    simpa only [hJ,hn] using Coeff.real_value_le_negative_half_norm_sq H V hH hzero hG0
      r hball he J (by simpa only [hn] using hnorm)
  refine ⟨W,A,W₀,B,X,t,D,V,H,hV,h0,hH,hzero,hcone,hrec,?_,⟨r,hr,hb⟩,?_⟩
  · intro a
    exact (hrec ⟨sobolevSourceFL4 a.val,(realSobolevSourceFL4 a).property⟩).trans
      (A.renormalizedHamiltonian_eq_sobolevPhysicalCorrection a)
  · intro q _ hq h2q G U hU hagree
    have hnc := Coeff.not_continuousWithinAt_extension_of_quadratic_bound hq h2q H hzero r hr hb
      G U hU (fun a ha hU _ => hagree a ha hU)
    exact ⟨hnc,fun hC => hnc hC.continuousWithinAt⟩

end NLS.ZakharovShabat
