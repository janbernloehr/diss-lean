import NLS.ZakharovShabat.SourceHamiltonianLocalActionDescent
import NLS.ZakharovShabat.SourceRealActionLifting

/-! # Hamiltonian action balls with real representatives

Each local factor recovers the Hamiltonian at every real source with
its actions in the ball. Nonnegative actions in the ball have real lifts.
-/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat.SourcePrimitivePowerAtlas
local instance : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩
local instance : (4 : ℝ≥0∞).HolderTriple 4 2 := (ENNReal.holderTriple_iff _ _ _).mpr (by
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_add])
variable {W : Set (CoeffPair 4)}
variable (A : SourcePrimitivePowerAtlas (by simp) (by norm_num) W)

/-- Actual analytic action balls, with complex and real source realization
and recovery independent of the real representative or inverse chart. -/
theorem exists_hamiltonian_realActionBalls :
    ∃ W₀ B X : Set (CoeffPair 4), ∃ t : (n : ℤ) → CoeffPair 4 → DeletedCoeff 4 n,
      ∃ _D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B X t,
        ∀ φ : realTypeSourceSubmodule 4, ∃ R : ℝ, 0 < R ∧
          (∀ b ∈ ball (sourceActionSequence (q := 2) (by simp) (by norm_num) t φ.val) R,
            ∃ ψ ∈ X, sourceActionSequence (q := 2) (by simp) (by norm_num) t ψ = b) ∧
          (∀ b ∈ ball (sourceActionSequence (q := 2) (by simp) (by norm_num) t φ.val) R,
            b ∈ Coeff.nonnegativeLocus 2 → ∃ ψ : realTypeSourceSubmodule 4,
              sourceActionSequence (q := 2) (by simp) (by norm_num) t ψ.val = b) ∧
          ∃ g : Coeff 2 → ℂ,
            AnalyticOnNhd ℂ g (ball (sourceActionSequence (q := 2) (by simp) (by norm_num) t φ.val) R) ∧
            ∀ ψ : realTypeSourceSubmodule 4, sourceActionSequence (q := 2) (by simp) (by norm_num) t ψ.val ∈
              ball (sourceActionSequence (q := 2) (by simp) (by norm_num) t φ.val) R →
              g (sourceActionSequence (q := 2) (by simp) (by norm_num) t ψ.val) =
                A.renormalizedHamiltonian ψ.val := by
  obtain ⟨W₀,B,X,t,D,U,_,_,hcharts⟩ := A.exists_local_hamiltonian_action_factors
  refine ⟨W₀,B,X,t,D,?_⟩
  intro φ
  obtain ⟨C,Z,T,g,hZ,hbase,hZC,hT,himage,hg,hrec⟩ := hcharts φ
  have hcenter : sourceActionSequence (q := 2) (by simp) (by norm_num) t φ.val ∈ T := by
    rw [← himage]
    exact ⟨_,hbase,rfl⟩
  obtain ⟨R,hR,hball,hlift⟩ := D.exists_realAction_ball φ Z hZ hbase T hT hcenter
  refine ⟨R,hR,?_,?_,g,hg.mono hball,?_⟩
  · intro b hb
    obtain ⟨z,hz,he⟩ := himage.symm ▸ hball hb
    exact ⟨C.inverse z,(C.image_subset (hZC hz)).1,(C.actionSequence_eq z (hZC hz)).trans he⟩
  · intro b hb hpos
    obtain ⟨z,⟨hz,hzr⟩,he⟩ := hlift ⟨hb,hpos⟩
    obtain ⟨w,hw⟩ := (Coeff.mem_realPairLocus_iff z).mp hzr
    have hreal : C.inverse z ∈ realTypeSourceLocus 4 := by
      rw [← hw]
      exact C.real_preserving w (hw.symm ▸ hZC hz)
    exact ⟨⟨C.inverse z,hreal⟩,(C.actionSequence_eq z (hZC hz)).trans he⟩
  · intro ψ hψ
    apply C.recover_of_real_action_lift Z hZC A.renormalizedHamiltonian g
      (fun a b hab => A.renormalizedHamiltonian_real_eq_of_actions A a b hab) _ ψ
      (hlift ⟨hψ,D.actionSequence_mem_nonnegativeLocus ψ⟩)
    intro z hz
    simpa only [C.actionSequence_eq z (hZC hz)] using hrec z hz

end NLS.ZakharovShabat.SourcePrimitivePowerAtlas
