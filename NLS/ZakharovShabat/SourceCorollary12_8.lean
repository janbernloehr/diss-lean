import NLS.ZakharovShabat.SourcePsiOriginalJacobianInverse

/-!
# Corollary 12.8 on the original root-placement domain

At every original Omega point, the actual Jacobian is a continuous
linear isomorphism on both the complex and real deleted lp spaces.
The same source domain W and all preceding data are retained.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Corollary 12.8, with exact identification of both real and complex derivatives. -/
structure SourceCorollary12_8Data (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p)) : Prop where
  previous : SourceLemma12_7Data hp hp1 W
  isomorphism : ∀ {V : Set (CoeffPair p)} {D : ℤ → Set ℂ} {c : ℝ},
    SourceIsolatingNeighborhoods hp hp1 V D c → IsOpen V →
    ∀ t : realTypeSourceSubmodule p × RealCoeff p, (t.1:CoeffPair p) ∈ W →
      t ∈ sourcePsiOriginalOmega V D → ∀ n : ℤ,
      ∃ e : DeletedCoeff p n ≃L[ℂ] DeletedCoeff p n,
      ∃ r : RealDeletedCoeff p n ≃L[ℝ] RealDeletedCoeff p n,
        e.toContinuousLinearMap = sourcePsiOriginalRootJacobian hp hp1 n
          (Coeff.deleteCoordinateTo n (RealCoeff.complexCLM p t.2)) t.1 ∧
        r.toContinuousLinearMap = sourcePsiOriginalRealRootJacobian hp hp1 n
          (RealDeletedCoeff.deleteCoordinateTo n t.2) t.1 ∧
        ∀ b : RealDeletedCoeff p n, RealDeletedCoeff.complexCLM n (r b) = e (RealDeletedCoeff.complexCLM n b)

theorem SourceLemma12_7Data.corollary12_8
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceLemma12_7Data hp hp1 W) : SourceCorollary12_8Data hp hp1 W := by
  refine ⟨H,?_⟩
  intro V D c hD hV t htW htΩ n
  exact ⟨H.originalJacobianEquiv hD hV t htW htΩ n,
    H.originalJacobianRealEquiv hD hV t htW htΩ n,rfl,
    H.originalJacobianRealEquiv_toCLM hD hV t htW htΩ n,
    H.originalJacobianRealEquiv_complex hD hV t htW htΩ n⟩

theorem sourceCorollary12_8 (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ IsConnected W ∧ realTypeSourceLocus p ⊆ W ∧
      SourceCorollary12_8Data hp hp1 W := by
  obtain ⟨W,hW,hc,hr,H⟩ := sourceLemma12_7 hp hp1
  exact ⟨W,hW,hc,hr,H.corollary12_8⟩

end NLS.ZakharovShabat
