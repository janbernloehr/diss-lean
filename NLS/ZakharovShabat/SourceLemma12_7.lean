import NLS.ZakharovShabat.SourceLemma12_6
import NLS.ZakharovShabat.SourcePsiOriginalJacobianInjective

/-!
# Lemma 12.7 on the original real root-placement domain

At every original Omega point and every omitted index the actual bounded
root Jacobian is injective on the complex deleted lp space. The preceding
source domain W, its diagonal-plus-compact decomposition, and all earlier
data remain unchanged.
-/

noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

structure SourceLemma12_7Data (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p)) : Prop where
  previous : SourceLemma12_6Data hp hp1 W
  injective : ∀ {V : Set (CoeffPair p)} {D : ℤ → Set ℂ} {c : ℝ},
    SourceIsolatingNeighborhoods hp hp1 V D c →
    ∀ t : realTypeSourceSubmodule p × RealCoeff p, (t.1:CoeffPair p) ∈ W →
      t ∈ sourcePsiOriginalOmega V D → ∀ n : ℤ,
      Function.Injective (sourcePsiOriginalRootJacobian hp hp1 n
        (Coeff.deleteCoordinateTo n (RealCoeff.complexCLM p t.2)) t.1)

theorem SourceLemma12_6Data.lemma12_7
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceLemma12_6Data hp hp1 W) : SourceLemma12_7Data hp hp1 W := by
  refine ⟨H,?_⟩
  intro V D c hD t htW htΩ n
  exact H.previous.previous.originalRootJacobian_injective hD t.1 htW htΩ.1 t.1.property
    n (RealCoeff.complexCLM p t.2) htΩ.2 (fun k => by simp)

/-- One unchanged open connected source domain contains every real-type source. -/
theorem sourceLemma12_7 (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ IsConnected W ∧ realTypeSourceLocus p ⊆ W ∧
      SourceLemma12_7Data hp hp1 W := by
  obtain ⟨W,hW,hc,hr,H⟩ := sourceLemma12_6 hp hp1
  exact ⟨W,hW,hc,hr,H.lemma12_7⟩

end NLS.ZakharovShabat
