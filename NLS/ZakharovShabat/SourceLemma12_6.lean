import NLS.ZakharovShabat.SourcePsiOriginalJacobianFiniteRank

/-!
# Lemma 12.6 on the original real root-placement domain

At every original Omega point and every omitted index, the actual bounded
Jacobian is a diagonal continuous linear equivalence plus a compact
operator. The preceding source domain W and all Lemma 12.5 data are retained.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

structure SourceLemma12_6Data (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p)) : Prop where
  previous : SourceLemma12_5Data hp hp1 W
  decomposition : ∀ {V : Set (CoeffPair p)} {discs : ℤ → Set ℂ} {c : ℝ},
    SourceIsolatingNeighborhoods hp hp1 V discs c → IsOpen V →
    ∀ t : realTypeSourceSubmodule p × RealCoeff p, (t.1:CoeffPair p) ∈ W →
      t ∈ sourcePsiOriginalOmega V discs → ∀ n : ℤ,
      ∃ D : DeletedCoeff p n ≃L[ℂ] DeletedCoeff p n,
        ∃ T : DeletedCoeff p n →L[ℂ] DeletedCoeff p n, IsCompactOperator T ∧
          sourcePsiOriginalRootJacobian hp hp1 n
            (Coeff.deleteCoordinateTo n (RealCoeff.complexCLM p t.2)) t.1 = D.toContinuousLinearMap+T ∧
          (∀ b : DeletedCoeff p n, ∀ m : ℤ,
            (D b:Coeff p) m = sourcePsiOriginalJacobianEntry hp hp1 n m m
              (RealCoeff.complexCLM p t.2) t.1*(b:Coeff p) m) ∧
          ∀ b : DeletedCoeff p n, ∀ m : ℤ,
            (D.symm b:Coeff p) m = (sourcePsiOriginalJacobianEntry hp hp1 n m m
              (RealCoeff.complexCLM p t.2) t.1)⁻¹*(b:Coeff p) m

theorem SourceLemma12_5Data.lemma12_6
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceLemma12_5Data hp hp1 W) : SourceLemma12_6Data hp hp1 W := by
  refine ⟨H,?_⟩
  intro V discs c hD hV t htW htΩ n
  obtain ⟨U,_,htU,_,K,C,_,_,hb⟩ := H.originalOmega hD hV t htW htΩ
  exact (hb t htU).diagonal_plus_compact_with_inverse n

/-- The compact part can be chosen as the canonical off-diagonal operator,
whose finite output cutoffs converge in norm. -/
theorem SourceLemma12_6Data.finiteRankApproximation
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceLemma12_6Data hp hp1 W)
    {V : Set (CoeffPair p)} {discs : ℤ → Set ℂ} {c : ℝ}
    (hD : SourceIsolatingNeighborhoods hp hp1 V discs c) (hV : IsOpen V)
    (t : realTypeSourceSubmodule p × RealCoeff p) (htW : (t.1:CoeffPair p) ∈ W)
    (htΩ : t ∈ sourcePsiOriginalOmega V discs) (n : ℤ) :
    let T := Coeff.deletedJacobianOffDiagonal n
      (sourcePsiOriginalRootJacobian hp hp1 n
        (Coeff.deleteCoordinateTo n (RealCoeff.complexCLM p t.2)) t.1)
    (∀ s : Finset ℤ, FiniteDimensional ℂ
      (LinearMap.range (Coeff.deletedOutputCutoff n T s).toLinearMap)) ∧
    Tendsto (Coeff.deletedOutputCutoff n T) atTop (𝓝 T) := by
  obtain ⟨U,_,htU,_,K,C,_,_,hb⟩ := H.previous.originalOmega hD hV t htW htΩ
  exact (hb t htU).offDiagonal_finiteRankApproximation n

theorem sourceLemma12_6 (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ IsConnected W ∧ realTypeSourceLocus p ⊆ W ∧
      SourceLemma12_6Data hp hp1 W := by
  obtain ⟨W,hW,hc,hr,H⟩ := sourceLemma12_5 hp hp1
  exact ⟨W,hW,hc,hr,H.lemma12_6⟩

end NLS.ZakharovShabat
