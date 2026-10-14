import NLS.ZakharovShabat.SourcePsiOriginalJacobianDecomposition
import NLS.SequenceSpaces.DeletedFiniteRankApproximation

/-!
# Finite-rank approximation of the original Jacobian remainder

The common reciprocal entry bound from Lemma 12.5 and Hölder duality
give an lp row majorant for the actual off-diagonal operator. Keeping
finitely many output rows then converges in operator norm, as in the
proof of Lemma 12.6. All central rows and columns are included.
-/

noncomputable section
open Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A single lp sequence bounds all output rows of the actual remainder. -/
theorem SourcePsiOriginalJacobianBounds.offDiagonal_rowMajorant
    {hp : p ≠ ⊤} {hp1 : 1 < p} {a : Coeff p} {ψ : CoeffPair p} {K C : ℝ}
    (H : SourcePsiOriginalJacobianBounds hp hp1 a ψ K C) (n : ℤ) :
    ∃ B : Coeff p, ∀ m : ℤ, ∀ b : DeletedCoeff p n,
      ‖((Coeff.deletedJacobianOffDiagonal n
        (sourcePsiOriginalRootJacobian hp hp1 n (Coeff.deleteCoordinateTo n a) ψ) b):Coeff p) m‖ ≤
        ‖B m‖*‖b‖ := by
  let Q := sourcePsiOriginalRootJacobian hp hp1 n (Coeff.deleteCoordinateTo n a) ψ
  let T := Coeff.deletedJacobianOffDiagonal n Q
  obtain ⟨B,_,hB⟩ := H.offDiagonal_div_bound
  let : Fact (1 ≤ p.conjExponent) := ⟨ENNReal.HolderConjugate.one_le p.conjExponent p⟩
  apply Coeff.exists_deletedOperator_rowMajorant_of_reciprocalEntries p.conjExponent hp n T B
  · intro m
    by_cases hm : m = n
    · subst m
      exact Coeff.deletedOperatorMatrixEntry_apply_deleted n n T
    · rw [Coeff.deletedOperatorMatrixEntry_apply_other n m m hm]
      exact Coeff.deletedJacobianOffDiagonal_diagonal n m hm Q
  · intro m k hkm
    by_cases hm : m = n
    · subst m
      have hz : Coeff.deletedOperatorMatrixEntry n T n k = 0 :=
        (T (Coeff.deleteCoordinateTo n (lp.single p k 1))).property
      rw [hz,norm_zero]
      exact div_nonneg (norm_nonneg _) (abs_nonneg _)
    by_cases hk : k = n
    · subst k
      rw [Coeff.deletedOperatorMatrixEntry_apply_deleted,norm_zero]
      exact div_nonneg (norm_nonneg _) (abs_nonneg _)
    · rw [Coeff.deletedOperatorMatrixEntry_apply_other n m k hk,
        Coeff.deletedJacobianOffDiagonal_entry_other n m k hk hkm.symm Q]
      have hb := hB n m k hkm.symm
      rw [sourcePsiOriginalJacobianEntry,Coeff.deletedOperatorMatrixEntry_apply_other n m k hk] at hb
      have he : ‖((m-k:ℤ):ℂ)‖ = |((k-m:ℤ):ℝ)| := by
        rw [Complex.norm_intCast]
        simp only [Int.cast_sub,abs_sub_comm]
      rw [he] at hb
      exact hb

/-- The actual finite output cutoffs have finite-dimensional range and converge in operator norm. -/
theorem SourcePsiOriginalJacobianBounds.offDiagonal_finiteRankApproximation
    {hp : p ≠ ⊤} {hp1 : 1 < p} {a : Coeff p} {ψ : CoeffPair p} {K C : ℝ}
    (H : SourcePsiOriginalJacobianBounds hp hp1 a ψ K C) (n : ℤ) :
    let T := Coeff.deletedJacobianOffDiagonal n
      (sourcePsiOriginalRootJacobian hp hp1 n (Coeff.deleteCoordinateTo n a) ψ)
    (∀ s : Finset ℤ, FiniteDimensional ℂ
      (LinearMap.range (Coeff.deletedOutputCutoff n T s).toLinearMap)) ∧
    Tendsto (Coeff.deletedOutputCutoff n T) atTop (𝓝 T) := by
  dsimp only
  obtain ⟨B,hB⟩ := H.offDiagonal_rowMajorant n
  exact ⟨fun s => Coeff.finiteDimensional_range_deletedOutputCutoff n _ s,
    Coeff.tendsto_deletedOutputCutoff_of_rowMajorant hp n _ B hB⟩

end NLS.ZakharovShabat
