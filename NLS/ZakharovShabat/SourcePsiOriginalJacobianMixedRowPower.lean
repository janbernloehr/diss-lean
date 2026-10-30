import NLS.SequenceSpaces.ReciprocalMixedRowPower
import NLS.ZakharovShabat.SourceLemma12_6

/-!
# Mixed row-power summability of the original Jacobian

The actual off-diagonal remainder satisfies the double-sum estimate in
the proof of Lemma 12.6, with the conjugate exponent of the source lp
space. The bound includes every finite-head row and column and holds at
every point of the original real root-placement domain.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual off-diagonal Jacobian satisfies the printed mixed row-sum finiteness. -/
theorem SourcePsiOriginalJacobianBounds.offDiagonal_mixedRowPower
    {hp : p ≠ ⊤} {hp1 : 1 < p} {a : Coeff p} {ψ : CoeffPair p} {K C : ℝ}
    (H : SourcePsiOriginalJacobianBounds hp hp1 a ψ K C) (n : ℤ) :
    let T := Coeff.deletedJacobianOffDiagonal n
      (sourcePsiOriginalRootJacobian hp hp1 n (Coeff.deleteCoordinateTo n a) ψ)
    Summable (fun m : ℤ =>
      (∑' k : ℤ, ‖Coeff.deletedOperatorMatrixEntry n T m k‖ ^ p.conjExponent.toReal) ^
        (p.toReal/p.conjExponent.toReal)) := by
  let Q := sourcePsiOriginalRootJacobian hp hp1 n (Coeff.deleteCoordinateTo n a) ψ
  let T := Coeff.deletedJacobianOffDiagonal n Q
  obtain ⟨B,_,hB⟩ := H.offDiagonal_div_bound
  let : Fact (1 ≤ p.conjExponent) := ⟨ENNReal.HolderConjugate.one_le p.conjExponent p⟩
  have hq : p.conjExponent ≠ ⊤ :=
    ((ENNReal.HolderConjugate.lt_top_iff_one_lt p.conjExponent p).mpr hp1).ne
  have hq1 : 1 < p.conjExponent :=
    (ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top
  apply Coeff.summable_mixedRowPower_of_reciprocal_bound hp hq hq1
    (fun m k => Coeff.deletedOperatorMatrixEntry n T m k) B
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
      rwa [he] at hb

/-- Mixed row-power summability holds at every original real-domain point. -/
theorem SourceLemma12_6Data.mixedRowPower
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceLemma12_6Data hp hp1 W)
    {V : Set (CoeffPair p)} {discs : ℤ → Set ℂ} {c : ℝ}
    (hD : SourceIsolatingNeighborhoods hp hp1 V discs c) (hV : IsOpen V)
    (t : realTypeSourceSubmodule p × RealCoeff p) (htW : (t.1:CoeffPair p) ∈ W)
    (htΩ : t ∈ sourcePsiOriginalOmega V discs) (n : ℤ) :
    let T := Coeff.deletedJacobianOffDiagonal n
      (sourcePsiOriginalRootJacobian hp hp1 n
        (Coeff.deleteCoordinateTo n (RealCoeff.complexCLM p t.2)) t.1)
    Summable (fun m : ℤ =>
      (∑' k : ℤ, ‖Coeff.deletedOperatorMatrixEntry n T m k‖ ^ p.conjExponent.toReal) ^
        (p.toReal/p.conjExponent.toReal)) := by
  obtain ⟨U,_,htU,_,K,C,_,_,hb⟩ := H.previous.originalOmega hD hV t htW htΩ
  exact (hb t htU).offDiagonal_mixedRowPower n

end NLS.ZakharovShabat
