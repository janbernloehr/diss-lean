import NLS.ZakharovShabat.SourceLemma12_5
import NLS.SequenceSpaces.DeletedJacobianInvertibleDiagonal
import NLS.SequenceSpaces.DeletedJacobianCompactRemainder

/-!
# Diagonal isomorphism and compact remainder of the original Jacobian

For each fixed omitted index, the actual diagonal approaches two. Its
nonzero finite head and separated tail give a bounded reciprocal symbol.
The common off-diagonal row majorant from Lemma 12.5 makes the canonical
remainder compact on the full deleted lp space.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

private theorem norm_intCast_eq_natAbs (k : ℤ) : ‖(k:ℂ)‖ = (k.natAbs:ℝ) := by
  rw [Complex.norm_intCast]
  rw [← Int.cast_abs, ← Int.natCast_natAbs]
  simp

/-- The extracted operator symbol equals the actual diagonal, including its deleted zero. -/
theorem sourcePsiOriginalJacobian_diagonalSymbol_eq_entry
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n m : ℤ) (a : Coeff p) (ψ : CoeffPair p) :
    Coeff.deletedJacobianDiagonalSymbol n
      (sourcePsiOriginalRootJacobian hp hp1 n (Coeff.deleteCoordinateTo n a) ψ) m =
      sourcePsiOriginalJacobianEntry hp hp1 n m m a ψ := by
  by_cases hm : m = n
  · subst m; simp
  · rw [Coeff.deletedJacobianDiagonalSymbol_apply_other n m hm,
      sourcePsiOriginalJacobianEntry,Coeff.deletedOperatorMatrixEntry_apply_other n m m hm]

/-- For fixed n, every sufficiently distant diagonal entry is within epsilon of two. -/
theorem SourcePsiOriginalJacobianBounds.diagonal_tail
    {hp : p ≠ ⊤} {hp1 : 1 < p} {a : Coeff p} {ψ : CoeffPair p} {K C : ℝ}
    (H : SourcePsiOriginalJacobianBounds hp hp1 a ψ K C)
    (n : ℤ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ m : ℤ, N ≤ m.natAbs →
      ‖sourcePsiOriginalJacobianEntry hp hp1 n m m a ψ-2‖ < ε := by
  obtain ⟨R,S,_,_,_,hentry⟩ := H.diagonal n
  obtain ⟨M,hM⟩ := Coeff.exists_cutoff_norm_apply_lt hp S (half_pos hε)
  obtain ⟨L,hL⟩ := exists_nat_gt (2*K/ε+1)
  refine ⟨M+n.natAbs+L+1,?_⟩
  intro m hm
  have hmn : m ≠ n := by intro he; subst m; omega
  have htri : m.natAbs ≤ (n-m).natAbs+n.natAbs := by
    have ht := Int.natAbs_add_le (m-n) n
    have he : (m-n).natAbs = (n-m).natAbs := by
      rw [← Int.natAbs_neg (m-n), neg_sub]
    simpa only [sub_add_cancel,he] using ht
  have hLd : (L:ℝ) < ‖((n-m:ℤ):ℂ)‖ := by
    rw [norm_intCast_eq_natAbs]
    exact_mod_cast (show L < (n-m).natAbs by omega)
  have hpos : 0 < ‖((n-m:ℤ):ℂ)‖ :=
    norm_pos_iff.mpr (by exact_mod_cast sub_ne_zero.mpr hmn.symm)
  have hquot : K/‖((n-m:ℤ):ℂ)‖ < ε/2 := by
    apply (div_lt_iff₀ hpos).mpr
    have haux : 2*K/ε < ‖((n-m:ℤ):ℂ)‖ := by linarith
    have hx := (div_lt_iff₀ hε).mp haux
    nlinarith
  have hs : ‖S m‖ < ε/2 := hM m (by omega)
  have hr := (hentry m hmn).2.trans_lt hquot
  rw [(hentry m hmn).1]
  have he : (2:ℂ)+R m+S m-2 = R m+S m := by ring
  rw [he]
  exact (norm_add_le _ _).trans_lt (by linarith)

/-- The actual diagonal tends to two as the signed row index escapes in either direction. -/
theorem SourcePsiOriginalJacobianBounds.diagonal_tendsto_two
    {hp : p ≠ ⊤} {hp1 : 1 < p} {a : Coeff p} {ψ : CoeffPair p} {K C : ℝ}
    (H : SourcePsiOriginalJacobianBounds hp hp1 a ψ K C) (n : ℤ) :
    Tendsto (fun m : ℤ => sourcePsiOriginalJacobianEntry hp hp1 n m m a ψ)
      (Filter.comap Int.natAbs atTop) (𝓝 2) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨N,hN⟩ := H.diagonal_tail n ε hε
  apply eventually_comap.mpr
  apply eventually_atTop.mpr
  exact ⟨N,fun j hj m hm => by simpa only [dist_eq_norm] using hN m (hm ▸ hj)⟩

/-- Nonzero finite head entries and the tail limit give a positive lower bound on every retained entry. -/
theorem SourcePsiOriginalJacobianBounds.diagonal_lowerBound
    {hp : p ≠ ⊤} {hp1 : 1 < p} {a : Coeff p} {ψ : CoeffPair p} {K C : ℝ}
    (H : SourcePsiOriginalJacobianBounds hp hp1 a ψ K C) (n : ℤ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ m : ℤ, m ≠ n →
      δ ≤ ‖Coeff.deletedJacobianDiagonalSymbol n
        (sourcePsiOriginalRootJacobian hp hp1 n (Coeff.deleteCoordinateTo n a) ψ) m‖ := by
  obtain ⟨N,hN⟩ := H.diagonal_tail n 1 (by norm_num)
  apply Coeff.exists_deletedSymbol_uniformLowerBound n _ N
  · intro m hm
    rw [sourcePsiOriginalJacobian_diagonalSymbol_eq_entry]
    exact H.diagonal_nonzero n m hm
  · intro m _ hm
    rw [sourcePsiOriginalJacobian_diagonalSymbol_eq_entry]
    have hsmall := hN m hm
    have ht := norm_sub_le (sourcePsiOriginalJacobianEntry hp hp1 n m m a ψ)
      (sourcePsiOriginalJacobianEntry hp hp1 n m m a ψ-2)
    have he : sourcePsiOriginalJacobianEntry hp hp1 n m m a ψ-
        (sourcePsiOriginalJacobianEntry hp hp1 n m m a ψ-2) = 2 := by ring
    rw [he] at ht
    norm_num at ht
    linarith

/-- The canonical off-diagonal remainder is compact, including all central rows and columns. -/
theorem SourcePsiOriginalJacobianBounds.offDiagonal_compact
    {hp : p ≠ ⊤} {hp1 : 1 < p} {a : Coeff p} {ψ : CoeffPair p} {K C : ℝ}
    (H : SourcePsiOriginalJacobianBounds hp hp1 a ψ K C) (n : ℤ) :
    IsCompactOperator (Coeff.deletedJacobianOffDiagonal n
      (sourcePsiOriginalRootJacobian hp hp1 n (Coeff.deleteCoordinateTo n a) ψ)) := by
  obtain ⟨B,_,hB⟩ := H.offDiagonal_div_bound
  let : Fact (1 ≤ p.conjExponent) := ⟨ENNReal.HolderConjugate.one_le p.conjExponent p⟩
  apply Coeff.isCompactOperator_deletedJacobianOffDiagonal_of_tailEntryBound p.conjExponent hp n _ B 0
  intro m _ _ r hrn hrm
  have hb := hB n m r hrm.symm
  rw [sourcePsiOriginalJacobianEntry,Coeff.deletedOperatorMatrixEntry_apply_other n m r hrn] at hb
  have he : ‖((m-r:ℤ):ℂ)‖ = |((r-m:ℤ):ℝ)| := by
    rw [Complex.norm_intCast]
    simp only [Int.cast_sub,abs_sub_comm]
  rw [he] at hb
  exact hb

/-- The actual Jacobian is a diagonal Banach isomorphism plus its compact off-diagonal remainder. -/
theorem SourcePsiOriginalJacobianBounds.diagonal_plus_compact
    {hp : p ≠ ⊤} {hp1 : 1 < p} {a : Coeff p} {ψ : CoeffPair p} {K C : ℝ}
    (H : SourcePsiOriginalJacobianBounds hp hp1 a ψ K C) (n : ℤ) :
    ∃ D : DeletedCoeff p n ≃L[ℂ] DeletedCoeff p n,
      ∃ T : DeletedCoeff p n →L[ℂ] DeletedCoeff p n,
        IsCompactOperator T ∧
        sourcePsiOriginalRootJacobian hp hp1 n (Coeff.deleteCoordinateTo n a) ψ = D.toContinuousLinearMap+T ∧
        ∀ b : DeletedCoeff p n, ∀ m : ℤ,
          (D b:Coeff p) m = sourcePsiOriginalJacobianEntry hp hp1 n m m a ψ*(b:Coeff p) m := by
  let Q := sourcePsiOriginalRootJacobian hp hp1 n (Coeff.deleteCoordinateTo n a) ψ
  obtain ⟨δ,hδ,hbound⟩ := H.diagonal_lowerBound n
  let D : DeletedCoeff p n ≃L[ℂ] DeletedCoeff p n := Coeff.deletedMultiplierEquivOfLowerBound n (Coeff.deletedJacobianDiagonalSymbol n Q) δ hδ hbound
  refine ⟨D,Coeff.deletedJacobianOffDiagonal n Q,H.offDiagonal_compact n,?_,?_⟩
  · exact Coeff.deletedJacobian_eq_diagonal_add_offDiagonal n Q
  · intro b m
    change Coeff.deletedJacobianDiagonalSymbol n Q m*(b:Coeff p) m = _
    rw [sourcePsiOriginalJacobian_diagonalSymbol_eq_entry]

/-- The diagonal inverse divides by the actual nonzero diagonal entry.
Both coordinate formulas also hold at the omitted coordinate, where inputs vanish. -/
theorem SourcePsiOriginalJacobianBounds.diagonal_plus_compact_with_inverse
    {hp : p ≠ ⊤} {hp1 : 1 < p} {a : Coeff p} {ψ : CoeffPair p} {K C : ℝ}
    (H : SourcePsiOriginalJacobianBounds hp hp1 a ψ K C) (n : ℤ) :
    ∃ D : DeletedCoeff p n ≃L[ℂ] DeletedCoeff p n,
      ∃ T : DeletedCoeff p n →L[ℂ] DeletedCoeff p n,
        IsCompactOperator T ∧
        sourcePsiOriginalRootJacobian hp hp1 n (Coeff.deleteCoordinateTo n a) ψ = D.toContinuousLinearMap+T ∧
        (∀ b : DeletedCoeff p n, ∀ m : ℤ,
          (D b:Coeff p) m = sourcePsiOriginalJacobianEntry hp hp1 n m m a ψ*(b:Coeff p) m) ∧
        ∀ b : DeletedCoeff p n, ∀ m : ℤ,
          (D.symm b:Coeff p) m = (sourcePsiOriginalJacobianEntry hp hp1 n m m a ψ)⁻¹*(b:Coeff p) m := by
  obtain ⟨D,T,hT,hQ,hD⟩ := H.diagonal_plus_compact n
  refine ⟨D,T,hT,hQ,hD,?_⟩
  intro b m
  by_cases hm : m = n
  · subst m
    simp only [show (D.symm b:Coeff p) n = 0 from (D.symm b).property,
      show (b:Coeff p) n = 0 from b.property,mul_zero]
  · have he := hD (D.symm b) m
    rw [D.apply_symm_apply] at he
    rw [he]
    simp only [← mul_assoc,inv_mul_cancel₀ (H.diagonal_nonzero n m hm),one_mul]

end NLS.ZakharovShabat
