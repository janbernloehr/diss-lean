import NLS.SequenceSpaces.CompactTailReciprocalMatrix
import NLS.SequenceSpaces.Compact

/-!
# Compactness from reciprocal bounds on tail rows and columns

Finitely many input columns factor through a finite Fourier projection
and so produce a compact operator. The remaining matrix has zero head
columns, allowing the existing tail-row reciprocal criterion to apply.
-/

noncomputable section
open scoped ENNReal
namespace NLS.Coeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

private def deletedHeadProjection (n : ℤ) (s : Finset ℤ) :
    DeletedCoeff p n →L[ℂ] DeletedCoeff p n :=
  (deleteCoordinateTo n).comp
    ((truncateCLM s).comp
      ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n).ker.subtypeL))

private theorem deletedHeadProjection_single (n k : ℤ) (hkn : k ≠ n)
    (s : Finset ℤ) :
    deletedHeadProjection (p := p) n s (deletedSingleCLM n k hkn 1) =
      if k ∈ s then deletedSingleCLM n k hkn 1 else 0 := by
  have htrunc : truncate s (lp.single p k (1 : ℂ)) =
      if k ∈ s then lp.single p k 1 else 0 := by
    ext j
    by_cases hk : k ∈ s <;> by_cases hj : j = k <;>
      simp [truncate_apply,hk,hj,lp.single_apply]
  change deleteCoordinateTo n
    (truncate s ((deletedSingleCLM n k hkn 1 : DeletedCoeff p n) : Coeff p)) = _
  rw [deletedSingleCLM_coe,htrunc]
  split_ifs with hk
  · exact deleteCoordinateTo_single_other n k hkn 1
  · simp

/-- Reciprocal off-diagonal matrix bounds only on distant output rows
and distant input columns imply compactness. The finitely many omitted
columns form a compact finite-rank part. -/
theorem isCompactOperator_deleted_of_tailRowColumnReciprocalMatrixBound
    (q : ℝ≥0∞) [Fact (1 ≤ q)] [p.HolderConjugate q]
    (hp : p ≠ ⊤) (n : ℤ)
    (T : DeletedCoeff p n →L[ℂ] DeletedCoeff p n)
    (b : Coeff p) (Krow Kcol : ℕ)
    (hdiag : ∀ m : ℤ, Krow ≤ m.natAbs →
      deletedOperatorMatrixEntry n T m m = 0)
    (hoff : ∀ m : ℤ, Krow ≤ m.natAbs →
      ∀ k : ℤ, Kcol < k.natAbs → k ≠ m →
        ‖deletedOperatorMatrixEntry n T m k‖ ≤
          ‖b m‖ / |((k-m : ℤ) : ℝ)|) :
    IsCompactOperator T := by
  let s : Finset ℤ := Finset.Icc (-(Kcol : ℤ)) (Kcol : ℤ)
  let P : DeletedCoeff p n →L[ℂ] DeletedCoeff p n :=
    deletedHeadProjection n s
  let S : DeletedCoeff p n →L[ℂ] DeletedCoeff p n := T - T.comp P
  have hP : IsCompactOperator P := by
    simpa only [P,deletedHeadProjection,ContinuousLinearMap.coe_comp]
      using (((isCompactOperator_truncateCLM (p := p) s).comp_clm
        ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n).ker.subtypeL)).clm_comp
          (deleteCoordinateTo n))
  have hTP : IsCompactOperator (T.comp P) := by
    simpa only [ContinuousLinearMap.coe_comp] using hP.clm_comp T
  have hentry (m k : ℤ) :
      deletedOperatorMatrixEntry n S m k =
        if k ∈ s then 0 else deletedOperatorMatrixEntry n T m k := by
    by_cases hkn : k = n
    · subst k
      simp
    · rw [deletedOperatorMatrixEntry_apply_other n m k hkn S,
        deletedOperatorMatrixEntry_apply_other n m k hkn T]
      by_cases hk : k ∈ s
      · simp [S,P,deletedHeadProjection_single n k hkn s,hk]
      · simp [S,P,deletedHeadProjection_single n k hkn s,hk]
  let K : ℕ := max Krow (Kcol+1)
  have hS : IsCompactOperator S := by
    apply isCompactOperator_deleted_of_tailReciprocalMatrixBound
      q hp n S b K
    · intro m hm
      have hmrow : Krow ≤ m.natAbs := by dsimp [K] at hm; omega
      have hmcol : Kcol < m.natAbs := by dsimp [K] at hm; omega
      have hms : m ∉ s := by
        simp only [s,Finset.mem_Icc]
        omega
      rw [hentry m m,if_neg hms]
      exact hdiag m hmrow
    · intro m hm k hkm
      have hmrow : Krow ≤ m.natAbs := by dsimp [K] at hm; omega
      rw [hentry m k]
      by_cases hks : k ∈ s
      · rw [if_pos hks,norm_zero]
        exact div_nonneg (norm_nonneg (b m))
          (abs_nonneg (((k-m : ℤ) : ℝ)))
      · rw [if_neg hks]
        have hkcol : Kcol < k.natAbs := by
          simp only [s,Finset.mem_Icc] at hks
          omega
        exact hoff m hmrow k hkcol hkm
  have hsum : T = S + T.comp P := by
    ext a
    simp [S]
  rw [hsum]
  exact hS.add hTP

end NLS.Coeff
