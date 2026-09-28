import NLS.SequenceSpaces.DeletedJacobianMatrixExpansion
import NLS.SequenceSpaces.CompactTailRowMajorant
import NLS.SequenceSpaces.CompactPuncturedKernel

/-!
# Compactness from reciprocal matrix bounds on a tail

The finite matrix expansion and conjugate `ℓᵖ` duality turn reciprocal
entry estimates into an output-row majorant. Since the operator is
bounded, the finitely many uncontrolled head rows are harmless.
-/

noncomputable section
open Filter Topology
open scoped ENNReal
namespace NLS.Coeff
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
  [p.HolderConjugate q]

/-- A row with reciprocal off-diagonal matrix bounds is represented
by an `ℓᑫ` kernel whose norm is controlled by the punctured lattice. -/
theorem exists_deletedOperator_rowKernel_of_reciprocalEntries
    (hp : p ≠ ⊤) (n m : ℤ)
    (T : DeletedCoeff p n →L[ℂ] DeletedCoeff p n)
    (b : Coeff p)
    (hdiag : deletedOperatorMatrixEntry n T m m = 0)
    (hoff : ∀ k : ℤ, k ≠ m →
      ‖deletedOperatorMatrixEntry n T m k‖ ≤
        ‖b m‖ / |((k-m : ℤ) : ℝ)|) :
    ∃ row : Coeff q,
      ‖row‖ ≤ ‖b m‖ *
        ‖puncturedLattice q
          ((ENNReal.HolderConjugate.lt_top_iff_one_lt p q).mp hp.lt_top)‖ ∧
      ∀ a : DeletedCoeff p n,
        ((T a : DeletedCoeff p n) : Coeff p) m =
          dualPairing (a : Coeff p) row := by
  let hq : 1 < q :=
    (ENNReal.HolderConjugate.lt_top_iff_one_lt p q).mp hp.lt_top
  let c : Coeff q := puncturedLattice q hq
  let w : Coeff q := (‖b m‖ : ℂ) • shift m c
  have hw (k : ℤ) : ‖w k‖ =
      ‖b m‖ * (if k = m then 0 else |((k-m : ℤ) : ℝ)|⁻¹) := by
    simp only [w,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,norm_mul,
      Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg (b m))]
    exact congrArg (‖b m‖ * ·)
      (norm_shift_puncturedLattice_apply hq m k)
  have hpoint (k : ℤ) :
      ‖deletedOperatorMatrixEntry n T m k‖ ≤ ‖w k‖ := by
    rw [hw]
    by_cases hkm : k = m
    · subst k
      simp [hdiag]
    · rw [if_neg hkm]
      simpa only [div_eq_mul_inv] using hoff k hkm
  have hmem : Memℓp
      (fun k : ℤ => deletedOperatorMatrixEntry n T m k) q :=
    (lp.memℓp w).mono' hpoint
  let row : Coeff q :=
    ⟨fun k => deletedOperatorMatrixEntry n T m k,hmem⟩
  have hrowBound : ‖row‖ ≤ ‖b m‖ * ‖c‖ := by
    calc
      ‖row‖ ≤ ‖w‖ :=
        lp.norm_mono (zero_lt_one.trans_le Fact.out).ne' hpoint
      _ = ‖b m‖ * ‖c‖ := by
        rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,
          abs_of_nonneg (norm_nonneg (b m)),norm_shift]
  refine ⟨row,hrowBound,?_⟩
  intro a
  have hmatrix := tendsto_deletedOperator_matrixSum hp n m T a
  have hsum : Summable (fun k : ℤ => (a : Coeff p) k * row k) :=
    (summable_norm_dualPairing (a : Coeff p) row).of_norm
  have hpair : Tendsto (fun s : Finset ℤ =>
      ∑ k ∈ s, (a : Coeff p) k * row k) atTop
        (𝓝 (dualPairing (a : Coeff p) row)) := by
    rw [dualPairing_apply]
    exact hsum.hasSum
  have hsame : (fun s : Finset ℤ =>
      ∑ k ∈ s, (a : Coeff p) k * row k) =
      (fun s : Finset ℤ =>
        ∑ k ∈ s, (a : Coeff p) k * deletedOperatorMatrixEntry n T m k) := rfl
  rw [hsame] at hpair
  exact tendsto_nhds_unique hmatrix hpair

/-- A deleted-coordinate operator with zero diagonal and reciprocal
off-diagonal matrix bounds on distant output rows is compact. No
separate row representation or finite-head estimate is required. -/
theorem isCompactOperator_deleted_of_tailReciprocalMatrixBound
    (q : ℝ≥0∞) [Fact (1 ≤ q)] [p.HolderConjugate q]
    (hp : p ≠ ⊤) (n : ℤ)
    (T : DeletedCoeff p n →L[ℂ] DeletedCoeff p n)
    (b : Coeff p) (K : ℕ)
    (hdiag : ∀ m : ℤ, K ≤ m.natAbs →
      deletedOperatorMatrixEntry n T m m = 0)
    (hoff : ∀ m : ℤ, K ≤ m.natAbs →
      ∀ k : ℤ, k ≠ m →
        ‖deletedOperatorMatrixEntry n T m k‖ ≤
          ‖b m‖ / |((k-m : ℤ) : ℝ)|) :
    IsCompactOperator T := by
  let c : Coeff q := puncturedLattice q
    ((ENNReal.HolderConjugate.lt_top_iff_one_lt p q).mp hp.lt_top)
  let B : Coeff p := (‖c‖ : ℂ) • b
  apply isCompactOperator_deleted_of_tailRowMajorant hp n T B K
  intro m hm a
  obtain ⟨row,hrowBound,hrep⟩ :=
    exists_deletedOperator_rowKernel_of_reciprocalEntries (q := q)
      hp n m T b (hdiag m hm) (hoff m hm)
  have hB : ‖B m‖ = ‖c‖ * ‖b m‖ := by
    simp only [B,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,norm_mul,
      Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg c)]
  rw [hrep a,hB]
  calc
    ‖dualPairing (a : Coeff p) row‖ ≤
        ‖(a : Coeff p)‖ * ‖row‖ := norm_dualPairing_le _ _
    _ ≤ ‖a‖ * (‖b m‖ * ‖c‖) :=
      mul_le_mul_of_nonneg_left hrowBound (norm_nonneg a)
    _ = (‖c‖ * ‖b m‖) * ‖a‖ := by ring

end NLS.Coeff
