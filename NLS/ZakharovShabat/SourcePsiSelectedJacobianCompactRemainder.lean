import NLS.ZakharovShabat.SourcePsiSelectedJacobianOffDiagonalTail
import NLS.SequenceSpaces.CompactTailReciprocalMatrix

/-!
# Compact off-diagonal remainder of the selected psi Jacobian

The selected Jacobian has reciprocal off-diagonal matrix estimates on
a common distant-row tail. Its canonical diagonal subtraction has
zero diagonal entries, so the matrix compactness criterion applies.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Near a real-type source, the off-diagonal remainder of the actual
selected sequence-valued psi Jacobian is compact on the real
quarter-π localized root locus. Only the distant-row estimates enter
the proof; finite head rows are controlled by boundedness. -/
theorem exists_local_sourcePsi_selectedJacobian_compactRemainder
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (n : ℤ) (a₀ : DeletedCoeff p n) :
    ∃ U : Set (DeletedCoeff p n × CoeffPair p), IsOpen U ∧
      (a₀,φ) ∈ U ∧
      ∃ c : ℤ → ℂ, ∃ R : ℤ → ℝ,
        ∀ a : DeletedCoeff p n, ∀ ψ : CoeffPair p,
          (a,ψ) ∈ U →
          IsRealType (CoeffPair.toMax p ψ) →
          (∀ j : ℤ, (displacedRoots (a : Coeff p) j).im = 0) →
          (∀ j : ℤ, ‖(a : Coeff p) j‖ ≤ Real.pi/4) →
          IsCompactOperator
            (Coeff.deletedJacobianOffDiagonal n
              (sourcePsiSelectedRootJacobian hp hp1 n c R a ψ)) := by
  obtain ⟨U,hUopen,hbase,K,c,R,hchoice,M,hM,hoff⟩ :=
    exists_local_sourcePsi_selectedJacobian_offDiagonalUniformTail
      hp hp1 φ hφ n a₀
  refine ⟨U,hUopen,hbase,c,R,?_⟩
  intro a ψ hpair hreal hroots hloc
  obtain ⟨B,hBnorm,hB⟩ := hoff a ψ hpair hreal hroots hloc
  let Q : DeletedCoeff p n →L[ℂ] DeletedCoeff p n :=
    sourcePsiSelectedRootJacobian hp hp1 n c R a ψ
  let T : DeletedCoeff p n →L[ℂ] DeletedCoeff p n :=
    Coeff.deletedJacobianOffDiagonal n Q
  let b : Coeff p :=
    sourcePsiOffDiagonalRowMajorant hp hp1 (a : Coeff p) ψ B
  let : Fact (1 ≤ p.conjExponent) :=
    ⟨ENNReal.HolderConjugate.one_le p.conjExponent p⟩
  apply Coeff.isCompactOperator_deleted_of_tailReciprocalMatrixBound
    p.conjExponent hp n T b K
  · intro m hm
    by_cases hmn : m = n
    · subst m
      exact Coeff.deletedOperatorMatrixEntry_apply_deleted n n T
    · rw [Coeff.deletedOperatorMatrixEntry_apply_other n m m hmn]
      exact Coeff.deletedJacobianOffDiagonal_diagonal n m hmn Q
  · intro m hm k hkm
    by_cases hmn : m = n
    · subst m
      have hzero : Coeff.deletedOperatorMatrixEntry n T n k = 0 :=
        (T (Coeff.deleteCoordinateTo n (lp.single p k 1))).property
      rw [hzero]
      simp only [norm_zero]
      exact div_nonneg (norm_nonneg (b n))
        (abs_nonneg (((k-n : ℤ) : ℝ)))
    by_cases hkn : k = n
    · subst k
      rw [Coeff.deletedOperatorMatrixEntry_apply_deleted]
      simp only [norm_zero]
      exact div_nonneg (norm_nonneg (b m))
        (abs_nonneg (((n-m : ℤ) : ℝ)))
    · rw [Coeff.deletedOperatorMatrixEntry_apply_other n m k hkn,
        Coeff.deletedJacobianOffDiagonal_entry_other n m k hkn (Ne.symm hkm) Q]
      have hentry := hB m hm hmn k hkn (Ne.symm hkm)
      have hden : |(((m-k : ℤ) : ℝ))| = |(((k-m : ℤ) : ℝ))| := by
        simp only [Int.cast_sub]
        exact abs_sub_comm (m : ℝ) (k : ℝ)
      simpa only [b,Q,Complex.norm_intCast,hden] using hentry

end NLS.ZakharovShabat
