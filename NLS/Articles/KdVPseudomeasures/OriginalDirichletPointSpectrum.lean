import NLS.Articles.KdVPseudomeasures.OriginalDirichletLabels
import NLS.KdV.SingularDirichletCharacteristicSufficiency

/-! # The complete original Dirichlet point spectrum

The full real characteristic labels are exactly the energies of nonzero
native eigenvectors. The domain is the full zero-trace H1 interval space,
and the actual partial operator acts on its full H-minus-one dual base.
No assertion about other spectrum or algebraic multiplicities is inferred.
-/
noncomputable section
namespace NLS.Articles.KdVPseudomeasures
open NLS.KdV NLS.Fourier

/-- The exact original distribution has a native eigenvector precisely at
its normalized Dirichlet characteristic zeros, including all central energies. -/
theorem originalDirichletCharacteristic_eq_zero_iff_native_eigen
    (q : OriginalHminusOnePotential) (lambda : ℂ) :
    originalDirichletCharacteristic q lambda = 0 ↔
      ∃ f : UnitDirichletH1, f ≠ 0 ∧
        singularDirichletOperator q.val f = lambda • singularDirichletDomainInclusion f := by
  change hillHminusDirichlet (originalPeriodOneCoefficients q) lambda = 0 ↔ _
  rw [hillHminusDirichlet_eq_zero_iff_native_eigen,
    periodOneOriginal_originalPeriodOneCoefficients]

/-- The same criterion is on the actual source H-minus-one partial operator. -/
theorem originalDirichletCharacteristic_eq_zero_iff_partial_eigen
    (q : OriginalHminusOnePotential) (lambda : ℂ) :
    originalDirichletCharacteristic q lambda = 0 ↔
      ∃ v : (singularDirichletPartialOperator q.val).domain,
        v.val ≠ 0 ∧ singularDirichletPartialOperator q.val v = lambda • v.val := by
  change hillHminusDirichlet (originalPeriodOneCoefficients q) lambda = 0 ↔ _
  rw [hillHminusDirichlet_eq_zero_iff_partial_eigen,
    periodOneOriginal_originalPeriodOneCoefficients]

/-- Every full intrinsic original Dirichlet label is a native eigenvalue,
with an actual nonzero zero-trace H1 vector. -/
theorem originalDirichletLabels_is_native_eigen (q : OriginalHminusOnePotential) (n : ℕ+) :
    ∃ f : UnitDirichletH1, f ≠ 0 ∧
      singularDirichletOperator q.val f =
        (originalDirichletLabels q n:ℂ) • singularDirichletDomainInclusion f :=
  (originalDirichletCharacteristic_eq_zero_iff_native_eigen q _).mp
    (originalDirichletLabels_is_root q n)

/-- The original full ordered positive-index labels exhaust EXACTLY all
native Dirichlet eigenvalues; no finite central block is omitted or supplied. -/
theorem originalDirichlet_native_eigen_iff_mem_labels
    (q : OriginalHminusOnePotential) (lambda : ℂ) :
    (∃ f : UnitDirichletH1, f ≠ 0 ∧
      singularDirichletOperator q.val f = lambda • singularDirichletDomainInclusion f) ↔
      ∃ n : ℕ+, lambda = (originalDirichletLabels q n:ℂ) := by
  rw [← originalDirichletCharacteristic_eq_zero_iff_native_eigen,
    originalDirichletLabels_roots_iff]

/-- Exhaustion on the actual source base-space partial operator. -/
theorem originalDirichlet_partial_eigen_iff_mem_labels
    (q : OriginalHminusOnePotential) (lambda : ℂ) :
    (∃ v : (singularDirichletPartialOperator q.val).domain,
      v.val ≠ 0 ∧ singularDirichletPartialOperator q.val v = lambda • v.val) ↔
      ∃ n : ℕ+, lambda = (originalDirichletLabels q n:ℂ) := by
  rw [← originalDirichletCharacteristic_eq_zero_iff_partial_eigen,
    originalDirichletLabels_roots_iff]

end NLS.Articles.KdVPseudomeasures
