import NLS.Articles.KdVPseudomeasures.OriginalDirichletLabels
import NLS.KdV.SingularDirichletCharacteristicNecessity

/-! # The native Dirichlet necessary condition on the entire original source

Every original real mean-zero physically period-one H-minus-one potential
is retained as its identical smooth-test distribution. Actual native
Dirichlet eigenvectors have energies among the full ordered characteristic
labels. The converse and native algebraic multiplicity counts remain open.
-/
noncomputable section
namespace NLS.Articles.KdVPseudomeasures
open NLS.KdV NLS.Fourier

/-- Every native eigenvector for the unchanged original distribution forces
its normalized original scalar Dirichlet characteristic to vanish. -/
theorem originalDirichletCharacteristic_eq_zero_of_native_eigen
    (q : OriginalHminusOnePotential) (lambda : ℂ) (f : UnitDirichletH1) (hf : f ≠ 0)
    (he : singularDirichletOperator q.val f = lambda • singularDirichletDomainInclusion f) :
    originalDirichletCharacteristic q lambda = 0 := by
  apply hillHminusDirichlet_eq_zero_of_native_eigen (originalPeriodOneCoefficients q) lambda f hf
  simpa only [periodOneOriginal_originalPeriodOneCoefficients] using he

/-- No native eigenvalue is lost by the ENTIRE intrinsic original Dirichlet
characteristic enumeration, including the finite central block. -/
theorem originalDirichlet_native_eigen_mem_labels
    (q : OriginalHminusOnePotential) (lambda : ℂ) (f : UnitDirichletH1) (hf : f ≠ 0)
    (he : singularDirichletOperator q.val f = lambda • singularDirichletDomainInclusion f) :
    ∃ n : ℕ+, lambda = (originalDirichletLabels q n:ℂ) :=
  (originalDirichletLabels_roots_iff q lambda).mp
    (originalDirichletCharacteristic_eq_zero_of_native_eigen q lambda f hf he)

/-- Necessity for the actual source partial operator with H-minus-one base
and full zero-trace H1 domain, without any spectral labeling assumption. -/
theorem originalDirichletCharacteristic_eq_zero_of_partial_eigen
    (q : OriginalHminusOnePotential) (lambda : ℂ)
    (hv : ∃ v : (singularDirichletPartialOperator q.val).domain,
      v.val ≠ 0 ∧ singularDirichletPartialOperator q.val v = lambda • v.val) :
    originalDirichletCharacteristic q lambda = 0 := by
  obtain ⟨f, hf, he⟩ := (singularDirichletPartialOperator_eigen_iff q.val lambda).mp hv
  exact originalDirichletCharacteristic_eq_zero_of_native_eigen q lambda f hf
    ((singularDirichletPencil_eq_zero_iff q.val lambda f).mp he)

end NLS.Articles.KdVPseudomeasures
