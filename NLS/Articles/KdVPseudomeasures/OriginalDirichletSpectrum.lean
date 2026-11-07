import NLS.Articles.KdVPseudomeasures.OriginalDirichletMultiplicity
import NLS.KdV.SingularDirichletSpectrum
import NLS.KdV.SingularDirichletDenseDomain

/-! # The full native Dirichlet spectrum on the original physical source

The actual operator is closed and densely defined on its full zero-trace
H1 domain in the full H-minus-one dual base. Its compact resolvent excludes
all spectrum beyond the independently verified characteristic zeros. Thus
the full intrinsic original labels enumerate its entire spectrum, with the
previously verified actual algebraic root-space dimensions.
-/
noncomputable section
open Set
namespace NLS.Articles.KdVPseudomeasures
open NLS.KdV NLS.Fourier

/-- The actual native operator for each original physical distribution is closed. -/
theorem isClosed_originalDirichletPartialOperator (q : OriginalHminusOnePotential) :
    (singularDirichletPartialOperator q.val).IsClosed :=
  isClosed_singularDirichletPartialOperator q.val

/-- Its domain is dense in the FULL native H-minus-one base. -/
theorem dense_domain_originalDirichletPartialOperator (q : OriginalHminusOnePotential) :
    Dense ((singularDirichletPartialOperator q.val).domain : Set UnitDirichletHminus) :=
  dense_domain_singularDirichletPartialOperator q.val

/-- There is an actual compact bounded inverse at a resolvent energy for every original source. -/
theorem exists_compact_originalDirichletResolvent (q : OriginalHminusOnePotential) :
    ∃ a ∈ singularDirichletResolventSet q.val,
      IsCompactOperator (singularDirichletBaseResolvent q.val a) := by
  obtain ⟨a, ha⟩ := singularDirichletResolventSet_nonempty q.val
  exact ⟨a, ha, isCompactOperator_singularDirichletBaseResolvent q.val a⟩

/-- The complete original characteristic detects the ENTIRE spectrum. -/
theorem mem_originalDirichletSpectrum_iff_characteristic
    (q : OriginalHminusOnePotential) (lambda : ℂ) :
    lambda ∈ singularDirichletSpectrum q.val ↔ originalDirichletCharacteristic q lambda = 0 := by
  rw [mem_singularDirichletSpectrum_iff,
    ← originalDirichletCharacteristic_eq_zero_iff_native_eigen]

/-- Every original full label is in the actual operator spectrum. -/
theorem originalDirichletLabels_mem_spectrum (q : OriginalHminusOnePotential) (n : ℕ+) :
    (originalDirichletLabels q n:ℂ) ∈ singularDirichletSpectrum q.val :=
  (mem_originalDirichletSpectrum_iff_characteristic q _).mpr
    (originalDirichletLabels_is_root q n)

/-- All original Dirichlet labels, including the full central block, exhaust
the entire native spectrum. -/
theorem mem_originalDirichletSpectrum_iff_mem_labels
    (q : OriginalHminusOnePotential) (lambda : ℂ) :
    lambda ∈ singularDirichletSpectrum q.val ↔
      ∃ n : ℕ+, lambda = (originalDirichletLabels q n:ℂ) := by
  rw [mem_originalDirichletSpectrum_iff_characteristic, originalDirichletLabels_roots_iff]

/-- The entire native spectrum is precisely the range of the complete original labels. -/
theorem originalDirichletSpectrum_eq_range_labels (q : OriginalHminusOnePotential) :
    singularDirichletSpectrum q.val = range (fun n : ℕ+ => (originalDirichletLabels q n:ℂ)) := by
  ext lambda
  simp only [mem_originalDirichletSpectrum_iff_mem_labels, mem_range]
  exact exists_congr fun n => eq_comm

/-- Each bounded region contains finitely many full original Dirichlet spectral values. -/
theorem finite_originalDirichletSpectrum_norm_le (q : OriginalHminusOnePotential) (R : ℝ) :
    Set.Finite {z : ℂ | z ∈ singularDirichletSpectrum q.val ∧ ‖z‖ ≤ R} :=
  finite_singularDirichletSpectrum_norm_le q.val R

end NLS.Articles.KdVPseudomeasures
