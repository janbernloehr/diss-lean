import NLS.Articles.KdVPseudomeasures.OriginalComplexDirichletMultiplicity
import NLS.KdV.HminusOneDirichletComplexLabels
import NLS.KdV.HminusOneDirichletComplexRealLabels

/-! Source equation (6) on the ENTIRE ORIGINAL complex physically period-one
H^-1 distribution domain: the complete lexicographically ordered positive
Dirichlet sequence, with ACTUAL operator algebraic multiplicities and the
literal original n-times-l2 asymptotic. -/
noncomputable section
open Set
namespace NLS.Articles.KdVPseudomeasures
open NLS.KdV NLS.ComplexAnalysis NLS.Fourier

/-- Full original complex positive-index Dirichlet spectral labels. -/
def originalComplexDirichletLabels (q : OriginalComplexHminusOnePotential) : ℕ+ → ℂ :=
  hillHminusDirichletComplexLabels (periodOneOriginalExtract q.val)

/-- The ENTIRE original complex native spectrum, central and high, is exhausted. -/
theorem originalComplexDirichletLabels_spectrum_iff
    (q : OriginalComplexHminusOnePotential) (e : ℂ) :
    e ∈ singularDirichletSpectrum q.val ↔ ∃ n : ℕ+, originalComplexDirichletLabels q n = e := by
  have h := hillHminusDirichletComplexLabels_spectrum_iff (periodOneOriginalExtract q.val) e
  rw [originalComplexDirichlet_distribution q] at h
  exact h

/-- Every original label has precisely the source lexicographic order. -/
theorem monotone_originalComplexDirichletLabels (q : OriginalComplexHminusOnePotential) :
    Monotone (fun n : ℕ+ => complexLexKey (originalComplexDirichletLabels q n)) :=
  monotone_hillHminusDirichletComplexLabels (periodOneOriginalExtract q.val)

/-- Every ACTUAL original native algebraic multiplicity equals the exact
positive-index occurrence count, including all central associated vectors. -/
theorem originalComplexDirichletLabels_multiplicity
    (q : OriginalComplexHminusOnePotential) (e : ℂ) :
    (∑ᶠ n : ℕ+, if originalComplexDirichletLabels q n = e then (1:ℕ) else 0) =
      singularDirichletAlgebraicMultiplicity q.val e := by
  have h := hillHminusDirichletComplexLabels_multiplicity (periodOneOriginalExtract q.val) e
  rw [originalComplexDirichlet_distribution q] at h
  exact h

/-- The same occurrence count is the independently normalized original
characteristic zero order at every complex energy. -/
theorem originalComplexDirichletLabels_analytic_multiplicity
    (q : OriginalComplexHminusOnePotential) (e : ℂ) :
    (∑ᶠ n : ℕ+, if originalComplexDirichletLabels q n = e then (1:ℕ) else 0) =
      analyticOrderNatAt (originalComplexDirichletCharacteristic q) e := by
  rw [originalComplexDirichletLabels_multiplicity,
    originalComplexDirichletAlgebraicMultiplicity_eq_analyticOrderNatAt]

/-- Source equation (6): mu_n=n^2*pi^2+n*l2_n on the SAME original positive index. -/
theorem memlp_originalComplexDirichletLabels_inverseIndex_error
    (q : OriginalComplexHminusOnePotential) :
    Memℓp (fun n : ℕ+ =>
      (originalComplexDirichletLabels q n-((Real.pi:ℂ)*(n:ℕ))^2)/(n:ℕ)) 2 :=
  memlp_hillHminusDirichletComplexLabels_inverseIndex_error (periodOneOriginalExtract q.val)

/-- No value has infinitely many occurrences in the original complex list. -/
theorem finite_fiber_originalComplexDirichletLabels
    (q : OriginalComplexHminusOnePotential) (e : ℂ) :
    {n : ℕ+ | originalComplexDirichletLabels q n = e}.Finite :=
  finite_fiber_hillHminusDirichletComplexLabels (periodOneOriginalExtract q.val) e

/-- The literal source equation (6), with one l2 error sequence for ALL
positive indices, including every central eigenvalue. -/
theorem exists_l2_originalComplexDirichletLabels_error
    (q : OriginalComplexHminusOnePotential) :
    ∃ a : ℕ+ → ℂ, Memℓp a 2 ∧ ∀ n : ℕ+,
      originalComplexDirichletLabels q n = ((Real.pi:ℂ)*(n:ℕ))^2+(n:ℕ)*a n := by
  refine ⟨fun n => (originalComplexDirichletLabels q n-((Real.pi:ℂ)*(n:ℕ))^2)/(n:ℕ),
    memlp_originalComplexDirichletLabels_inverseIndex_error q,?_⟩
  intro n
  have hn : ((n:ℕ):ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt n.property)
  field_simp [hn]; ring

/-- Restriction to the original real article domain preserves its complete
previously proved positive sequence, with identical distribution and index. -/
theorem originalComplexDirichletLabels_of_real (q : OriginalHminusOnePotential) (n : ℕ+) :
    originalComplexDirichletLabels (originalHminusOnePotentialToComplex q) n =
      (originalDirichletLabels q n:ℂ) :=
  hillHminusDirichletComplexLabels_eq_real (originalPeriodOneCoefficients q)
    (originalPeriodOneCoefficients_real q) n

end NLS.Articles.KdVPseudomeasures
