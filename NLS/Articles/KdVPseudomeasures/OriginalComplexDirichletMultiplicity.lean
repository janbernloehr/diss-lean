import NLS.KdV.SingularDirichletMultiplicityOrder
import NLS.Articles.KdVPseudomeasures.OriginalDirichletAlgebraicMultiplicity

/-! # Complex Dirichlet multiplicities on the full original distribution domain

Physical period one is retained as an explicit original distribution
condition. No reality, zero-mean, smoothness or distant-energy assumption
is needed for the multiplicity theorem. Extraction/insertion preserves the
ENTIRE original distribution on every smooth test.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
open NLS.KdV NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue

/-- The full complex physically period-one original H-minus-one domain,
allowing arbitrary mean. The article's complex mean-zero domain is included. -/
def OriginalComplexHminusOnePotential :=
  {q : FourierLebesgueSpace (2:ℝ) (-1) 2 // IsPeriodicDistribution 1 q.val.toTempered}

/-- The independently normalized scalar characteristic of the same original complex distribution. -/
def originalComplexDirichletCharacteristic (q : OriginalComplexHminusOnePotential) (lambda : ℂ) : ℂ :=
  hillHminusDirichlet (periodOneOriginalExtract q.val) lambda

/-- No original smooth-test value changes under the full complex source adapter. -/
theorem originalComplexDirichlet_distribution (q : OriginalComplexHminusOnePotential) :
    periodOneOriginal (periodOneOriginalExtract q.val) = q.val :=
  periodOneOriginal_extract q.val q.property

/-- The ENTIRE complex original native spectrum equals this original characteristic zero set. -/
theorem mem_originalComplexDirichletSpectrum_iff_characteristic
    (q : OriginalComplexHminusOnePotential) (lambda : ℂ) :
    lambda ∈ singularDirichletSpectrum q.val ↔ originalComplexDirichletCharacteristic q lambda = 0 := by
  have h := mem_singularDirichletSpectrum_source_iff (periodOneOriginalExtract q.val) lambda
  rw [originalComplexDirichlet_distribution q] at h
  exact h

/-- Full actual operator algebraic multiplicity equals normalized characteristic
order for EVERY complex original source and EVERY complex energy. -/
theorem originalComplexDirichletAlgebraicMultiplicity_eq_analyticOrderNatAt
    (q : OriginalComplexHminusOnePotential) (lambda : ℂ) :
    singularDirichletAlgebraicMultiplicity q.val lambda =
      analyticOrderNatAt (originalComplexDirichletCharacteristic q) lambda := by
  have h := singularDirichletAlgebraicMultiplicity_eq_analyticOrderNatAt
    (periodOneOriginalExtract q.val) lambda
  rw [originalComplexDirichlet_distribution q] at h
  exact h

theorem originalComplexDirichletAlgebraicMultiplicity_eq_analyticOrderAt
    (q : OriginalComplexHminusOnePotential) (lambda : ℂ) :
    (singularDirichletAlgebraicMultiplicity q.val lambda : ℕ∞) =
      analyticOrderAt (originalComplexDirichletCharacteristic q) lambda := by
  have h := singularDirichletAlgebraicMultiplicity_eq_analyticOrderAt
    (periodOneOriginalExtract q.val) lambda
  rw [originalComplexDirichlet_distribution q] at h
  exact h

/-- All actual finite root levels include exactly the truncated complex
algebraic multiplicity; complex associated vectors are not discarded. -/
theorem finrank_originalComplexDirichletRootSpace_eq_min_multiplicity
    (q : OriginalComplexHminusOnePotential) (lambda : ℂ) (N : ℕ) :
    Module.finrank ℂ (singularDirichletRootSpace q.val lambda N) =
      min N (singularDirichletAlgebraicMultiplicity q.val lambda) := by
  have h := finrank_singularDirichletRootSpace_eq_min_multiplicity
    (periodOneOriginalExtract q.val) lambda N
  rw [originalComplexDirichlet_distribution q] at h
  exact h

/-- The original real source is included without changing its distribution. -/
def originalHminusOnePotentialToComplex (q : OriginalHminusOnePotential) : OriginalComplexHminusOnePotential :=
  ⟨q.val,q.property.2.2⟩

theorem originalComplexDirichletCharacteristic_of_real (q : OriginalHminusOnePotential) (lambda : ℂ) :
    originalComplexDirichletCharacteristic (originalHminusOnePotentialToComplex q) lambda =
      originalDirichletCharacteristic q lambda := rfl

end NLS.Articles.KdVPseudomeasures
