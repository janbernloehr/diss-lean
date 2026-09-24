import NLS.ZakharovShabat.SourceDeletedPairOmittedSquare
import NLS.ZakharovShabat.SourceStandardRootOmittedJointAnalytic
import NLS.ComplexAnalysis.JointSpectralDerivative

/-!
# Joint analyticity of the deleted periodic-pair product

On the omitted-root domain, the deleted pair product is the square
of the jointly analytic omitted standard-root product. Consequently
its spectral derivative is jointly continuous. This is the local
regularity needed to bound the central critical-offset coefficients.
-/

noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The canonical deleted periodic product as a joint spectral and
source function. -/
def sourceDeletedPairJointProduct (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n : ℤ) : ℂ × CoeffPair p → ℂ :=
  fun t => canonicalDeletedPeriodicProduct hp hp1
    (periodOnePotential t.2) (periodOnePotential_mem t.2) n t.1

/-- Joint analyticity follows from the omitted-root square identity
on any open source set where the omitted product is jointly analytic. -/
theorem sourceDeletedPairJointProduct_analyticOnNhd_of_omitted
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (W : Set (CoeffPair p)) (n : ℤ)
    (hDopen : IsOpen (sourceStandardRootOmittedJointDomain hp hp1 W n))
    (hO : AnalyticOnNhd ℂ (sourceStandardRootOmittedJointProduct hp hp1 n)
      (sourceStandardRootOmittedJointDomain hp hp1 W n)) :
    AnalyticOnNhd ℂ (sourceDeletedPairJointProduct hp hp1 n)
      (sourceStandardRootOmittedJointDomain hp hp1 W n) := by
  let D := sourceStandardRootOmittedJointDomain hp hp1 W n
  have heq : D.EqOn
      (fun t => (sourceStandardRootOmittedJointProduct hp hp1 n t)^2)
      (sourceDeletedPairJointProduct hp hp1 n) := by
    intro t ht
    exact sourceStandardRootOmittedProduct_sq_eq_canonicalDeletedPeriodicProduct
      hp hp1 t.2 n t.1 ht.2
  exact (hO.pow 2).congr hDopen heq

/-- The spectral derivative of the deleted periodic pair product is
jointly continuous on the same omitted-root domain. -/
theorem continuousOn_sourceDeletedPairJointSpectralDerivative
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (W : Set (CoeffPair p)) (n : ℤ)
    (hDopen : IsOpen (sourceStandardRootOmittedJointDomain hp hp1 W n))
    (hO : AnalyticOnNhd ℂ (sourceStandardRootOmittedJointProduct hp hp1 n)
      (sourceStandardRootOmittedJointDomain hp hp1 W n)) :
    ContinuousOn (fun t : ℂ × CoeffPair p =>
      deriv (canonicalDeletedPeriodicProduct hp hp1
        (periodOnePotential t.2) (periodOnePotential_mem t.2) n) t.1)
      (sourceStandardRootOmittedJointDomain hp hp1 W n) := by
  exact NLS.ComplexAnalysis.continuousOn_spectral_deriv_of_analyticOnNhd
    (sourceDeletedPairJointProduct hp hp1 n)
    (sourceStandardRootOmittedJointDomain hp hp1 W n) hDopen
    (sourceDeletedPairJointProduct_analyticOnNhd_of_omitted
      hp hp1 W n hDopen hO)

/-- One connected almost-real source domain supports joint
analyticity and continuous spectral derivatives for every deleted
periodic-pair product. -/
theorem exists_global_sourceDeletedPairJointAnalytic
    (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ IsConnected W ∧
      realTypeSourceLocus p ⊆ W ∧
      ∀ n : ℤ,
        IsOpen (sourceStandardRootOmittedJointDomain hp hp1 W n) ∧
        AnalyticOnNhd ℂ (sourceDeletedPairJointProduct hp hp1 n)
          (sourceStandardRootOmittedJointDomain hp hp1 W n) ∧
        ContinuousOn (fun t : ℂ × CoeffPair p =>
          deriv (canonicalDeletedPeriodicProduct hp hp1
            (periodOnePotential t.2) (periodOnePotential_mem t.2) n) t.1)
          (sourceStandardRootOmittedJointDomain hp hp1 W n) := by
  obtain ⟨W,hWopen,hWconn,hreal,hdata⟩ :=
    exists_global_source_analytic_omittedJointProduct hp hp1
  refine ⟨W,hWopen,hWconn,hreal,?_⟩
  intro n
  obtain ⟨hDopen,hO,_,_⟩ := hdata n
  exact ⟨hDopen,
    sourceDeletedPairJointProduct_analyticOnNhd_of_omitted hp hp1 W n hDopen hO,
    continuousOn_sourceDeletedPairJointSpectralDerivative hp hp1 W n hDopen hO⟩

end NLS.ZakharovShabat
