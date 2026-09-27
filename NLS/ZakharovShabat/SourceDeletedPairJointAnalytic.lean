import NLS.ZakharovShabat.SourceDeletedPairOmittedSquare
import NLS.ZakharovShabat.SourceStandardRootOmittedJointAnalytic
import NLS.ComplexAnalysis.JointSpectralDerivative

/-!
# Joint analyticity of the deleted periodic-pair product

On the omitted-root domain, the deleted pair product is the square
of the jointly analytic omitted standard-root product. Its spectral
derivative is therefore jointly analytic as well. These facts give
the local regularity of the central critical-offset coefficients.
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

/-- The spectral derivative is in fact jointly analytic on the
omitted-root domain. This stronger regularity supports analytic
critical-gap coefficients, including when the selected gap is closed. -/
theorem sourceDeletedPairJointSpectralDerivative_analyticOnNhd_of_omitted
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (W : Set (CoeffPair p)) (n : ℤ)
    (hDopen : IsOpen (sourceStandardRootOmittedJointDomain hp hp1 W n))
    (hO : AnalyticOnNhd ℂ (sourceStandardRootOmittedJointProduct hp hp1 n)
      (sourceStandardRootOmittedJointDomain hp hp1 W n)) :
    AnalyticOnNhd ℂ (fun t : ℂ × CoeffPair p =>
      deriv (canonicalDeletedPeriodicProduct hp hp1
        (periodOnePotential t.2) (periodOnePotential_mem t.2) n) t.1)
      (sourceStandardRootOmittedJointDomain hp hp1 W n) := by
  let P := sourceDeletedPairJointProduct hp hp1 n
  let D := sourceStandardRootOmittedJointDomain hp hp1 W n
  have hP : AnalyticOnNhd ℂ P D :=
    sourceDeletedPairJointProduct_analyticOnNhd_of_omitted
      hp hp1 W n hDopen hO
  let ev : ((ℂ × CoeffPair p) →L[ℂ] ℂ) →L[ℂ] ℂ :=
    ContinuousLinearMap.apply ℂ ℂ (1,0)
  have hderiv : AnalyticOnNhd ℂ
      (fun t : ℂ × CoeffPair p => (fderiv ℂ P t) (1,0)) D :=
    ev.comp_analyticOnNhd hP.fderiv
  have heq : D.EqOn
      (fun t : ℂ × CoeffPair p => (fderiv ℂ P t) (1,0))
      (fun t => deriv (canonicalDeletedPeriodicProduct hp hp1
        (periodOnePotential t.2) (periodOnePotential_mem t.2) n) t.1) := by
    intro t ht
    symm
    exact NLS.ComplexAnalysis.deriv_spectral_section_eq_fderiv P t.1 t.2
      ((hP t ht).differentiableAt)
  exact hderiv.congr hDopen heq

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
