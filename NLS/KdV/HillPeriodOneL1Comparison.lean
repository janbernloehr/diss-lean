import NLS.SequenceSpaces.PeriodOneL1Inclusion
import NLS.Fourier.PeriodOneSynthesisAlgebra
import NLS.KdV.ClassicalHillTraceFamily
import NLS.KdV.HminusOneDirichletNorming

/-! Literal unit-period continuous-potential realization of the dense L1
coefficient source. Both the ACTUAL characteristic and the canonical
norming terminal agree with the independently normalized physical IVP. -/
noncomputable section
open scoped ENNReal
open Set Complex NLS.LinearVolterra NLS.Fourier NLS.ZakharovShabat
namespace NLS.KdV

def periodOneL1PhysicalCoefficients : Coeff 1 →L[ℂ] Coeff 2 :=
  (Coeff.periodDouble (p := 2)).toContinuousLinearMap.comp
    (Coeff.exponentInclusion (by norm_num : (1:ℝ≥0∞) ≤ 2))

def periodOneL1PotentialCurve : Coeff 1 →L[ℂ] Curve ℂ :=
  hillUnitPotentialCurveCLM.comp periodOneSynthesisCLM

@[simp] theorem periodOneL1PotentialCurve_apply (a : Coeff 1) (t : Icc (0:ℝ) 1) :
    periodOneL1PotentialCurve a t = periodOneSynthesis a t := rfl

theorem hillContinuousCoefficients_periodOneSynthesis (a : Coeff 1) :
    SpectralWeight.one.toCoeff (hillContinuousCoefficients (periodOneSynthesisCLM a)) =
      Coeff.periodDouble (Coeff.exponentInclusion (by norm_num : (1:ℝ≥0∞) ≤ 2) a) := by
  ext k
  simp only [SpectralWeight.toCoeff_apply,hillContinuousCoefficients_apply]
  change fourierCoeff (continuousSynthesis (Coeff.periodDouble a)) k =
    Coeff.periodDouble (Coeff.exponentInclusion (by norm_num : (1:ℝ≥0∞) ≤ 2) a) k
  rw [fourierCoeff_continuousSynthesis]
  by_cases hk : k%2=0
  · have he : k=2*(k/2) := by omega
    rw [he,Coeff.periodDouble_even,Coeff.periodDouble_even,Coeff.exponentInclusion_apply]
  · have he : k=2*(k/2)+1 := by omega
    rw [he,Coeff.periodDouble_odd,Coeff.periodDouble_odd]


theorem hillL2DirichletTerminal_periodOneL1_eq_classical (a : Coeff 1) (μ : ℂ) :
    hillL2DirichletTerminal
      (Coeff.periodDouble (Coeff.exponentInclusion (by norm_num : (1:ℝ≥0∞) ≤ 2) a)) μ =
      classicalHillDirichletTerminal (periodOneL1PotentialCurve a) μ := by
  rw [← hillContinuousCoefficients_periodOneSynthesis,hillL2DirichletTerminal_eq_classical]
  rfl

theorem hillHminusDirichlet_eq_classical_L1 (a : Coeff 1) (μ : ℂ) :
    hillHminusDirichlet (periodOneL1Inclusion a) μ =
      classicalHillDirichlet (periodOneL1PotentialCurve a) μ := by
  rw [periodOneL1Inclusion,ContinuousLinearMap.comp_apply,hillHminusDirichlet_eq_hillL2,
    ← hillContinuousCoefficients_periodOneSynthesis,hillL2Dirichlet_eq_classical]
  rfl

theorem hillHminusDirichletNorming_eq_classical_L1 (n : ℕ+) (a : Coeff 1)
    (ha : periodOneL1Inclusion a ∈ hillHminusCanonicalDirichletDomain) :
    hillHminusDirichletNorming n (periodOneL1Inclusion a) =
      classicalHillDirichletTerminal (periodOneL1PotentialCurve a)
        (hillHminusCanonicalDirichlet n (periodOneL1Inclusion a)) := by
  rw [periodOneL1Inclusion,ContinuousLinearMap.comp_apply] at ha ⊢
  rw [hillHminusDirichletNorming_eq_hillL2 n _ ha,
    ← hillContinuousCoefficients_periodOneSynthesis,hillL2DirichletTerminal_eq_classical]
  rfl

end NLS.KdV
