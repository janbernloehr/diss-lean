import NLS.SequenceSpaces.SobolevBilinearPairing
import NLS.ZakharovShabat.SobolevHierarchyOperations
import NLS.ZakharovShabat.PeriodOneSobolevHamiltonian
import NLS.ZakharovShabat.ClassicalNLSFourthHamiltonian
import NLS.Fourier.SmoothPeriodOneCoefficientAlgebra

/-! # The physical fourth Hamiltonian on H^(3/2)

The third derivative is paired distributionally with the original H^(3/2)
field. The quartic interaction uses the H¹ cubic product and the L² first
derivative. Both are bounded polynomial constructions, without spectral data.
-/
noncomputable section
set_option autoImplicit false
open Complex Set NLS.Fourier
open scoped ContDiff
namespace NLS.ZakharovShabat

/-- Unit-period differentiation on the full real Sobolev scale. -/
def periodOneSobolevDerivative (s t : ℝ) (h : t+1 ≤ s) :
    WeightedCoeff (Weight.sobolev s) 2 →L[ℂ] WeightedCoeff (Weight.sobolev t) 2 :=
  (2 : ℂ) • ((WeightedCoeff.sobolevDerivative t).comp (WeightedCoeff.sobolevInclusion h))

@[simp] theorem periodOneSobolevDerivative_apply (s t : ℝ) (h : t+1 ≤ s)
    (a : WeightedCoeff (Weight.sobolev s) 2) (n : ℤ) :
    (periodOneSobolevDerivative s t h a).val n = 2*I*(Real.pi:ℂ)*n*a.val n := by
  change (2:ℂ)*(I*(Real.pi:ℂ)*n*(WeightedCoeff.sobolevInclusion h a).val n) = _
  rw [WeightedCoeff.sobolevInclusion_apply]
  ring

/-- The original fractional physical field domain. -/
abbrev FourthSobolevField := WeightedCoeff (Weight.sobolev (3/2)) 2
abbrev FourthSobolevSource := FourthSobolevField × FourthSobolevField

/-- The third physical derivative, with loss of exactly three Sobolev orders. -/
def fourthSobolevThirdDerivative :
    FourthSobolevField →L[ℂ] WeightedCoeff (Weight.sobolev (-(3/2))) 2 :=
  (periodOneSobolevDerivative (-1/2) (-(3/2)) (by norm_num)).comp
    ((periodOneSobolevDerivative (1/2) (-1/2) (by norm_num)).comp
      (periodOneSobolevDerivative (3/2) (1/2) (by norm_num)))

@[simp] theorem fourthSobolevThirdDerivative_apply (a : FourthSobolevField) (n : ℤ) :
    (fourthSobolevThirdDerivative a).val n = (2*I*(Real.pi:ℂ)*n)^3*a.val n := by
  simp only [fourthSobolevThirdDerivative,ContinuousLinearMap.comp_apply,
    periodOneSobolevDerivative_apply]
  ring

/-- Include in H¹ without changing any physical Fourier coefficient. -/
def fourthSobolevToH1 : FourthSobolevField →L[ℂ] ScalarSobolev 1 :=
  WeightedCoeff.sobolevInclusion (by norm_num)

@[simp] theorem fourthSobolevToH1_apply (a : FourthSobolevField) (n : ℤ) :
    (fourthSobolevToH1 a).val n = a.val n := WeightedCoeff.sobolevInclusion_apply _ _ _

/-- The first physical derivative as an L² sequence. -/
def fourthSobolevFirstDerivative : FourthSobolevField →L[ℂ] Coeff 2 :=
  (WeightedCoeff.sobolevToL2 (s := (0 : ℕ)) (Nat.cast_nonneg 0)).comp
    ((hierarchySobolevDerivative 1 0 (by norm_num)).comp fourthSobolevToH1)

@[simp] theorem fourthSobolevFirstDerivative_apply (a : FourthSobolevField) (n : ℤ) :
    fourthSobolevFirstDerivative a n = 2*I*(Real.pi:ℂ)*n*a.val n := by
  simp only [fourthSobolevFirstDerivative,ContinuousLinearMap.comp_apply,
    WeightedCoeff.sobolevToL2_apply,hierarchySobolevDerivative_apply,fourthSobolevToH1_apply]

/-- The physical cubic a²b, realized in unweighted L² coefficients. -/
def fourthSobolevCubic (ab : FourthSobolevSource) : Coeff 2 :=
  WeightedCoeff.sobolevToL2 (s := (0 : ℕ)) (Nat.cast_nonneg 0)
    (hierarchySobolevTriple 0 (fourthSobolevToH1 ab.1) (fourthSobolevToH1 ab.1)
      (fourthSobolevToH1 ab.2))

/-- The distributional leading term and the ordinary quartic interaction,
with the original physical i and -3 factors. -/
def periodOneSobolevFourthHamiltonian (ab : FourthSobolevSource) : ℂ :=
  I*(WeightedCoeff.sobolevBilinearPairing (3/2) ab.1 (fourthSobolevThirdDerivative ab.2)-
    3*Coeff.dualPairing (Coeff.reflection (fourthSobolevCubic ab))
      (fourthSobolevFirstDerivative ab.2))

/-- The cubic physical product depends holomorphically on the fractional field. -/
theorem analyticAt_fourthSobolevCubic (ab : FourthSobolevSource) :
    AnalyticAt ℂ fourthSobolevCubic ab := by
  have ha : AnalyticAt ℂ (fun cd : FourthSobolevSource => fourthSobolevToH1 cd.1) ab :=
    (fourthSobolevToH1.analyticAt _).comp analyticAt_fst
  have hb : AnalyticAt ℂ (fun cd : FourthSobolevSource => fourthSobolevToH1 cd.2) ab :=
    (fourthSobolevToH1.analyticAt _).comp analyticAt_snd
  exact ((WeightedCoeff.sobolevToL2 (s := (0 : ℕ)) (Nat.cast_nonneg 0)).analyticAt _).comp
    (analyticAt_hierarchySobolevTriple 0 ha ha hb)

/-- Physical H₄ is entire complex analytic at the article's H^(3/2) regularity. -/
theorem analyticAt_periodOneSobolevFourthHamiltonian (ab : FourthSobolevSource) :
    AnalyticAt ℂ periodOneSobolevFourthHamiltonian ab := by
  have hlead := ((WeightedCoeff.sobolevBilinearPairing (p := 2) (q := 2) (3/2)).analyticAt_bilinear
    (ab.1,fourthSobolevThirdDerivative ab.2)).comp
      (f := fun cd : FourthSobolevSource => (cd.1,fourthSobolevThirdDerivative cd.2))
      (analyticAt_fst.prod ((fourthSobolevThirdDerivative.analyticAt _).comp analyticAt_snd))
  have hc := (Coeff.reflection.toContinuousLinearEquiv.analyticAt _).comp
    (analyticAt_fourthSobolevCubic ab)
  have hd := (fourthSobolevFirstDerivative.analyticAt _).comp (analyticAt_snd (p := ab))
  have hquart := (Coeff.dualPairing.analyticAt_bilinear _).comp
    (f := fun cd : FourthSobolevSource =>
      (Coeff.reflection (fourthSobolevCubic cd),fourthSobolevFirstDerivative cd.2))
    (hc.prod hd)
  exact analyticAt_const.mul (hlead.sub (analyticAt_const.mul hquart))

/-- The original fractional source norm controls continuity of the physical Hamiltonian. -/
theorem continuous_periodOneSobolevFourthHamiltonian :
    Continuous periodOneSobolevFourthHamiltonian :=
  continuous_iff_continuousAt.mpr fun ab => (analyticAt_periodOneSobolevFourthHamiltonian ab).continuousAt

end NLS.ZakharovShabat
