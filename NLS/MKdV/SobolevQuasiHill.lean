import NLS.MKdV.QuasiHillZSComparison
import NLS.MKdV.QuasiHillPhysicalEquation
import NLS.ZakharovShabat.ClassicalSobolevPotential
import NLS.Fourier.PeriodOneSobolev

/-! # The independent Miura–Hill construction on the original period-one H¹ space

Even insertion is used only to reuse the existing period-two Fourier
representative. The resulting physical function has period one and retains
the original coefficients and derivative symbol 2*pi*i*n.
-/
noncomputable section
open Set Complex MeasureTheory NLS.LinearVolterra NLS.Fourier NLS.ZakharovShabat
namespace NLS.MKdV

/-- The actual continuous period-one representative of the original H¹ input. -/
def periodOneMiuraCurve (a : ScalarDomain 2) : Curve ℂ :=
  sobolevUnitCurve (Coeff.periodDoubleSobolev a)

@[simp] theorem periodOneMiuraCurve_apply (a : ScalarDomain 2) (t : Icc (0 : ℝ) 1) :
    periodOneMiuraCurve a t = periodOneSobolevSynthesis a (t.val : AddCircle (2 : ℝ)) := by
  rw [periodOneSobolevSynthesis_eq]
  rfl

theorem periodOneMiuraCurve_endpoints (a : ScalarDomain 2) :
    periodOneMiuraCurve a ⟨1,by constructor <;> norm_num⟩ =
      periodOneMiuraCurve a ⟨0,by constructor <;> norm_num⟩ := by
  simp only [periodOneMiuraCurve_apply]
  simpa only [zero_add] using periodOneSobolevSynthesis_periodic a 0

/-- The independently defined quasi-Hill discriminant for the original H¹ source. -/
def periodOneMiuraDiscriminant (a : ScalarDomain 2) (μ : ℂ) : ℂ :=
  quasiHillDiscriminant (periodOneMiuraCurve a) μ

/-- The independent trace identity holds on every complex H¹ source and
includes the zero spectral parameter. The separate physical scalar equation
is certified below; the weak Hill operator identification remains separate. -/
theorem periodOneMiuraDiscriminant_eq_ZS (a : ScalarDomain 2) (z : ℂ) :
    periodOneMiuraDiscriminant a (z^2) =
      classicalDiscriminant (classicalSobolevPotential
        (Coeff.periodDoubleSobolev a,Coeff.periodDoubleSobolev a)) z :=
  quasiHillDiscriminant_eq_ZS (periodOneMiuraCurve a) _ (by intro t; rfl) z

/-- Each independent H¹ Miura–Hill column satisfies the physical second-order
equation almost everywhere, with the actual Fourier Sobolev derivative. -/
theorem periodOneMiuraSolution_scalar_equation_ae
    (a : ScalarDomain 2) (μ : ℂ) (v : ℂ × ℂ) :
    ∀ᵐ x : ℝ, x ∈ Ioo (0 : ℝ) 1 →
      -deriv (deriv (fun y => (quasiHillSolution (periodOneMiuraCurve a) μ v y).1)) x+
        miuraPotential (fun y => periodOneSobolevSynthesis a (y : AddCircle (2 : ℝ))) x*
          (quasiHillSolution (periodOneMiuraCurve a) μ v x).1 =
            μ*(quasiHillSolution (periodOneMiuraCurve a) μ v x).1 :=
  quasiHillSolution_scalar_equation_ae (periodOneMiuraCurve a)
    (fun y => periodOneSobolevSynthesis a (y : AddCircle (2 : ℝ)))
    (periodOneMiuraCurve_apply a) (absolutelyContinuous_periodOneSobolevSynthesis a) μ v

end NLS.MKdV
