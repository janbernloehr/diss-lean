import NLS.MKdV.SobolevQuasiHill
import NLS.MKdV.PhysicalHillDiscriminant

/-! # The physical discriminant identity on the original complex H¹ domain

The Hill discriminant uses scalar columns with actual position/derivative
initial conditions. The physical equation, absolute continuity and uniqueness
of these independent columns are proved in the shared library. The original
H¹ input is realized by the literal period-one Fourier series.
-/
noncomputable section
open Set Complex MeasureTheory NLS.LinearVolterra NLS.Fourier NLS.ZakharovShabat NLS.MKdV
namespace NLS.Articles.MKdVNLSHierarchies

/-- The physical Hill discriminant at the Miura potential of an original H¹ input. -/
def hillDiscriminant (a : ScalarDomain 2) (μ : ℂ) : ℂ :=
  physicalMiuraDiscriminant (periodOneMiuraCurve a) μ

/-- Theorem 5, p. 9: independent physical Hill and ZS discriminants, with the
full complex H¹ domain, squared spectral parameter and zero parameter included. -/
theorem theorem5_discriminant_identity (a : ScalarDomain 2) (z : ℂ) :
    hillDiscriminant a (z^2) =
      classicalDiscriminant (classicalSobolevPotential
        (Coeff.periodDoubleSobolev a,Coeff.periodDoubleSobolev a)) z := by
  rw [hillDiscriminant, physicalMiuraDiscriminant_eq_quasiHill (periodOneMiuraCurve a)
    (periodOneMiuraCurve_endpoints a)]
  exact periodOneMiuraDiscriminant_eq_ZS a z

/-- The independent physical Hill columns solve the actual Miura equation on
this domain. This is a proved construction property, not a spectral hypothesis. -/
theorem hill_column_spec (a : ScalarDomain 2) (μ : ℂ) (v : ℂ × ℂ) :
    let g := physicalMiuraSolution (periodOneMiuraCurve a) μ v
    AbsolutelyContinuousOnInterval g 0 1 ∧
      AbsolutelyContinuousOnInterval (deriv g) 0 1 ∧
      g 0 = v.1 ∧ deriv g 0 = v.2 ∧
      ∀ᵐ x : ℝ, x ∈ Ioo (0 : ℝ) 1 →
        -deriv (deriv g) x+
          miuraPotential (fun y => periodOneSobolevSynthesis a (y : AddCircle (2 : ℝ))) x*g x =
            μ*g x := by
  have h := physicalMiuraSolution_spec (periodOneMiuraCurve a)
    (fun y => periodOneSobolevSynthesis a (y : AddCircle (2 : ℝ)))
    (periodOneMiuraCurve_apply a) (absolutelyContinuous_periodOneSobolevSynthesis a) μ v
  exact ⟨h.1,h.2.1,physicalMiuraSolution_zero _ _ _,deriv_physicalMiuraSolution_zero _ _ _,h.2.2⟩

end NLS.Articles.MKdVNLSHierarchies
