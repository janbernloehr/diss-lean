import NLS.KdV.HillStateSecondDerivative
import NLS.ComplexAnalysis.ScalarHillProductMagri

/-! # Weak Magri reduction at every actual rough Hill solution

The physical L² potential and original scalar IVP supply every coefficient
and derivative in the weak integral. Vanishing test endpoint values remove
the exact boundary term. The potential is never differentiated.
-/
noncomputable section
open Set Complex Filter Topology MeasureTheory
open NLS.LinearVolterra NLS.ZakharovShabat NLS.ComplexAnalysis NLS.FunctionalAnalysis
open scoped ENNReal
namespace NLS.KdV

def hillSolutionProductMagri (q : Coeff 2) (mu : ℂ) (v w : ℂ × ℂ) (g dg : Curve ℂ) : ℂ :=
  ∫ x in (0 : ℝ)..1, scalarHillProductMagriIntegrand (hillIntervalPotential q) mu
    (hillL2FrequencyStateCurve q (Complex.sqrt mu) v) (hillL2FrequencyStateCurve q (Complex.sqrt mu) w) g dg x

theorem hillSolutionProductMagri_eq_first (q : Coeff 2) (mu : ℂ) (v w : ℂ × ℂ) (g dg : Curve ℂ)
    (hg : AbsolutelyContinuousOnInterval (extend g) 0 1)
    (hdg : ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1), HasDerivAt (extend g) (extend dg x) x)
    (h0 : g ⟨0,by norm_num⟩ = 0) (h1 : g ⟨1,by norm_num⟩ = 0) :
    hillSolutionProductMagri q mu v w g dg =
      4*mu*(∫ x in (0 : ℝ)..1,
        (extend (hillL2FrequencyStateCurve q (Complex.sqrt mu) v) x).1*
          (extend (hillL2FrequencyStateCurve q (Complex.sqrt mu) w) x).1*extend dg x) := by
  have hd (u : ℂ × ℂ) : ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1),
      HasDerivAt (fun r => (extend (hillL2FrequencyStateCurve q (Complex.sqrt mu) u) r).1)
        (extend (hillL2FrequencyStateCurve q (Complex.sqrt mu) u) x).2 x ∧
      HasDerivAt (fun r => (extend (hillL2FrequencyStateCurve q (Complex.sqrt mu) u) r).2)
        ((hillIntervalPotential q x-mu)*(extend (hillL2FrequencyStateCurve q (Complex.sqrt mu) u) x).1) x := by
    filter_upwards [ae_hasDerivAt_hillL2FrequencyStateCurve_fst q (Complex.sqrt mu) u,
      ae_hasDerivAt_hillL2FrequencyStateCurve_snd q (Complex.sqrt mu) u] with x hx hy
    exact ⟨hx,by simpa only [complex_sqrt_sq] using hy⟩
  have he := integral_scalarHillProductMagri_eq (hillIntervalPotential q) mu _ _ g dg
    (memLp_hillIntervalPotential q) (absolutelyContinuousOnInterval_hillStateCurve q _ v)
    (absolutelyContinuousOnInterval_hillStateCurve q _ w) hg (hd v) (hd w) hdg
  have hg0 : extend g 0 = 0 := by
    simpa only [NLS.LinearVolterra.extend,projIcc_of_mem _ (show (0 : ℝ) ∈ Icc 0 1 by norm_num)] using h0
  have hg1 : extend g 1 = 0 := by
    simpa only [NLS.LinearVolterra.extend,projIcc_of_mem _ (show (1 : ℝ) ∈ Icc 0 1 by norm_num)] using h1
  simpa only [hillSolutionProductMagri,hg0,hg1,mul_zero,sub_self,sub_zero] using he

end NLS.KdV
