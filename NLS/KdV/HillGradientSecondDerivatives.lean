import NLS.KdV.HillLogNormingRegularity
import NLS.KdV.HillStateSecondDerivative

/-! # Actual second derivatives of the independent Hill cotangents

The Dirichlet-energy and log-norming cotangents are differentiated along
the actual rough scalar IVP. Their first derivatives are absolutely
continuous, and their second derivatives use only the L² potential.
-/
noncomputable section
open Set Complex Filter Topology MeasureTheory
open NLS.LinearVolterra NLS.ZakharovShabat NLS.ComplexAnalysis NLS.FunctionalAnalysis
open scoped ENNReal
namespace NLS.KdV

def hillDirichletGradientSecond (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1 ≤ n) (x : ℝ) : ℂ :=
  (scalarStateMass (hillDirichletStateCurve q n hn) : ℂ)⁻¹*
    (2*(extend (hillDirichletStateCurve q n hn) x).2^2+
      2*(hillIntervalPotential (SpectralWeight.one.toCoeff q.val) x-
        hillDirichletEnergy q.val q.property.1 q.property.2 n hn)*(extend (hillDirichletStateCurve q n hn) x).1^2)

def hillLogNormingGradientSecond (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1 ≤ n) (x : ℝ) : ℂ :=
  2*(extend (hillDirichletCosineCurve q n hn) x).2*(extend (hillDirichletStateCurve q n hn) x).2+
    2*(hillIntervalPotential (SpectralWeight.one.toCoeff q.val) x-
      hillDirichletEnergy q.val q.property.1 q.property.2 n hn)*
      (extend (hillDirichletCosineCurve q n hn) x).1*(extend (hillDirichletStateCurve q n hn) x).1-
    hillLogNormingProjection q n hn*(2*(extend (hillDirichletStateCurve q n hn) x).2^2+
      2*(hillIntervalPotential (SpectralWeight.one.toCoeff q.val) x-
        hillDirichletEnergy q.val q.property.1 q.property.2 n hn)*(extend (hillDirichletStateCurve q n hn) x).1^2)

theorem ae_hasDerivAt_hillDirichletGradientSpatialCurve (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1 ≤ n) :
    ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1),
      HasDerivAt (extend (hillDirichletGradientSpatialCurve q n hn)) (hillDirichletGradientSecond q n hn x) x := by
  let mu : ℂ := hillDirichletEnergy q.val q.property.1 q.property.2 n hn
  filter_upwards [ae_hasDerivAt_hillL2FrequencyStateCurve_fst (SpectralWeight.one.toCoeff q.val) (Complex.sqrt mu) (0,1),
    ae_hasDerivAt_hillL2FrequencyStateCurve_snd (SpectralWeight.one.toCoeff q.val) (Complex.sqrt mu) (0,1)] with x hx hy
  rw [complex_sqrt_sq] at hy
  have hd := (hx.mul hy).const_mul (2/(scalarStateMass (hillDirichletStateCurve q n hn) : ℂ))
  convert! hd using 1
  dsimp only [hillDirichletGradientSecond,hillDirichletStateCurve,mu]
  ring

theorem ae_hasDerivAt_hillLogNormingGradientSpatialCurve (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1 ≤ n) :
    ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1),
      HasDerivAt (extend (hillLogNormingGradientSpatialCurve q n hn)) (hillLogNormingGradientSecond q n hn x) x := by
  let mu : ℂ := hillDirichletEnergy q.val q.property.1 q.property.2 n hn
  filter_upwards [ae_hasDerivAt_hillL2FrequencyStateCurve_fst (SpectralWeight.one.toCoeff q.val) (Complex.sqrt mu) (1,0),
    ae_hasDerivAt_hillL2FrequencyStateCurve_snd (SpectralWeight.one.toCoeff q.val) (Complex.sqrt mu) (1,0),
    ae_hasDerivAt_hillL2FrequencyStateCurve_fst (SpectralWeight.one.toCoeff q.val) (Complex.sqrt mu) (0,1),
    ae_hasDerivAt_hillL2FrequencyStateCurve_snd (SpectralWeight.one.toCoeff q.val) (Complex.sqrt mu) (0,1)] with x hcf hcd hsf hsd
  rw [complex_sqrt_sq] at hcd hsd
  have hd := ((hcd.mul hsf).add (hcf.mul hsd)).sub
    ((hsf.mul hsd).const_mul (2*hillLogNormingProjection q n hn))
  convert! hd using 1
  dsimp only [hillLogNormingGradientSecond,hillDirichletStateCurve,hillDirichletCosineCurve,mu]
  ring

end NLS.KdV
