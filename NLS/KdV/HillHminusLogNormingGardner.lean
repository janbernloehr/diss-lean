import NLS.KdV.HillHminusLogNormingCotangent
import NLS.KdV.HillLogNormingGardnerBrackets
import NLS.Fourier.ACPeriodicUnitCoefficients

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology MeasureTheory
namespace NLS.KdV

/-- The genuine H-minus-one Gardner bracket of any physically matched
analytic log-norming germs is exactly the original physical bracket. -/
theorem hillLogNormings_hminus_Gardner_eq_physical
    (q : RealPeriodOneHillPotential) (n m : ℕ) (hn : 1≤n) (hm : 1≤m)
    (k l : PeriodOneHminusOne → ℂ)
    (hk : AnalyticAt ℂ k (hillOriginalHminusSource q.val))
    (hl : AnalyticAt ℂ l (hillOriginalHminusSource q.val))
    (hkm : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      k (hillOriginalHminusSource p.val)=
        (hillDirichletLogMultiplier p.val p.property.1 p.property.2 n hn : ℂ))
    (hlm : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      l (hillOriginalHminusSource p.val)=
        (hillDirichletLogMultiplier p.val p.property.1 p.property.2 m hm : ℂ)) :
    NLS.Poisson.hminusGardnerBracket k l (hillOriginalHminusSource q.val)=
      hillLogNormingGardnerBracket q n m hn hm := by
  have hp : NLS.LinearVolterra.extend (hillLogNormingGradientCurve q m hm) 1=
      NLS.LinearVolterra.extend (hillLogNormingGradientCurve q m hm) 0 := by
    rw [show NLS.LinearVolterra.extend (hillLogNormingGradientCurve q m hm) 1=
        hillLogNormingGradientCurve q m hm ⟨1,by norm_num⟩ from NLS.LinearVolterra.extend_coe _ ⟨1,by norm_num⟩,
      show NLS.LinearVolterra.extend (hillLogNormingGradientCurve q m hm) 0=
        hillLogNormingGradientCurve q m hm ⟨0,by norm_num⟩ from NLS.LinearVolterra.extend_coe _ ⟨0,by norm_num⟩,
      (hillLogNormingGradientCurve_endpoints q m hm).1,
      (hillLogNormingGradientCurve_endpoints q m hm).2]
  unfold NLS.Poisson.hminusGardnerBracket
  rw [Fourier.gardnerBivector_eq_integral_of_ac_coefficients _ _
    (NLS.LinearVolterra.extend (hillLogNormingGradientCurve q n hn))
    (NLS.LinearVolterra.extend (hillLogNormingGradientCurve q m hm))
    (NLS.LinearVolterra.extend (hillLogNormingGradientSpatialCurve q m hm))
    (NLS.LinearVolterra.continuous_extend _) (NLS.LinearVolterra.continuous_extend _)
    (NLS.LinearVolterra.continuous_extend _)
    (absolutelyContinuousOnInterval_hillLogNormingGradientCurve q m hm)
    (ae_hasDerivAt_hillLogNormingGradientCurve q m hm) hp
    (hillLogNorming_hminus_gradient_coefficients q n hn k hk hkm)
    (hillLogNorming_hminus_gradient_coefficients q m hm l hl hlm)]
  unfold hillLogNormingGardnerBracket
  apply intervalIntegral.integral_congr_ae_restrict
  rw [uIoc_of_le (by norm_num : (0 : ℝ)≤1)]
  filter_upwards [ae_hasDerivAt_hillLogNormingGradientCurve q m hm] with x hx
  rw [hx.deriv]

/-- Actual physically matched analytic H-minus-one log-norming germs
Poisson commute at every original real rough source, including collapsed gaps. -/
theorem hillLogNormings_hminus_Gardner_commute
    (q : RealPeriodOneHillPotential) (n m : ℕ) (hn : 1≤n) (hm : 1≤m)
    (k l : PeriodOneHminusOne → ℂ)
    (hk : AnalyticAt ℂ k (hillOriginalHminusSource q.val))
    (hl : AnalyticAt ℂ l (hillOriginalHminusSource q.val))
    (hkm : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      k (hillOriginalHminusSource p.val)=
        (hillDirichletLogMultiplier p.val p.property.1 p.property.2 n hn : ℂ))
    (hlm : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      l (hillOriginalHminusSource p.val)=
        (hillDirichletLogMultiplier p.val p.property.1 p.property.2 m hm : ℂ)) :
    NLS.Poisson.hminusGardnerBracket k l (hillOriginalHminusSource q.val)=0 := by
  rw [hillLogNormings_hminus_Gardner_eq_physical q n m hn hm k l hk hl hkm hlm,
    hillLogNormingGardnerBracket_eq_zero]

end NLS.KdV
