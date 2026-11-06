import NLS.KdV.HillHminusDirichletCotangent
import NLS.KdV.HillHminusLogNormingGardner

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology MeasureTheory
namespace NLS.KdV

/-- Exact original physical bracket of genuine H-minus-one Dirichlet-energy germs. -/
theorem hillDirichletEnergies_hminus_Gardner_eq_physical
    (q : RealPeriodOneHillPotential) (n m : ℕ) (hn : 1≤n) (hm : 1≤m)
    (k l : PeriodOneHminusOne → ℂ)
    (hk : AnalyticAt ℂ k (hillOriginalHminusSource q.val))
    (hl : AnalyticAt ℂ l (hillOriginalHminusSource q.val))
    (hkm : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      k (hillOriginalHminusSource p.val)=
        (hillDirichletEnergy p.val p.property.1 p.property.2 n hn : ℂ))
    (hlm : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      l (hillOriginalHminusSource p.val)=
        (hillDirichletEnergy p.val p.property.1 p.property.2 m hm : ℂ)) :
    NLS.Poisson.hminusGardnerBracket k l (hillOriginalHminusSource q.val)=
      hillDirichletGardnerBracket q n m hn hm := by
  have hp : NLS.LinearVolterra.extend (hillDirichletGradientCurve q m hm) 1=
      NLS.LinearVolterra.extend (hillDirichletGradientCurve q m hm) 0 := by
    rw [show NLS.LinearVolterra.extend (hillDirichletGradientCurve q m hm) 1=
        hillDirichletGradientCurve q m hm ⟨1,by norm_num⟩ from NLS.LinearVolterra.extend_coe _ ⟨1,by norm_num⟩,
      show NLS.LinearVolterra.extend (hillDirichletGradientCurve q m hm) 0=
        hillDirichletGradientCurve q m hm ⟨0,by norm_num⟩ from NLS.LinearVolterra.extend_coe _ ⟨0,by norm_num⟩,
      (hillDirichletGradientCurve_endpoints q m hm).1,
      (hillDirichletGradientCurve_endpoints q m hm).2]
  unfold NLS.Poisson.hminusGardnerBracket
  rw [Fourier.gardnerBivector_eq_integral_of_ac_coefficients _ _
    (NLS.LinearVolterra.extend (hillDirichletGradientCurve q n hn))
    (NLS.LinearVolterra.extend (hillDirichletGradientCurve q m hm))
    (NLS.LinearVolterra.extend (hillDirichletGradientSpatialCurve q m hm))
    (NLS.LinearVolterra.continuous_extend _) (NLS.LinearVolterra.continuous_extend _)
    (NLS.LinearVolterra.continuous_extend _)
    (absolutelyContinuousOnInterval_hillDirichletGradientCurve q m hm)
    (ae_hasDerivAt_hillDirichletGradientCurve q m hm) hp
    (hillDirichletEnergy_hminus_gradient_coefficients q n hn k hk hkm)
    (hillDirichletEnergy_hminus_gradient_coefficients q m hm l hl hlm)]
  unfold hillDirichletGardnerBracket
  apply intervalIntegral.integral_congr_ae_restrict
  rw [uIoc_of_le (by norm_num : (0 : ℝ)≤1)]
  filter_upwards [ae_hasDerivAt_hillDirichletGradientCurve q m hm] with x hx
  rw [hx.deriv]

/-- Genuine H-minus-one Dirichlet energies commute at every original real source. -/
theorem hillDirichletEnergies_hminus_Gardner_commute
    (q : RealPeriodOneHillPotential) (n m : ℕ) (hn : 1≤n) (hm : 1≤m)
    (k l : PeriodOneHminusOne → ℂ)
    (hk : AnalyticAt ℂ k (hillOriginalHminusSource q.val))
    (hl : AnalyticAt ℂ l (hillOriginalHminusSource q.val))
    (hkm : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      k (hillOriginalHminusSource p.val)=
        (hillDirichletEnergy p.val p.property.1 p.property.2 n hn : ℂ))
    (hlm : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      l (hillOriginalHminusSource p.val)=
        (hillDirichletEnergy p.val p.property.1 p.property.2 m hm : ℂ)) :
    NLS.Poisson.hminusGardnerBracket k l (hillOriginalHminusSource q.val)=0 := by
  rw [hillDirichletEnergies_hminus_Gardner_eq_physical q n m hn hm k l hk hl hkm hlm,
    hillDirichletGardnerBracket_eq_zero]

/-- Exact mixed bracket with the original physical norming normalization. -/
theorem hillDirichletLogNorming_hminus_Gardner_eq_physical
    (q : RealPeriodOneHillPotential) (n m : ℕ) (hn : 1≤n) (hm : 1≤m)
    (k l : PeriodOneHminusOne → ℂ)
    (hk : AnalyticAt ℂ k (hillOriginalHminusSource q.val))
    (hl : AnalyticAt ℂ l (hillOriginalHminusSource q.val))
    (hkm : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      k (hillOriginalHminusSource p.val)=
        (hillDirichletEnergy p.val p.property.1 p.property.2 n hn : ℂ))
    (hlm : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      l (hillOriginalHminusSource p.val)=
        (hillDirichletLogMultiplier p.val p.property.1 p.property.2 m hm : ℂ)) :
    NLS.Poisson.hminusGardnerBracket k l (hillOriginalHminusSource q.val)=
      hillDirichletLogGardnerBracket q n m hn hm := by
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
    (NLS.LinearVolterra.extend (hillDirichletGradientCurve q n hn))
    (NLS.LinearVolterra.extend (hillLogNormingGradientCurve q m hm))
    (NLS.LinearVolterra.extend (hillLogNormingGradientSpatialCurve q m hm))
    (NLS.LinearVolterra.continuous_extend _) (NLS.LinearVolterra.continuous_extend _)
    (NLS.LinearVolterra.continuous_extend _)
    (absolutelyContinuousOnInterval_hillLogNormingGradientCurve q m hm)
    (ae_hasDerivAt_hillLogNormingGradientCurve q m hm) hp
    (hillDirichletEnergy_hminus_gradient_coefficients q n hn k hk hkm)
    (hillLogNorming_hminus_gradient_coefficients q m hm l hl hlm)]
  unfold hillDirichletLogGardnerBracket
  apply intervalIntegral.integral_congr_ae_restrict
  rw [uIoc_of_le (by norm_num : (0 : ℝ)≤1)]
  filter_upwards [ae_hasDerivAt_hillLogNormingGradientCurve q m hm] with x hx
  rw [hx.deriv]

/-- The actual H-minus-one mixed matrix has the physical minus-one-half normalization. -/
theorem hillDirichletLogNorming_hminus_Gardner_eq
    (q : RealPeriodOneHillPotential) (n m : ℕ) (hn : 1≤n) (hm : 1≤m)
    (k l : PeriodOneHminusOne → ℂ)
    (hk : AnalyticAt ℂ k (hillOriginalHminusSource q.val))
    (hl : AnalyticAt ℂ l (hillOriginalHminusSource q.val))
    (hkm : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      k (hillOriginalHminusSource p.val)=
        (hillDirichletEnergy p.val p.property.1 p.property.2 n hn : ℂ))
    (hlm : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      l (hillOriginalHminusSource p.val)=
        (hillDirichletLogMultiplier p.val p.property.1 p.property.2 m hm : ℂ)) :
    NLS.Poisson.hminusGardnerBracket k l (hillOriginalHminusSource q.val)=if n=m then -(1/2 : ℂ) else 0 := by
  rw [hillDirichletLogNorming_hminus_Gardner_eq_physical q n m hn hm k l hk hl hkm hlm,
    hillDirichletLogGardnerBracket_eq]

end NLS.KdV
