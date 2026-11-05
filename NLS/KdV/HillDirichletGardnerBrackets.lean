import NLS.KdV.HillDirichletGradientCurves
import NLS.KdV.HillDirichletGradients

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open MeasureTheory NLS.LinearVolterra NLS.ZakharovShabat NLS.ComplexAnalysis NLS.FunctionalAnalysis
open scoped ComplexConjugate ENNReal

namespace NLS.KdV

theorem hillDirichletGradientCurve_endpoints
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1≤n) :
    hillDirichletGradientCurve q n hn ⟨0,by norm_num⟩=0 ∧
      hillDirichletGradientCurve q n hn ⟨1,by norm_num⟩=0 := by
  let A := hillDirichletStateCurve q n hn
  have h0 : (A ⟨0,by norm_num⟩).1=0 := by
    dsimp only [A,hillDirichletStateCurve]
    rw [hillL2FrequencyStateCurve_zero]
  have h1 : (A ⟨1,by norm_num⟩).1=0 := hillDirichletEnergy_zero q.val q.property.1 q.property.2 n hn
  constructor
  · change (scalarStateMass A : ℂ)⁻¹*(A ⟨0,by norm_num⟩).1^2=0
    rw [h0,zero_pow (by omega),mul_zero]
  · change (scalarStateMass A : ℂ)⁻¹*(A ⟨1,by norm_num⟩).1^2=0
    rw [h1,zero_pow (by omega),mul_zero]

theorem hillDirichletGradient_represents_branch
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1≤n) (a : Coeff 2 → ℂ)
    (ha : AnalyticAt ℂ a (SpectralWeight.one.toCoeff q.val))
    (ha0 : a (SpectralWeight.one.toCoeff q.val)=(hillDirichletEnergy q.val q.property.1 q.property.2 n hn : ℂ))
    (hz : ∀ᶠ p in 𝓝 (SpectralWeight.one.toCoeff q.val), hillL2DirichletCharacteristic p (a p)=0)
    (h : Coeff 2) :
    (fderiv ℂ a (SpectralWeight.one.toCoeff q.val)) h=
      ∫ x in (0 : ℝ)..1, -(hillPhysicalDirection h).ofLp.2 x*
        NLS.LinearVolterra.extend (hillDirichletGradientCurve q n hn) x := by
  have hf := hillDirichlet_branch_fderiv_integral (SpectralWeight.one.toCoeff q.val) q.property.2 a ha hz h
  rw [ha0] at hf
  rw [hf,div_eq_mul_inv,← intervalIntegral.integral_mul_const]
  apply intervalIntegral.integral_congr
  intro x _
  let A := hillDirichletStateCurve q n hn
  change (-(hillPhysicalDirection h).ofLp.2 x*(NLS.LinearVolterra.extend A x).1^2)*(scalarStateMass A : ℂ)⁻¹=
    -(hillPhysicalDirection h).ofLp.2 x*((scalarStateMass A : ℂ)⁻¹*(NLS.LinearVolterra.extend A x).1^2)
  ring

def hillDirichletGardnerBracket
    (q : RealPeriodOneHillPotential) (n m : ℕ) (hn : 1≤n) (hm : 1≤m) : ℂ :=
  ∫ x in (0 : ℝ)..1, NLS.LinearVolterra.extend (hillDirichletGradientCurve q n hn) x*
    deriv (NLS.LinearVolterra.extend (hillDirichletGradientCurve q m hm)) x

theorem hillDirichletGardnerBracket_eq_zero
    (q : RealPeriodOneHillPotential) (n m : ℕ) (hn : 1≤n) (hm : 1≤m) :
    hillDirichletGardnerBracket q n m hn hm=0 := by
  let A := hillDirichletStateCurve q n hn
  let B := hillDirichletStateCurve q m hm
  let c : ℂ := 2/((scalarStateMass A : ℂ)*(scalarStateMass B : ℂ))
  have hdiff : deriv (NLS.LinearVolterra.extend (hillDirichletGradientCurve q m hm))
      =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] NLS.LinearVolterra.extend (hillDirichletGradientSpatialCurve q m hm) := by
    filter_upwards [ae_hasDerivAt_hillDirichletGradientCurve q m hm] with x hx
    exact hx.deriv
  calc
    hillDirichletGardnerBracket q n m hn hm=
        ∫ x in (0 : ℝ)..1, NLS.LinearVolterra.extend (hillDirichletGradientCurve q n hn) x*
          NLS.LinearVolterra.extend (hillDirichletGradientSpatialCurve q m hm) x := by
      apply intervalIntegral.integral_congr_ae_restrict
      rw [uIoc_of_le (by norm_num : (0 : ℝ)≤1)]
      filter_upwards [hdiff] with x hx
      rw [hx]
    _ = c*scalarStateSquaredPairing A B := by
      rw [scalarStateSquaredPairing_eq_integral,← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro x _
      change ((scalarStateMass A : ℂ)⁻¹*(NLS.LinearVolterra.extend A x).1^2)*
        ((2/(scalarStateMass B : ℂ))*((NLS.LinearVolterra.extend B x).1*(NLS.LinearVolterra.extend B x).2))=
          c*((NLS.LinearVolterra.extend A x).1^2*(NLS.LinearVolterra.extend B x).1*(NLS.LinearVolterra.extend B x).2)
      dsimp only [c]
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring
    _ = 0 := by rw [scalarStateSquaredPairing_hillDirichletState_zero,mul_zero]

end NLS.KdV
