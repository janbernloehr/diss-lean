import NLS.KdV.HillIndexedDiscriminantSources
import NLS.KdV.HillDirichletTraceCotangent
import NLS.KdV.HillPhysicalGermDerivativeUniqueness

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.ZakharovShabat NLS.FunctionalAnalysis NLS.LinearVolterra
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



/-- The actual energy-discriminant source evaluates a Dirichlet cotangent as the
original trace/Dirichlet Gardner bracket, with its zero boundary term. -/
theorem hillEnergyHamiltonianSource_dirichlet_pairing
    (q : RealPeriodOneHillPotential) (E : ℂ) (n : ℕ) (hn : 1≤n) :
    hillPhysicalDirectionPairing (SpectralWeight.one.toCoeff
      (hillEnergyHamiltonianSource (SpectralWeight.one.toCoeff q.val) E))
        (hillDirichletGradientCurve q n hn)=
      hillDiscriminantDirichletGardnerBracket q (Complex.sqrt E) n hn := by
  let f := NLS.LinearVolterra.extend (hillEnergyDiscriminantGradientCurve (SpectralWeight.one.toCoeff q.val) E)
  let g := NLS.LinearVolterra.extend (hillDirichletGradientCurve q n hn)
  have hF := hillEnergyDiscriminantGradient_H1 (SpectralWeight.one.toCoeff q.val) E
  have hG := hillDirichletGradient_H1 q n hn
  have hf : IntervalIntegrable (deriv f) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ)≤1)).mpr
      (hF.2.2.integrable (by norm_num))
  have hg : IntervalIntegrable (deriv g) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ)≤1)).mpr
      (hG.2.2.integrable (by norm_num))
  have hi := integral_mul_deriv_eq_complex hF.1 hG.1 hf hg
  have h0 : g 0=0 := by
    simpa only [g,NLS.LinearVolterra.extend,projIcc_of_mem _ (show (0 : ℝ)∈Icc 0 1 by norm_num)] using
      (hillDirichletGradientCurve_endpoints q n hn).1
  have h1 : g 1=0 := by
    simpa only [g,NLS.LinearVolterra.extend,projIcc_of_mem _ (show (1 : ℝ)∈Icc 0 1 by norm_num)] using
      (hillDirichletGradientCurve_endpoints q n hn).2
  change (∫ x in (0 : ℝ)..1,f x*deriv g x)=f 1*g 1-f 0*g 0-
    (∫ x in (0 : ℝ)..1,deriv f x*g x) at hi
  rw [h0,h1,mul_zero,mul_zero,sub_self,zero_sub] at hi
  have hA : unitComplexCurvePairing (hillEnergyDiscriminantGradientSpatialCurve (SpectralWeight.one.toCoeff q.val) E)
      (hillDirichletGradientCurve q n hn)=∫ x in (0 : ℝ)..1,deriv f x*g x := by
    rw [unitComplexCurvePairing_apply]
    apply intervalIntegral.integral_congr_ae_restrict
    rw [uIoc_of_le (by norm_num : (0 : ℝ)≤1)]
    filter_upwards [ae_hasDerivAt_hillEnergyDiscriminantGradientCurve (SpectralWeight.one.toCoeff q.val) E] with x hx
    change NLS.LinearVolterra.extend (hillEnergyDiscriminantGradientSpatialCurve (SpectralWeight.one.toCoeff q.val) E) x*g x=_
    rw [hx.deriv]
  have hB : unitComplexCurvePairing (hillEnergyDiscriminantGradientCurve (SpectralWeight.one.toCoeff q.val) E)
      (hillDirichletGradientSpatialCurve q n hn)=∫ x in (0 : ℝ)..1,f x*deriv g x := by
    rw [unitComplexCurvePairing_apply]
    apply intervalIntegral.integral_congr_ae_restrict
    rw [uIoc_of_le (by norm_num : (0 : ℝ)≤1)]
    filter_upwards [ae_hasDerivAt_hillDirichletGradientCurve q n hn] with x hx
    change f x*NLS.LinearVolterra.extend (hillDirichletGradientSpatialCurve q n hn) x=_
    rw [hx.deriv]
  rw [hillEnergyHamiltonianSource_pairing,←unitComplexCurvePairing_energy_dirichlet,hA,hB,hi]

/-- Exactly one actual Dirichlet label moves under the indexed isospectral source;
the velocity is half its physical terminal sheet, including at zero sheets. -/
theorem hillDirichletBranch_indexedDiscriminantSource_fderiv
    (q : RealPeriodOneHillPotential) (n k : ℕ) (hn : 1≤n) (hk : 1≤k)
    (a : Coeff 2 → ℂ) (ha : AnalyticAt ℂ a (SpectralWeight.one.toCoeff q.val))
    (ha0 : a (SpectralWeight.one.toCoeff q.val)=(hillDirichletEnergy q.val q.property.1 q.property.2 n hn : ℂ))
    (hz : ∀ᶠ p in 𝓝 (SpectralWeight.one.toCoeff q.val),hillL2DirichletCharacteristic p (a p)=0) :
    (fderiv ℂ a (SpectralWeight.one.toCoeff q.val))
      (SpectralWeight.one.toCoeff (hillIndexedDiscriminantHamiltonianSource q k hk))=
      if n=k then hillDirichletSheetRoot (SpectralWeight.one.toCoeff q.val)
        (hillDirichletEnergy q.val q.property.1 q.property.2 n hn)/2 else 0 := by
  rw [hillDirichletGradient_represents_branch q n hn a ha ha0 hz,←hillPhysicalDirectionPairing_apply]
  change hillPhysicalDirectionPairing (SpectralWeight.one.toCoeff (hillEnergyHamiltonianSource
      (SpectralWeight.one.toCoeff q.val) (hillDirichletEnergy q.val q.property.1 q.property.2 k hk)))
      (hillDirichletGradientCurve q n hn)=_
  rw [hillEnergyHamiltonianSource_dirichlet_pairing]
  by_cases hnk : n=k
  · subst k
    rw [if_pos rfl,hillDiscriminantDirichletGardnerBracket_diagonal]
  · rw [if_neg hnk]
    rw [hillDiscriminantDirichletGardnerBracket_eq]
    · change hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q.val)
        (hillDirichletEnergy q.val q.property.1 q.property.2 k hk)*_/_=0
      rw [hillDirichletEnergy_zero,zero_mul,zero_div]
    · rw [complex_sqrt_sq]
      exact hillDirichletEnergy_ne_of_ne q k n hk hn (Ne.symm hnk)

/-- Actual physical Dirichlet branches carry all indexed-source velocities simultaneously. -/
theorem exists_hillDirichletBranch_indexedDiscriminantSource_variations
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1≤n) :
    ∃ a : Coeff 2 → ℂ, AnalyticAt ℂ a (SpectralWeight.one.toCoeff q.val) ∧
      a (SpectralWeight.one.toCoeff q.val)=(hillDirichletEnergy q.val q.property.1 q.property.2 n hn : ℂ) ∧
      (∀ᶠ p in 𝓝 (SpectralWeight.one.toCoeff q.val),hillL2DirichletCharacteristic p (a p)=0) ∧
      (∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
        a (SpectralWeight.one.toCoeff p.val)=(hillDirichletEnergy p.val p.property.1 p.property.2 n hn : ℂ)) ∧
      ∀ k : ℕ, ∀ hk : 1≤k,
        (fderiv ℂ a (SpectralWeight.one.toCoeff q.val))
          (SpectralWeight.one.toCoeff (hillIndexedDiscriminantHamiltonianSource q k hk))=
          if n=k then hillDirichletSheetRoot (SpectralWeight.one.toCoeff q.val)
            (hillDirichletEnergy q.val q.property.1 q.property.2 n hn)/2 else 0 := by
  obtain ⟨a,ha,ha0,hz,hmatch⟩ := exists_hillDirichletEnergy_analytic_extension q n hn
  exact ⟨a,ha,ha0,hz,hmatch,fun k hk =>
    hillDirichletBranch_indexedDiscriminantSource_fderiv q n k hn hk a ha ha0 hz⟩

end NLS.KdV
