import NLS.KdV.HillCharacteristicCircleData
import NLS.KdV.HillDirichletAnalyticAngles

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

/-- Characteristic sheeted Hill angles can be anchored at any prescribed
physical base angle, in particular at either periodic terminal endpoint. -/
theorem exists_hillDirichlet_analytic_characteristic_angle_at (k : ℕ) (hk : 1≤k)
    (hgap : hillRealGapHalfLength q hq hr k≠0) (e : ℂ)
    (hpoint : cosineGapPoint (hillRealGapCenter q hq hr k) (hillRealGapHalfLength q hq hr k) e=
      (hillDirichletEnergy q hq hr k hk : ℂ))
    (hsin : Complex.sin e=hillDirichletGapSine q hq hr k hk) :
    ∃ d μ S ε : Coeff 2 → ℂ,
      AnalyticAt ℂ d (SpectralWeight.one.toCoeff q) ∧
      AnalyticAt ℂ μ (SpectralWeight.one.toCoeff q) ∧
      AnalyticAt ℂ S (SpectralWeight.one.toCoeff q) ∧
      AnalyticAt ℂ ε (SpectralWeight.one.toCoeff q) ∧
      d (SpectralWeight.one.toCoeff q)=(hillRealGapHalfLength q hq hr k : ℂ) ∧
      μ (SpectralWeight.one.toCoeff q)=(hillDirichletEnergy q hq hr k hk : ℂ) ∧
      S (SpectralWeight.one.toCoeff q)=hillDirichletGapSine q hq hr k hk ∧
      ε (SpectralWeight.one.toCoeff q)=e ∧
      cosineGapPoint (hillRealGapCenter q hq hr k) (hillRealGapHalfLength q hq hr k) e=
        (hillDirichletEnergy q hq hr k hk : ℂ) ∧
      Complex.sin e=hillDirichletGapSine q hq hr k hk ∧
      (∀ᶠ p : Coeff 2 in 𝓝 (SpectralWeight.one.toCoeff q),
        d p≠0 ∧ (d p)^2=hillLocalGapSquare q hq hr k p/4 ∧
        hillL2DirichletCharacteristic p (μ p)=0 ∧
        cosineGapPoint (hillLocalGapMidpoint q hq hr k p) (d p) (ε p)=μ p ∧
        Complex.sin (ε p)=S p ∧
        S p=I*hillDirichletSheetRoot p (μ p)/(d p*hillLocalDeflatedComplexRoot q hq hr k (μ p,p))) ∧
      ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
        hillRealGapHalfLength p.val p.property.1 p.property.2 k≠0 ∧
        (ε (SpectralWeight.one.toCoeff p.val)).im=0 ∧
        cosineGapPoint (hillRealGapCenter p.val p.property.1 p.property.2 k)
          (hillRealGapHalfLength p.val p.property.1 p.property.2 k) (ε (SpectralWeight.one.toCoeff p.val))=
            (hillDirichletEnergy p.val p.property.1 p.property.2 k hk : ℂ) ∧
        Complex.sin (ε (SpectralWeight.one.toCoeff p.val))=hillDirichletGapSine p.val p.property.1 p.property.2 k hk := by
  obtain ⟨d,μ,S,hd,hμ,hS,hd0,hμ0,hS0,hcircle,hcomplex,hphysical⟩ :=
    exists_hillDirichlet_analytic_characteristic_circle_data q hq hr k hk hgap
  obtain ⟨U,_,hqU,hM,_,_⟩ := exists_hillLocalGapSymmetricData_analytic_neighborhood q hq hr k hk
  have hM0 := (hillLocalGapSymmetricData_eq_physical_of_geometry q hq hr q hq hr k hk
    (hillRealGapContour_band_bounds q hq hr k hk)
    (hillRealGapSegment_subset_intrinsic_contour_ball q hq hr k hk)).1
  obtain ⟨ε,hε,hε0,hterminal⟩ := exists_analytic_parametricCosine_terminal_with_sine
    (hillLocalGapMidpoint q hq hr k) d μ S (SpectralWeight.one.toCoeff q) e
    (hM _ hqU) hd hμ hS (hd0 ▸ ofReal_ne_zero.mpr hgap) (hS0.trans hsin.symm)
    (by rw [hM0,hd0,hμ0];exact hpoint) hcircle
  let P : RealPeriodOneHillPotential → Coeff 2 := fun p => SpectralWeight.one.toCoeff p.val
  have hP : Continuous P := SpectralWeight.one.toCoeff.continuous.comp continuous_subtype_val
  refine ⟨d,μ,S,ε,hd,hμ,hS,hε,hd0,hμ0,hS0,hε0,hpoint,hsin,?_,?_⟩
  · filter_upwards [hcomplex,hterminal] with p hp ht
    exact ⟨hp.1,hp.2.1,hp.2.2.1,ht.1,ht.2,hp.2.2.2⟩
  · filter_upwards [hphysical,hP.continuousAt.tendsto.eventually hterminal] with p hp ht
    have hpointp : cosineGapPoint (hillRealGapCenter p.val p.property.1 p.property.2 k)
        (hillRealGapHalfLength p.val p.property.1 p.property.2 k) (ε (P p)) =
          (hillDirichletEnergy p.val p.property.1 p.property.2 k hk : ℂ) := by
      rw [← hp.2.2.2.2,← hp.2.1]
      exact ht.1.trans hp.2.2.1
    have hsinp : Complex.sin (ε (P p)) = hillDirichletGapSine p.val p.property.1 p.property.2 k hk :=
      ht.2.trans hp.2.2.2.1
    exact ⟨hp.1,hillDirichlet_angle_im_eq_zero p.val p.property.1 p.property.2 k hk hp.1 _ hpointp hsinp,hpointp,hsinp⟩

end NLS.KdV
