import NLS.KdV.HillIndexedCartesian
import NLS.KdV.HillIndexedLocalFlow

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.ZakharovShabat NLS.FunctionalAnalysis NLS.LinearVolterra
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



private theorem physical_germ_deriv_on_indexed_curve
    (k : ℕ) (hk : 1≤k) (γ : ℝ → hillRealSourceSubmodule) (t : ℝ)
    (hγ : HasDerivAt γ (hillRealIndexedDiscriminantField k hk (γ t)) t)
    (G : Coeff 2 → ℂ) (hG : AnalyticAt ℂ G (SpectralWeight.one.toCoeff (γ t).val))
    (F : RealPeriodOneHillPotential → ℂ)
    (hmatch : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨(γ t).val,(γ t).property⟩ : RealPeriodOneHillPotential),
      G (SpectralWeight.one.toCoeff p.val)=F p) :
    HasDerivAt (fun τ => F ⟨(γ τ).val,(γ τ).property⟩)
      ((fderiv ℂ G (SpectralWeight.one.toCoeff (γ t).val))
        (SpectralWeight.one.toCoeff (hillIndexedDiscriminantHamiltonianSource
          ⟨(γ t).val,(γ t).property⟩ k hk))) t := by
  let P : hillRealSourceSubmodule →L[ℝ] Coeff 2 :=
    (SpectralWeight.one.toCoeff.restrictScalars ℝ).comp hillRealSourceSubmodule.subtypeL
  have hc := (hG.differentiableAt.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t
    (P.hasFDerivAt.comp_hasDerivAt t hγ)
  have hQ : Continuous (fun p : hillRealSourceSubmodule =>
      (⟨p.val,p.property⟩ : RealPeriodOneHillPotential)) := continuous_subtype_val.subtype_mk _
  have he := (hQ.continuousAt.comp hγ.continuousAt).tendsto.eventually hmatch
  exact hc.congr_of_eventuallyEq (Filter.EventuallyEq.symm he)

variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

include h0q h0r in
/-- The actual physical Cartesian coordinate obeys its exact indexed spectral ODE
on every genuine real trajectory, including zero terminal sheets and collapsed gaps. -/
theorem hasDerivAt_hillSpectralCartesian_indexed_integralCurve
    (n k : ℕ) (hn : 1≤n) (hk : 1≤k) (γ : ℝ → hillRealSourceSubmodule) (t : ℝ)
    (hγ : HasDerivAt γ (hillRealIndexedDiscriminantField k hk (γ t)) t) :
    HasDerivAt (fun τ => hillSpectralCartesian (γ τ).val (γ τ).property.1 (γ τ).property.2 n hn)
      (I*(hillAbelianSelectedGlobalPsi (γ t).val (γ t).property.1 (γ t).property.2 n hn
        (hillDirichletEnergy (γ t).val (γ t).property.1 (γ t).property.2 k hk)/2)*
          hillSpectralCartesian (γ t).val (γ t).property.1 (γ t).property.2 n hn) t := by
  obtain ⟨Z,hZ,hmatch,hD⟩ := exists_hillSpectralCartesian_indexedSource_variations
    (γ t).val (γ t).property.1 (γ t).property.2 h0q h0r n hn
  have hd := physical_germ_deriv_on_indexed_curve k hk γ t hγ Z hZ
    (fun p => hillSpectralCartesian p.val p.property.1 p.property.2 n hn) hmatch
  exact hD k hk ▸ hd

/-- Every actual physical gap moment is stationary along each indexed spectral trajectory. -/
theorem hasDerivAt_hillRealGapIntegral_indexed_integralCurve
    (n k : ℕ) (hn : 1≤n) (hk : 1≤k) (m : ℕ) (γ : ℝ → hillRealSourceSubmodule) (t : ℝ)
    (hγ : HasDerivAt γ (hillRealIndexedDiscriminantField k hk (γ t)) t) :
    HasDerivAt (fun τ => (hillRealGapIntegral (γ τ).val (γ τ).property.1 (γ τ).property.2 n m : ℂ)) 0 t := by
  let q : RealPeriodOneHillPotential := ⟨(γ t).val,(γ t).property⟩
  obtain ⟨V,hV,hqV,hmatch⟩ := exists_hillRealSourceMoments_physical_neighborhood q.val q.property.1 q.property.2 n hn
  have he : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      hillRealSourceMoment q.val q.property.1 q.property.2 n m (SpectralWeight.one.toCoeff p.val)=
        (hillRealGapIntegral p.val p.property.1 p.property.2 n m : ℂ) :=
    Filter.Eventually.mono (hV.mem_nhds hqV) (fun p hp => hmatch p hp m)
  have hd := physical_germ_deriv_on_indexed_curve k hk γ t hγ
    (hillRealSourceMoment q.val q.property.1 q.property.2 n m)
    (analyticAt_hillRealSourceMoment q.val q.property.1 q.property.2 n hn m)
    (fun p => (hillRealGapIntegral p.val p.property.1 p.property.2 n m : ℂ)) he
  have hz := hillRealSourceMoment_isospectral_fderiv q.val q.property.1 q.property.2 n hn m
    (SpectralWeight.one.toCoeff (hillIndexedDiscriminantHamiltonianSource q k hk))
    (hillIndexedDiscriminantHamiltonianSource_isospectral q k hk)
  exact hz ▸ hd

/-- All actual gap moments, including every physical action, are conserved on
the full open interval of an indexed real spectral curve. -/
theorem hillRealGapIntegral_eq_on_indexed_integralCurve
    (n k : ℕ) (hn : 1≤n) (hk : 1≤k) (m : ℕ) (γ : ℝ → hillRealSourceSubmodule) (a b : ℝ)
    (hγ : ∀ t∈Ioo a b, HasDerivAt γ (hillRealIndexedDiscriminantField k hk (γ t)) t)
    (u v : ℝ) (hu : u∈Ioo a b) (hv : v∈Ioo a b) :
    hillRealGapIntegral (γ u).val (γ u).property.1 (γ u).property.2 n m=
      hillRealGapIntegral (γ v).val (γ v).property.1 (γ v).property.2 n m := by
  have hd (t : ℝ) (ht : t∈Ioo a b) :=
    hasDerivAt_hillRealGapIntegral_indexed_integralCurve n k hn hk m γ t (hγ t ht)
  have he := isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo a b).isPreconnected
    (fun t ht => (hd t ht).differentiableAt.differentiableWithinAt)
    (fun t ht => (hd t ht).deriv) hu hv
  exact Complex.ofReal_injective he

end NLS.KdV
