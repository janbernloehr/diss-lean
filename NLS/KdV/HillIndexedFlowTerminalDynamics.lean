import NLS.KdV.HillIndexedLocalFlow
import NLS.KdV.HillIndexedDirichletVariations
import NLS.KdV.HillIndexedSheetVariations

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

/-- The actual moving Dirichlet labels along a constructed indexed flow have
exactly the diagonal sheet velocity, including at endpoints and collapsed gaps. -/
theorem hasDerivAt_hillDirichletEnergy_indexed_integralCurve
    (n k : ℕ) (hn : 1≤n) (hk : 1≤k) (γ : ℝ → hillRealSourceSubmodule) (t : ℝ)
    (hγ : HasDerivAt γ (hillRealIndexedDiscriminantField k hk (γ t)) t) :
    HasDerivAt (fun τ => (hillDirichletEnergy (γ τ).val (γ τ).property.1 (γ τ).property.2 n hn : ℂ))
      (if n=k then hillDirichletSheetRoot (SpectralWeight.one.toCoeff (γ t).val)
        (hillDirichletEnergy (γ t).val (γ t).property.1 (γ t).property.2 n hn)/2 else 0) t := by
  let q : RealPeriodOneHillPotential := ⟨(γ t).val,(γ t).property⟩
  obtain ⟨a,ha,_,_,hmatch,hD⟩ := exists_hillDirichletBranch_indexedDiscriminantSource_variations q n hn
  have hd := physical_germ_deriv_on_indexed_curve k hk γ t hγ a ha
    (fun p => (hillDirichletEnergy p.val p.property.1 p.property.2 n hn : ℂ)) hmatch
  exact hD k hk ▸ hd

/-- The physical log-norming coordinates satisfy their exact spectral-curve ODE
along each actual indexed source trajectory, without sheet division. -/
theorem hasDerivAt_hillLogMultiplier_indexed_integralCurve
    (n k : ℕ) (hn : 1≤n) (hk : 1≤k) (γ : ℝ → hillRealSourceSubmodule) (t : ℝ)
    (hγ : HasDerivAt γ (hillRealIndexedDiscriminantField k hk (γ t)) t) :
    HasDerivAt (fun τ => (hillDirichletLogMultiplier (γ τ).val (γ τ).property.1 (γ τ).property.2 n hn : ℂ))
      (if n=k then deriv (hillL2Discriminant (SpectralWeight.one.toCoeff (γ t).val))
        (hillDirichletEnergy (γ t).val (γ t).property.1 (γ t).property.2 n hn)/2 else 0) t := by
  let q : RealPeriodOneHillPotential := ⟨(γ t).val,(γ t).property⟩
  obtain ⟨F,hF,hmatch,hD⟩ := exists_hillLogNorming_indexedDiscriminantSource_variations q n hn
  have hd := physical_germ_deriv_on_indexed_curve k hk γ t hγ F hF
    (fun p => (hillDirichletLogMultiplier p.val p.property.1 p.property.2 n hn : ℂ)) hmatch
  exact hD k hk ▸ hd

/-- The actual terminal sheet obeys the filled spectral-curve ODE on an indexed
trajectory even where that sheet is zero. -/
theorem hasDerivAt_hillDirichletSheet_indexed_integralCurve
    (n k : ℕ) (hn : 1≤n) (hk : 1≤k) (γ : ℝ → hillRealSourceSubmodule) (t : ℝ)
    (hγ : HasDerivAt γ (hillRealIndexedDiscriminantField k hk (γ t)) t) :
    HasDerivAt (fun τ => hillDirichletSheetRoot (SpectralWeight.one.toCoeff (γ τ).val)
        (hillDirichletEnergy (γ τ).val (γ τ).property.1 (γ τ).property.2 n hn))
      (if n=k then hillL2Discriminant (SpectralWeight.one.toCoeff (γ t).val)
          (hillDirichletEnergy (γ t).val (γ t).property.1 (γ t).property.2 n hn)*
        deriv (hillL2Discriminant (SpectralWeight.one.toCoeff (γ t).val))
          (hillDirichletEnergy (γ t).val (γ t).property.1 (γ t).property.2 n hn)/2 else 0) t := by
  let q : RealPeriodOneHillPotential := ⟨(γ t).val,(γ t).property⟩
  obtain ⟨S,hS,hmatch,hD⟩ := exists_hillDirichletSheet_indexedDiscriminantSource_variations q n hn
  have hd := physical_germ_deriv_on_indexed_curve k hk γ t hγ S hS
    (fun p => hillDirichletSheetRoot (SpectralWeight.one.toCoeff p.val)
      (hillDirichletEnergy p.val p.property.1 p.property.2 n hn)) hmatch
  exact hD k hk ▸ hd

/-- All unselected Dirichlet labels stay fixed on the actual spectral trajectory. -/
theorem hillDirichletEnergy_eq_on_other_indexed_integralCurve
    (n k : ℕ) (hn : 1≤n) (hk : 1≤k) (hnk : n≠k)
    (γ : ℝ → hillRealSourceSubmodule) (a b : ℝ)
    (hγ : ∀ t∈Ioo a b, HasDerivAt γ (hillRealIndexedDiscriminantField k hk (γ t)) t)
    (u v : ℝ) (hu : u∈Ioo a b) (hv : v∈Ioo a b) :
    hillDirichletEnergy (γ u).val (γ u).property.1 (γ u).property.2 n hn=
      hillDirichletEnergy (γ v).val (γ v).property.1 (γ v).property.2 n hn := by
  have hd (t : ℝ) (ht : t∈Ioo a b) :=
    hasDerivAt_hillDirichletEnergy_indexed_integralCurve n k hn hk γ t (hγ t ht)
  simp only [if_neg hnk] at hd
  have he := isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo a b).isPreconnected
    (fun t ht => (hd t ht).differentiableAt.differentiableWithinAt)
    (fun t ht => (hd t ht).deriv) hu hv
  exact Complex.ofReal_injective he

end NLS.KdV
