import NLS.KdV.HillIndexedFlowTerminalDynamics
import NLS.KdV.HillIsospectralGapInvariants
import NLS.KdV.HillLocalGapPhysicalMatching

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.LinearVolterra NLS.FunctionalAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



/-- Pull an actual physically matched analytic germ through an original
indexed real Hill trajectory. -/
theorem hillPhysicalGerm_hasDerivAt_on_indexedCurve
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

/-- Both physical symmetric gap invariants are stationary on every actual
indexed trajectory, including collapsed gaps. -/
theorem hasDerivAt_hillGapSymmetricData_indexed_integralCurve
    (n k : ℕ) (hn : 1≤n) (hk : 1≤k) (γ : ℝ → hillRealSourceSubmodule) (t : ℝ)
    (hγ : HasDerivAt γ (hillRealIndexedDiscriminantField k hk (γ t)) t) :
    HasDerivAt (fun τ => (hillRealGapCenter (γ τ).val (γ τ).property.1 (γ τ).property.2 n : ℂ)) 0 t ∧
    HasDerivAt (fun τ => (2*(hillRealGapHalfLength (γ τ).val (γ τ).property.1 (γ τ).property.2 n : ℂ))^2) 0 t := by
  let q : RealPeriodOneHillPotential := ⟨(γ t).val,(γ t).property⟩
  obtain ⟨U,_,hqU,hM,hS,_⟩ := exists_hillLocalGapSymmetricData_analytic_neighborhood q.val q.property.1 q.property.2 n hn
  obtain ⟨W,hW,hqW,hmatch⟩ := exists_hillLocalGapSymmetricData_physical_neighborhood q.val q.property.1 q.property.2 n hn
  have hz := hillLocalGapSymmetricData_isospectral_fderiv q.val q.property.1 q.property.2 n hn
    (SpectralWeight.one.toCoeff (hillIndexedDiscriminantHamiltonianSource q k hk))
    (hillIndexedDiscriminantHamiltonianSource_isospectral q k hk)
  have hdM := hillPhysicalGerm_hasDerivAt_on_indexedCurve k hk γ t hγ
    (hillLocalGapMidpoint q.val q.property.1 q.property.2 n) (hM _ hqU)
    (fun p => (hillRealGapCenter p.val p.property.1 p.property.2 n : ℂ))
    (Filter.Eventually.mono (hW.mem_nhds hqW) (fun p hp => (hmatch p hp).1))
  have hdS := hillPhysicalGerm_hasDerivAt_on_indexedCurve k hk γ t hγ
    (hillLocalGapSquare q.val q.property.1 q.property.2 n) (hS _ hqU)
    (fun p => (2*(hillRealGapHalfLength p.val p.property.1 p.property.2 n : ℂ))^2)
    (Filter.Eventually.mono (hW.mem_nhds hqW) (fun p hp => (hmatch p hp).2))
  exact ⟨hz.1 ▸ hdM,hz.2 ▸ hdS⟩

/-- The actual center and half-length of every physical gap are constant
on each indexed trajectory, with no gap-opening assumption. -/
theorem hillGapGeometry_eq_on_indexed_integralCurve
    (n k : ℕ) (hn : 1≤n) (hk : 1≤k) (γ : ℝ → hillRealSourceSubmodule) (a b : ℝ)
    (hγ : ∀ t∈Ioo a b, HasDerivAt γ (hillRealIndexedDiscriminantField k hk (γ t)) t)
    (u v : ℝ) (hu : u∈Ioo a b) (hv : v∈Ioo a b) :
    hillRealGapCenter (γ u).val (γ u).property.1 (γ u).property.2 n=
      hillRealGapCenter (γ v).val (γ v).property.1 (γ v).property.2 n ∧
    hillRealGapHalfLength (γ u).val (γ u).property.1 (γ u).property.2 n=
      hillRealGapHalfLength (γ v).val (γ v).property.1 (γ v).property.2 n := by
  have hd (t : ℝ) (ht : t∈Ioo a b) := hasDerivAt_hillGapSymmetricData_indexed_integralCurve n k hn hk γ t (hγ t ht)
  have hm := isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo a b).isPreconnected
    (fun t ht => (hd t ht).1.differentiableAt.differentiableWithinAt)
    (fun t ht => (hd t ht).1.deriv) hu hv
  have hs := isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo a b).isPreconnected
    (fun t ht => (hd t ht).2.differentiableAt.differentiableWithinAt)
    (fun t ht => (hd t ht).2.deriv) hu hv
  refine ⟨Complex.ofReal_injective hm,?_⟩
  have hsR : (2*hillRealGapHalfLength (γ u).val (γ u).property.1 (γ u).property.2 n)^2=
      (2*hillRealGapHalfLength (γ v).val (γ v).property.1 (γ v).property.2 n)^2 := by exact_mod_cast hs
  have hdu := (hillRealGapContour_geometry (γ u).val (γ u).property.1 (γ u).property.2 n hn).1
  have hdv := (hillRealGapContour_geometry (γ v).val (γ v).property.1 (γ v).property.2 n hn).1
  nlinarith

/-- Each actual Dirichlet energy remains in a fixed bounded physical gap
throughout an indexed trajectory. -/
theorem hillDirichletEnergy_bound_on_indexed_integralCurve
    (n k : ℕ) (hn : 1≤n) (hk : 1≤k) (γ : ℝ → hillRealSourceSubmodule) (a b : ℝ)
    (hγ : ∀ t∈Ioo a b, HasDerivAt γ (hillRealIndexedDiscriminantField k hk (γ t)) t)
    (u : ℝ) (hu : u∈Ioo a b) :
    ∀ t∈Ioo a b,
      ‖(hillDirichletEnergy (γ t).val (γ t).property.1 (γ t).property.2 n hn : ℂ)‖≤
        |hillRealGapCenter (γ u).val (γ u).property.1 (γ u).property.2 n|+
          hillRealGapHalfLength (γ u).val (γ u).property.1 (γ u).property.2 n := by
  intro t ht
  have hg := hillGapGeometry_eq_on_indexed_integralCurve n k hn hk γ a b hγ u t hu ht
  have hmem := hillDirichletEnergy_mem_gap (γ t).val (γ t).property.1 (γ t).property.2 n hn
  have hm : |hillDirichletEnergy (γ t).val (γ t).property.1 (γ t).property.2 n hn-
      hillRealGapCenter (γ t).val (γ t).property.1 (γ t).property.2 n|≤
      hillRealGapHalfLength (γ t).val (γ t).property.1 (γ t).property.2 n := by
    apply abs_le.mpr
    dsimp only [hillRealGapCenter,hillRealGapHalfLength]
    constructor <;> linarith [hmem.1,hmem.2]
  rw [←hg.1,←hg.2] at hm
  have hbnd := abs_le.mp hm
  rw [norm_real,Real.norm_eq_abs]
  apply abs_le.mpr
  constructor <;> linarith [le_abs_self (hillRealGapCenter (γ u).val (γ u).property.1 (γ u).property.2 n),
    neg_abs_le (hillRealGapCenter (γ u).val (γ u).property.1 (γ u).property.2 n)]

end NLS.KdV
