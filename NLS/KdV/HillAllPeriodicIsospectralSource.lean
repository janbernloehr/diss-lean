import NLS.KdV.HillMeanZeroIsospectralCompactness
import NLS.KdV.HillFiniteEndpointTransport

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.LinearVolterra NLS.FunctionalAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



/-- A zero physical log-norming coordinate lies at an actual periodic
endpoint, by strict signed trace inequality in every open gap interior. -/
theorem hillDirichletEnergy_endpoint_of_logMultiplier_zero
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1≤n)
    (hκ : hillDirichletLogMultiplier q.val q.property.1 q.property.2 n hn=0) :
    hillDirichletEnergy q.val q.property.1 q.property.2 n hn=
      hillRealLabels q.val q.property.1 q.property.2 (2*n-1) ∨
    hillDirichletEnergy q.val q.property.1 q.property.2 n hn=
      hillRealLabels q.val q.property.1 q.property.2 (2*n) := by
  have hm := hillDirichletEnergy_mem_gap q.val q.property.1 q.property.2 n hn
  have ht := (hillDirichletLogMultiplier_eq_zero_iff q.val q.property.1 q.property.2 n hn).mp hκ
  by_contra he
  push Not at he
  have hi := hillL2Discriminant_signed_gap_gt_two q.val q.property.1 q.property.2 n hn _
    ⟨lt_of_le_of_ne hm.1 he.1.symm,lt_of_le_of_ne hm.2 he.2⟩
  linarith

/-- Every original real mean-zero rough Hill source has an actual all-periodic
isospectral source in the same original space, with exactly its original norm.
It is obtained as a strong subsequential limit of actual finite endpoint
transports; no compactness or infinite transport premise is supplied. -/
theorem exists_hillAllPeriodicIsospectralSource
    (q : RealPeriodOneHillPotential) (hmean : q.val.val 0=0) :
    ∃ r : RealPeriodOneHillPotential,
      r.val.val 0=0 ∧ ‖r.val‖=‖q.val‖ ∧
      (∀ E : ℂ, hillL2Discriminant (SpectralWeight.one.toCoeff r.val) E=
        hillL2Discriminant (SpectralWeight.one.toCoeff q.val) E) ∧
      (∀ n : ℕ, ∀ hn : 1≤n,
        hillDirichletLogMultiplier r.val r.property.1 r.property.2 n hn=0) := by
  have hfinite (N : ℕ) := exists_hillFiniteEndpointTransport q hmean (Finset.Icc 1 N)
    (by intro n hn;exact (Finset.mem_Icc.mp hn).1)
  let a : ℕ → RealPeriodOneHillPotential := fun N => (hfinite N).choose
  have ha (N : ℕ) := (hfinite N).choose_spec
  obtain ⟨r,hrmean,hrΔ,hrnorm,σ,hσ,hconv⟩ := exists_hillMeanZeroIsospectral_tendsto_subseq q hmean a
    (fun N => (ha N).1) (fun N => (ha N).2.2.1)
  have hsub : Tendsto (fun k => a (σ k)) atTop (𝓝 r) := tendsto_subtype_rng.mpr hconv
  refine ⟨r,hrmean,hrnorm,hrΔ,?_⟩
  intro n hn
  have hk := (continuous_hillDirichletLogMultiplier n hn).continuousAt.tendsto.comp hsub
  have hz : Tendsto (fun k => hillDirichletLogMultiplier (a (σ k)).val
      (a (σ k)).property.1 (a (σ k)).property.2 n hn) atTop (𝓝 (0 : ℝ)) := by
    apply tendsto_nhds_of_eventually_eq
    filter_upwards [eventually_ge_atTop n] with k hkn
    have hns : n∈Finset.Icc 1 (σ k) := Finset.mem_Icc.mpr ⟨hn,hkn.trans (hσ.id_le k)⟩
    exact ((ha (σ k)).2.2.2.2.1 n hn hns).1
  exact tendsto_nhds_unique hk hz

/-- Every original mean-zero rough Hill source admits a simultaneous actual
periodic terminal for every positive index on its original isospectral set,
with the original source norm and all original labelled endpoints retained. -/
theorem exists_hillSimultaneousPeriodicTerminals
    (q : RealPeriodOneHillPotential) (hmean : q.val.val 0=0) :
    ∃ r : RealPeriodOneHillPotential,
      r.val.val 0=0 ∧ ‖r.val‖=‖q.val‖ ∧
      (∀ E : ℂ, hillL2Discriminant (SpectralWeight.one.toCoeff r.val) E=
        hillL2Discriminant (SpectralWeight.one.toCoeff q.val) E) ∧
      (∀ n : ℕ, ∀ hn : 1≤n,
        hillDirichletLogMultiplier r.val r.property.1 r.property.2 n hn=0 ∧
        hillDirichletSheetRoot (SpectralWeight.one.toCoeff r.val)
          (hillDirichletEnergy r.val r.property.1 r.property.2 n hn)=0 ∧
        (hillDirichletEnergy r.val r.property.1 r.property.2 n hn=
          hillRealLabels q.val q.property.1 q.property.2 (2*n-1) ∨
         hillDirichletEnergy r.val r.property.1 r.property.2 n hn=
          hillRealLabels q.val q.property.1 q.property.2 (2*n))) := by
  obtain ⟨r,hrmean,hrnorm,hrΔ,hrκ⟩ := exists_hillAllPeriodicIsospectralSource q hmean
  have hlabels := hillRealLabels_eq_of_discriminant_eq r q hrΔ
  refine ⟨r,hrmean,hrnorm,hrΔ,?_⟩
  intro n hn
  refine ⟨hrκ n hn,(hillDirichletSheetRoot_eq_zero_iff_logMultiplier_eq_zero r n hn).mpr
    (hrκ n hn),?_⟩
  simpa only [hlabels] using hillDirichletEnergy_endpoint_of_logMultiplier_zero r n hn (hrκ n hn)

end NLS.KdV
