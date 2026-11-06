import NLS.KdV.HillCartesianFiniteInvariant
import NLS.KdV.HillIntrinsicCartesianBracketContinuity
import NLS.KdV.HillAllPeriodicIsospectralSource

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ZakharovShabat
namespace NLS.KdV

/-- Actual finite transports and ORIGINAL L2 isospectral compactness
produce an all-periodic source preserving the intrinsic normalized
ORIGINAL Cartesian bracket. Every transport and limiting condition is proved. -/
theorem exists_hillAllPeriodicIsospectralSource_preserving_normalized_bracket
    (q : RealPeriodOneHillPotential) (hmean : q.val.val 0 = 0)
    (n m : ℕ+) (σ τ : Bool)
    (hgapn : hillRealGapHalfLength q.val q.property.1 q.property.2 n ≠ 0)
    (hgapm : hillRealGapHalfLength q.val q.property.1 q.property.2 m ≠ 0) :
    ∃ r : RealPeriodOneHillPotential,
      r.val.val 0 = 0 ∧ ‖r.val‖ = ‖q.val‖ ∧
      (∀ E : ℂ, hillL2Discriminant (SpectralWeight.one.toCoeff r.val) E =
        hillL2Discriminant (SpectralWeight.one.toCoeff q.val) E) ∧
      (∀ k : ℕ, ∀ hk : 1 ≤ k, hillDirichletLogMultiplier r.val r.property.1 r.property.2 k hk = 0) ∧
      hillIntrinsicNormalizedCartesianBracket n m σ τ r =
        hillIntrinsicNormalizedCartesianBracket n m σ τ q := by
  have hfinite (N : ℕ) := exists_hillFiniteEndpointTransport_preserving_normalized_bracket
    q hmean n m σ τ hgapn hgapm (Finset.Icc 1 N) (by intro k hk; exact (Finset.mem_Icc.mp hk).1)
  let a : ℕ → RealPeriodOneHillPotential := fun N => (hfinite N).choose
  have ha (N : ℕ) := (hfinite N).choose_spec
  obtain ⟨r,hrmean,hrΔ,hrnorm,ρ,hρ,hconv⟩ := exists_hillMeanZeroIsospectral_tendsto_subseq q hmean a
    (fun N => (ha N).1) (fun N => (ha N).2.2.1)
  have hsub : Tendsto (fun k => a (ρ k)) atTop (𝓝 r) := tendsto_subtype_rng.mpr hconv
  have hlabels := hillRealLabels_eq_of_discriminant_eq r q hrΔ
  have hrn : hillRealGapHalfLength r.val r.property.1 r.property.2 n ≠ 0 := by
    unfold hillRealGapHalfLength
    rw [hlabels]
    exact hgapn
  have hrm : hillRealGapHalfLength r.val r.property.1 r.property.2 m ≠ 0 := by
    unfold hillRealGapHalfLength
    rw [hlabels]
    exact hgapm
  refine ⟨r,hrmean,hrnorm,hrΔ,?_,?_⟩
  · intro k hk
    have ht := (continuous_hillDirichletLogMultiplier k hk).continuousAt.tendsto.comp hsub
    have hz : Tendsto (fun j => hillDirichletLogMultiplier (a (ρ j)).val
        (a (ρ j)).property.1 (a (ρ j)).property.2 k hk) atTop (𝓝 (0 : ℝ)) := by
      apply tendsto_nhds_of_eventually_eq
      filter_upwards [eventually_ge_atTop k] with j hj
      have hks : k ∈ Finset.Icc 1 (ρ j) := Finset.mem_Icc.mpr ⟨hk,hj.trans (hρ.id_le j)⟩
      exact ((ha (ρ j)).2.2.2.2.1 k hk hks).1
    exact tendsto_nhds_unique ht hz
  · have ht := (continuousAt_hillIntrinsicNormalizedCartesianBracket r n m σ τ hrn hrm).tendsto.comp hsub
    have hz : Tendsto (fun j => hillIntrinsicNormalizedCartesianBracket n m σ τ (a (ρ j))) atTop
        (𝓝 (hillIntrinsicNormalizedCartesianBracket n m σ τ q)) := by
      apply tendsto_nhds_of_eventually_eq
      exact Eventually.of_forall (fun j => (ha (ρ j)).2.2.2.2.2.2)
    exact tendsto_nhds_unique ht hz

end NLS.KdV
