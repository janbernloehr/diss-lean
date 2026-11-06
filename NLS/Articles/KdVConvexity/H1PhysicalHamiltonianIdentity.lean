import NLS.Articles.KdVConvexity.FiniteH1PhysicalIdentity

/-! # Sobolev density extends the physical renormalized identity to every real H1 source -/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
namespace NLS.Articles.KdVConvexity
open NLS.KdV

/-- The smooth identity extends in the actual H1 norm. Both physical
energy and the original weighted linear action sum are continuous there,
and the raw action map is continuous in the original ell2 target norm. -/
theorem contourHamiltonian_eq_native_physical_H1
    (R : ℕ+ → BaseActionSpace → ℂ)
    (hH : ContinuousOn (contourHamiltonian R) positiveQuadrant)
    (hR : ∀ q : RealHillWeightedPotential hillH1SpectralWeight, q.val.val 0=0 → ∀ n : ℕ+,
      R n (baseActionInclusion (physicalHilbertActions hillH1SpectralWeight q)) =
        hillHminusRealGapCubicContourMoment (hillWeightedNativeHminusSource hillH1SpectralWeight q.val)
          (hillWeightedNativeHminusSource_real hillH1SpectralWeight q) n)
    (hsum : ∀ a ∈ positiveQuadrant, Summable (fun n => ‖weightedContourTerm R n (baseActionInclusion a)‖))
    (q : RealHillWeightedPotential hillH1SpectralWeight) (hm : q.val.val 0=0) :
    contourHamiltonian R (physicalHilbertActions hillH1SpectralWeight q) =
      hillNativeH1Hamiltonian q.val-hillH1LinearActionEnergy q := by
  let A := physicalHilbertActions hillH1SpectralWeight
  let F : RealHillWeightedPotential hillH1SpectralWeight → ℂ := fun p => contourHamiltonian R (A p)
  let G : RealHillWeightedPotential hillH1SpectralWeight → ℂ :=
    fun p => hillNativeH1Hamiltonian p.val-hillH1LinearActionEnergy p
  have hF : Continuous F := hH.comp_continuous (continuous_physicalHilbertActions hillH1SpectralWeight)
    (fun p => physicalHilbertActions_mem_positiveQuadrant hillH1SpectralWeight p)
  have hG : Continuous G :=
    (continuous_hillNativeH1Hamiltonian.comp continuous_subtype_val).sub continuous_hillH1LinearActionEnergy
  have ht := tendsto_hillRealWeightedTruncate hillH1SpectralWeight q
  have he (N : ℕ) : F (hillRealWeightedTruncate hillH1SpectralWeight N q)=
      G (hillRealWeightedTruncate hillH1SpectralWeight N q) :=
    contourHamiltonian_eq_native_physical_finite_H1 R hR hsum _
      (hillRealWeightedTruncate_mean_zero hillH1SpectralWeight N q hm)
      (hillRealTruncationFinsupp hillH1SpectralWeight N q)
      (hillRealWeightedTruncate_eq_ofFinsupp hillH1SpectralWeight N q)
  have hFlim := hF.continuousAt.tendsto.comp ht
  have hGlim : Tendsto (fun N => F (hillRealWeightedTruncate hillH1SpectralWeight N q))
      atTop (nhds (G q)) := (hG.continuousAt.tendsto.comp ht).congr' (Eventually.of_forall (fun N => (he N).symm))
  exact tendsto_nhds_unique hFlim hGlim

end NLS.Articles.KdVConvexity
