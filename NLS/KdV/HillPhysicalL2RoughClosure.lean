import NLS.KdV.HillOriginalHminusCompactness
import NLS.KdV.HillRoughPhysicalL2Reconstruction

/-! # Bounded original L2 approximants retain physical L2 rough limits

The existing compactness theorem keeps the limit in the ORIGINAL real L2
space. Uniqueness of the rough limit identifies its exact raw coefficients.
-/
noncomputable section
set_option autoImplicit false
open Set Filter Topology
namespace NLS.KdV

theorem exists_original_physical_of_bounded_hminus_limit
    (q : PeriodOneHminusOne) (a : ℕ → RealPeriodOneHillPotential)
    (hb : Bornology.IsBounded (range (fun n => (a n).val)))
    (ht : Tendsto (fun n => hillOriginalHminusSource (a n).val) atTop (𝓝 q)) :
    ∃ p : RealPeriodOneHillPotential, hillOriginalHminusSource p.val=q := by
  obtain ⟨p,σ,hσ,hp⟩ := exists_hillRealSource_hminus_tendsto_subseq a hb
  exact ⟨p,tendsto_nhds_unique hp (ht.comp hσ.tendsto_atTop)⟩

theorem memlp_of_bounded_original_hminus_limit
    (q : PeriodOneHminusOne) (a : ℕ → RealPeriodOneHillPotential)
    (hb : Bornology.IsBounded (range (fun n => (a n).val)))
    (ht : Tendsto (fun n => hillOriginalHminusSource (a n).val) atTop (𝓝 q)) :
    Memℓp q.val 2 := by
  obtain ⟨p,hp⟩ := exists_original_physical_of_bounded_hminus_limit q a hb ht
  rw [←hp]
  have h := lp.memℓp (Fourier.paritySample 0 (SpectralWeight.one.toCoeff p.val))
  convert h using 1
  funext j
  rw [hillOriginalHminusSource_apply,hillUnitSample_apply,SpectralWeight.toCoeff_apply]

end NLS.KdV
