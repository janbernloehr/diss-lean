import NLS.MKdV.MiuraNLSActionsCartesianChart
import NLS.MKdV.MiuraRestrictedActionBrackets
import NLS.ZakharovShabat.ScalarRealL2Density

/-! # Zero mean closes the central original NLS action on original L2 -/
noncomputable section
open Set Complex Filter Topology NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

/-- The central NLS action vanishes at every physical original-L2
zero-mean profile, by mean-preserving finite Fourier approximation. -/
theorem miuraOriginalNLSActionSequence_zero_of_mean_zero (a : Coeff 2)
    (ha : ∀ j, a j = conj (a (-j))) (hm : a 0 = 0) : miuraOriginalNLSActionSequence a 0 = 0 := by
  let F : Coeff 2 → ℂ := fun b => miuraOriginalNLSActionSequence b 0
  have hF : ContinuousAt F a := (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 1 0).continuous.continuousAt.comp
    (analyticOnNhd_miuraOriginalNLSActionSequence a (real_mem_miuraOriginalNLSActionDomain a ha)).continuousAt
  have he (N : ℕ) : F (scalarInclusion (scalarL2H1Approx a N)) = 0 := by
    let b := scalarL2H1Approx a N
    have hb := scalarL2H1Approx_real a ha N
    have hb0 : b.val 0 = 0 := by simp [b,scalarL2H1Approx_coefficient,hm]
    have hbr : ∀ j, scalarInclusion b j = conj (scalarInclusion b (-j)) := by
      intro j; simpa only [scalarInclusion_apply] using hb j
    change miuraOriginalNLSActionSequence (scalarInclusion b) 0 = 0
    rw [miuraOriginalNLSActionSequence_apply _ (real_mem_miuraOriginalNLSActionDomain _ hbr)]
    change miuraRestrictedNLSAction 0 (scalarInclusion b) = 0
    rw [miuraRestrictedNLSAction_eq_original b hb]
    exact (miuraNLSAction_zero_iff_mean_zero b hb).mpr hb0
  have hlim := hF.tendsto.comp (tendsto_scalarInclusion_scalarL2H1Approx a)
  exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (Eventually.of_forall (fun N => (he N).symm)))

end NLS.MKdV
