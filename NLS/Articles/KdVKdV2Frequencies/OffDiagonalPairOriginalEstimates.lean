import NLS.Articles.KdVKdV2Frequencies.OffDiagonalFrequencyPairCharts
import NLS.KdV.PhysicalOffDiagonalFrequencyEstimates

/-! Preserve the SAME actual physical chart and its original estimates
while pulling the smoothing packet through the global native inverse. -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.KdV NLS.ZakharovShabat
open NLS.Articles.KdVConvexity
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies

theorem exists_offDiagonalFrequencyPairChart_with_original_estimates (D : GlobalRoughAbelianForwardData)
    (β t : ℝ) (hβ : 0<β) (hβ1 : β<1) (ht : 0<t) (hβt : 2*t=1-β)
    (z0 : Coeff 2 × Coeff 2)
    (hz0 : z0∈Coeff.realPairLocus 2) :
    ∃ ε : ℝ, 0<ε ∧ ε<β ∧ ∃ P : OffDiagonalFrequencyPairChart D β t ε, z0∈P.domain ∧
      SourceLemma12_12Data (by norm_num) (by norm_num)
        P.physicalChart.psi.family.originalDomain P.physicalChart.psi.family.domain P.physicalChart.psi.family.roots := by
  obtain ⟨U,hU,hzU,Q,hQ,hmean,hmatch⟩ := exists_hillNative_pair_inverse D actionIndexEquiv
    t ht.le z0 hz0
  let J := periodOneSobolevImageInclusion t ht.le
  let R := fun z => J (Q z)
  have hRa : AnalyticOnNhd ℂ R U := by
    intro z hz
    exact (J.analyticAt _).comp (hQ z hz)
  have hreal (z : Coeff 2 × Coeff 2) (hz : z∈U) (hzr : z∈Coeff.realPairLocus 2) :
      IsRealPeriodOneHminusOne (R z) := by
    change IsRealPeriodOneHminusOne (J (Q z))
    rw [hmatch z hz hzr]
    exact nativeRealPairInverse_real D actionIndexEquiv t ht.le z hzr
  obtain ⟨ε,hε,hεβ,B,hqB,H⟩ := exists_physicalOffDiagonalFrequencyChart_with_original_estimates β t hβ hβ1 ht hβt (Q z0) (hreal z0 hzU hz0)
  obtain ⟨V,hV,hzV,hVU,hQV,packet,hpa,hpn,hpz,hpp⟩ :=
    exists_analytic_packet_pullback Q U hU hQ B.domain B.domain_open B.packet B.analytic_packet
      B.bound B.norm_packet (fun (b : Coeff 1) (j : ℤ) => b j)
      (fun n a => (Weight.sobolev (-(β-ε)) (n : ℤ) : ℂ)*B.physical.offDiagonalCorrection n (J a))
      B.nonpositive B.positive z0 hzU hqB
  have hmem (z : Coeff 2 × Coeff 2) (hz : z∈V) : R z∈B.physical.domain :=
    mem_of_subset_preimage J B.domain B.physical.domain B.domain_subset (Q z) (hQV z hz)
  have hzero (z : Coeff 2 × Coeff 2) (hz : z∈V) : (R z).val 0=0 := by
    rw [periodOneSobolevImageInclusion_apply]
    exact hmean z (hVU hz)
  have hsign (z : Coeff 2 × Coeff 2) (hz : z∈V) (hzr : z∈Coeff.realPairLocus 2) (j : ℤ) :
      (D.signed (R z)).val j=(signedPairToDeleted actionIndexEquiv z).val j/(Weight.sobolev (t-1/2) j : ℂ) := by
    change (D.signed (J (Q z))).val j=_
    rw [hmatch z (hVU hz) hzr]
    exact nativeRealPairInverse_signed_apply D actionIndexEquiv t ht.le z hzr j
  exact ⟨ε,hε,hεβ,⟨V,hV,R,hRa.mono hVU,hzero,(fun z hz hzr => hreal z (hVU hz) hzr),hsign,
    B.physical,hmem,packet,hpa,B.bound,B.bound_pos,hpn,hpz,hpp⟩,hzV,H⟩

end NLS.Articles.KdVKdV2Frequencies
