import NLS.SequenceSpaces.AnalyticPacketPullback
import NLS.KdV.HillNativePairInverse
import NLS.KdV.PhysicalSobolevLpFrequencyChart
import NLS.Articles.KdVKdV2Frequencies.RawPairArnoldActions

/-! Actual UNDIVIDED frequency packets in the signed h^0 pair topology.
Every real Hilbert pair is a center, including arbitrary infinite support
and closed-action boundary points. The SAME native inverse is retained. -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.KdV NLS.ZakharovShabat
open NLS.Articles.KdVConvexity
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies

structure StrongLpFrequencyPairChart (D : GlobalRoughAbelianForwardData)
    (r : ℝ≥0∞) [Fact (1 ≤ r)] where
  domain : Set (Coeff 2 × Coeff 2)
  domain_open : IsOpen domain
  roughPotential : (Coeff 2 × Coeff 2) → PeriodOneHminusOne
  analytic_potential : AnalyticOnNhd ℂ roughPotential domain
  rough_zero : ∀ z∈domain, (roughPotential z).val 0=0
  rough_real : ∀ z∈domain, z∈Coeff.realPairLocus 2 → IsRealPeriodOneHminusOne (roughPotential z)
  rough_signed : ∀ z∈domain, z∈Coeff.realPairLocus 2 → ∀ j : ℤ,
    (D.signed (roughPotential z)).val j=(signedPairToDeleted actionIndexEquiv z).val j
  physicalChart : PhysicalMiuraFrequencyChart
  rough_mem : ∀ z∈domain, roughPotential z∈physicalChart.domain
  packet : (Coeff 2 × Coeff 2) → Coeff r
  analytic_packet : AnalyticOnNhd ℂ packet domain
  bound : ℝ
  bound_pos : 0<bound
  norm_packet : ∀ z∈domain, ‖packet z‖≤bound
  nonpositive : ∀ z∈domain, ∀ j : ℤ, j≤0 → packet z j=0
  positive : ∀ z∈domain, ∀ n : ℕ+, packet z (n : ℤ)=physicalChart.correction n (roughPotential z)

namespace StrongLpFrequencyPairChart
variable {D : GlobalRoughAbelianForwardData} {r : ℝ≥0∞} [Fact (1 ≤ r)]

def correction (P : StrongLpFrequencyPairChart D r) (n : ℕ+) (z : Coeff 2 × Coeff 2) : ℂ :=
  P.physicalChart.correction n (P.roughPotential z)

theorem analytic_correction (P : StrongLpFrequencyPairChart D r) (n : ℕ+) :
    AnalyticOnNhd ℂ (P.correction n) P.domain := by
  intro z hz
  exact (P.physicalChart.analytic_correction n _ (P.rough_mem z hz)).comp (P.analytic_potential z hz)

end StrongLpFrequencyPairChart

theorem exists_strongLpFrequencyPairChart (D : GlobalRoughAbelianForwardData)
    {r : ℝ≥0∞} [Fact (1 ≤ r)] (hr : 1<r) (z0 : Coeff 2 × Coeff 2)
    (hz0 : z0∈Coeff.realPairLocus 2) :
    ∃ P : StrongLpFrequencyPairChart D r, z0∈P.domain := by
  obtain ⟨U,hU,hzU,Q,hQ,hmean,hmatch⟩ := exists_hillNative_pair_inverse D actionIndexEquiv
    (1/2) (by norm_num) z0 hz0
  let R := fun z => halfSobolevHillInclusion (Q z)
  have hRa : AnalyticOnNhd ℂ R U := by
    intro z hz
    exact (halfSobolevHillInclusion.analyticAt _).comp (hQ z hz)
  have hreal (z : Coeff 2 × Coeff 2) (hz : z∈U) (hzr : z∈Coeff.realPairLocus 2) :
      IsRealPeriodOneHminusOne (R z) := by
    change IsRealPeriodOneHminusOne (halfSobolevHillInclusion (Q z))
    rw [hmatch z hz hzr]
    exact nativeRealPairInverse_real D actionIndexEquiv (1/2) (by norm_num) z hzr
  obtain ⟨B,hqB⟩ := exists_physicalSobolevLpFrequencyChart hr (Q z0) (hreal z0 hzU hz0)
  obtain ⟨V,hV,hzV,hVU,hQV,packet,hpa,hpn,hpz,hpp⟩ :=
    exists_analytic_packet_pullback Q U hU hQ B.domain B.domain_open B.packet B.analytic_packet
      B.bound B.norm_packet (fun (b : Coeff r) (j : ℤ) => b j)
      (fun n a => B.physical.correction n (halfSobolevHillInclusion a))
      B.nonpositive B.positive z0 hzU hqB
  have hmem (z : Coeff 2 × Coeff 2) (hz : z∈V) : R z∈B.physical.domain :=
    mem_of_subset_preimage halfSobolevHillInclusion B.domain B.physical.domain B.domain_subset (Q z) (hQV z hz)
  have hzero (z : Coeff 2 × Coeff 2) (hz : z∈V) : (R z).val 0=0 := by
    rw [periodOneSobolevImageInclusion_apply]
    exact hmean z (hVU hz)
  have hsign (z : Coeff 2 × Coeff 2) (hz : z∈V) (hzr : z∈Coeff.realPairLocus 2) (j : ℤ) :
      (D.signed (R z)).val j=(signedPairToDeleted actionIndexEquiv z).val j := by
    change (D.signed (halfSobolevHillInclusion (Q z))).val j=_
    rw [hmatch z (hVU hz) hzr]
    exact nativeRealHalfPairInverse_signed_apply D actionIndexEquiv z hzr j
  exact ⟨⟨V,hV,R,hRa.mono hVU,hzero,(fun z hz hzr => hreal z (hVU hz) hzr),hsign,
    B.physical,hmem,packet,hpa,B.bound,B.bound_pos,hpn,hpz,hpp⟩,hzV⟩

end NLS.Articles.KdVKdV2Frequencies
