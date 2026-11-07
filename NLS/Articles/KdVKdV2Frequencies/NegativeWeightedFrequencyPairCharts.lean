import NLS.SequenceSpaces.AnalyticPacketPullback
import NLS.KdV.HillNativePairInverse
import NLS.KdV.PhysicalNegativeWeightedFrequencyChart
import NLS.Articles.KdVKdV2Frequencies.RawPairArnoldActions

/-! Actual intermediate frequency packets in the normalized native pair
coordinates. The packet norm is the original negative weighted ell1 norm;
its physical scalar correction and raw signed coordinates retain their weights. -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.KdV NLS.ZakharovShabat
open NLS.Articles.KdVConvexity
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies

structure NegativeWeightedFrequencyPairChart (D : GlobalRoughAbelianForwardData)
    (β t : ℝ) where
  domain : Set (Coeff 2 × Coeff 2)
  domain_open : IsOpen domain
  roughPotential : (Coeff 2 × Coeff 2) → PeriodOneHminusOne
  analytic_potential : AnalyticOnNhd ℂ roughPotential domain
  rough_zero : ∀ z∈domain, (roughPotential z).val 0=0
  rough_real : ∀ z∈domain, z∈Coeff.realPairLocus 2 → IsRealPeriodOneHminusOne (roughPotential z)
  rough_signed : ∀ z∈domain, z∈Coeff.realPairLocus 2 → ∀ j : ℤ,
    (D.signed (roughPotential z)).val j=(signedPairToDeleted actionIndexEquiv z).val j/(Weight.sobolev (t-1/2) j : ℂ)
  physicalChart : PhysicalMiuraFrequencyChart
  rough_mem : ∀ z∈domain, roughPotential z∈physicalChart.domain
  packet : (Coeff 2 × Coeff 2) → Coeff 1
  analytic_packet : AnalyticOnNhd ℂ packet domain
  bound : ℝ
  bound_pos : 0<bound
  norm_packet : ∀ z∈domain, ‖packet z‖≤bound
  nonpositive : ∀ z∈domain, ∀ j : ℤ, j≤0 → packet z j=0
  positive : ∀ z∈domain, ∀ n : ℕ+, packet z (n : ℤ)=(Weight.sobolev (-β) (n : ℤ) : ℂ)*physicalChart.correction n (roughPotential z)

namespace NegativeWeightedFrequencyPairChart
variable {D : GlobalRoughAbelianForwardData} {β t : ℝ}

def correction (P : NegativeWeightedFrequencyPairChart D β t) (n : ℕ+) (z : Coeff 2 × Coeff 2) : ℂ :=
  P.physicalChart.correction n (P.roughPotential z)

theorem analytic_correction (P : NegativeWeightedFrequencyPairChart D β t) (n : ℕ+) :
    AnalyticOnNhd ℂ (P.correction n) P.domain := by
  intro z hz
  exact (P.physicalChart.analytic_correction n _ (P.rough_mem z hz)).comp (P.analytic_potential z hz)

end NegativeWeightedFrequencyPairChart

theorem exists_negativeWeightedFrequencyPairChart (D : GlobalRoughAbelianForwardData)
    (β t : ℝ) (hβ : 0<β) (hβ1 : β<1) (ht : 0<t) (hβt : 2*t=1-β)
    (z0 : Coeff 2 × Coeff 2)
    (hz0 : z0∈Coeff.realPairLocus 2) :
    ∃ P : NegativeWeightedFrequencyPairChart D β t, z0∈P.domain := by
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
  obtain ⟨B,hqB⟩ := exists_physicalNegativeWeightedFrequencyChart β t hβ hβ1 ht hβt (Q z0) (hreal z0 hzU hz0)
  obtain ⟨V,hV,hzV,hVU,hQV,packet,hpa,hpn,hpz,hpp⟩ :=
    exists_analytic_packet_pullback Q U hU hQ B.domain B.domain_open B.packet B.analytic_packet
      B.bound B.norm_packet (fun (b : Coeff 1) (j : ℤ) => b j)
      (fun n a => (Weight.sobolev (-β) (n : ℤ) : ℂ)*B.physical.correction n (J a))
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
  exact ⟨⟨V,hV,R,hRa.mono hVU,hzero,(fun z hz hzr => hreal z (hVU hz) hzr),hsign,
    B.physical,hmem,packet,hpa,B.bound,B.bound_pos,hpn,hpz,hpp⟩,hzV⟩

end NLS.Articles.KdVKdV2Frequencies
