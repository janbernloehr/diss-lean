import NLS.KdV.HillWeightedSpectralSequence
import NLS.Articles.KdVEstimates.WeightedActionEstimate
import NLS.Articles.KdVEstimates.EstimateAdapter

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.KdV
open scoped ENNReal Classical

namespace NLS.Articles.KdVEstimates



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))
include h0q h0r

theorem weighted_hillSpectralSequence_bound (r : ℝ) (hr0 : 0≤r) (hr1 : r≤1/2) (v : SpectralWeight) :
    let w := SpectralWeight.product (SpectralWeight.sobolev r hr0) v
    ∃ c : ℝ, 0<c ∧ ∀ p : RealHillWeightedPotential w, p.val.val 0=0 →
      ‖hillWeightedSpectralSequence h0q h0r w p‖ ≤
        c*((1+‖p.val‖)+w.realExtension (16*‖p.val‖^(3/2-r)))*‖p.val‖ := by
  obtain ⟨C,hC,hbound⟩ := theorem3_actions r hr0 hr1 v
  dsimp only at hbound ⊢
  let w := SpectralWeight.product (SpectralWeight.sobolev r hr0) v
  refine ⟨2*C,by positivity,?_⟩
  intro p hmean
  have ht := hbound p hmean
  have hsplit := (summable_hillWeightedActionTerm w p).sum_add_tsum_nat_add 1
  have hzero : hillWeightedActionTerm w p 0=0 := by simp [hillWeightedActionTerm]
  simp only [Finset.sum_range_one,hzero,zero_add] at hsplit
  have haction : (∑' n : ℕ, hillWeightedActionTerm w p n) ≤
      C^2*(((1+‖p.val‖)*‖p.val‖)^2+
        (w.realExtension (16*‖p.val‖^(3/2-r))*‖p.val‖)^2) := by
    rw [← hsplit]
    convert ht using 1 <;> first | rfl | ring
  have h := normBound_of_actionBound (norm_nonneg (hillWeightedSpectralSequence h0q h0r w p))
    (by positivity : 0≤(1+‖p.val‖)*‖p.val‖)
    (mul_nonneg (w.realExtension_pos _).le (norm_nonneg p.val)) hC.le
    (norm_hillWeightedSpectralSequence_sq h0q h0r w p) haction
  convert h using 1
  ring

end NLS.Articles.KdVEstimates
