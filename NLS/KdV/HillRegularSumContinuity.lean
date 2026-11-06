import NLS.KdV.HillUniformCorrectionDecay
import NLS.KdV.HillSummedRegularCorrection
import NLS.KdV.HillGlobalRegularContinuity
import NLS.SequenceSpaces.LocalSeriesContinuity

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))
include h0q h0r

theorem exists_hillRegularAbelianCorrection_locally_small_absolute_tail
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1 ≤ n) (ε : ℝ) (hε : 0 < ε) :
    ∃ L : ℕ, ∀ᶠ r : RealPeriodOneHillPotential in 𝓝 q,
      (∑' k : ℕ, ‖hillRegularAbelianCorrection r.val r.property.1 r.property.2 n hn ((k+L)+1) (by omega)‖) ≤ ε := by
  obtain ⟨N,hN,C,hC,hbound⟩ := exists_hillRegularAbelianCorrection_locally_uniform_quadratic_decay h0q h0r q.val q.property.1 q.property.2 n hn
  obtain ⟨K,hK⟩ := exists_nat_ge (2*C/ε)
  let L := max N K
  have hL : 1 ≤ L+1 := by omega
  have hL0 : (0 : ℝ) < (L+1 : ℕ) := by positivity
  have hCL : 2*C/(L+1 : ℕ) ≤ ε := by
    apply (div_le_iff₀ hL0).mpr
    have hle : 2*C/ε ≤ (L+1 : ℕ) := hK.trans (by exact_mod_cast (show K ≤ L+1 by dsimp [L];omega))
    have ht := (div_le_iff₀ hε).mp hle
    nlinarith
  refine ⟨L,?_⟩
  filter_upwards [hbound] with r hr
  have hmajor : Summable (fun k : ℕ => C/((k : ℝ)+(L+1 : ℕ))^2) := by
    simpa only [mul_one_div] using (NLS.ReciprocalSeries.summable_nat_reciprocal_sq_tail (L+1) hL).mul_left C
  have hb (k : ℕ) : ‖hillRegularAbelianCorrection r.val r.property.1 r.property.2 n hn ((k+L)+1) (by omega)‖ ≤ C/((k : ℝ)+(L+1 : ℕ))^2 := by
    simpa only [Nat.cast_add,Nat.cast_one,add_assoc] using hr ((k+L)+1) (by dsimp [L];omega) (by omega)
  have hs : Summable (fun k : ℕ => ‖hillRegularAbelianCorrection r.val r.property.1 r.property.2 n hn ((k+L)+1) (by omega)‖) :=
    hmajor.of_norm_bounded (fun k => by simpa only [norm_norm] using hb k)
  calc
    _ ≤ ∑' k : ℕ, C/((k : ℝ)+(L+1 : ℕ))^2 := hs.tsum_le_tsum hb hmajor
    _ = C*(∑' k : ℕ, 1/((k : ℝ)+(L+1 : ℕ))^2) := by rw [← tsum_mul_left];simp only [mul_one_div]
    _ ≤ C*(2/(L+1 : ℕ)) := mul_le_mul_of_nonneg_left (NLS.ReciprocalSeries.tsum_nat_reciprocal_sq_tail_le (L+1) hL) hC.le
    _ = 2*C/(L+1 : ℕ) := by ring
    _ ≤ ε := hCL

theorem continuous_hillSummedRegularAbelianCorrection (n : ℕ) (hn : 1 ≤ n) :
    Continuous (fun q : RealPeriodOneHillPotential => hillSummedRegularAbelianCorrection q.val q.property.1 q.property.2 n hn) := by
  apply continuous_iff_continuousAt.mpr
  intro q
  apply NLS.continuousAt_tsum_of_locally_small_nat_tails
    (fun r : RealPeriodOneHillPotential => fun k : ℕ => hillRegularAbelianCorrection r.val r.property.1 r.property.2 n hn (k+1) (by omega)) q
    (fun r => summable_hillRegularAbelianCorrection h0q h0r r.val r.property.1 r.property.2 n hn)
    (fun k => (continuous_hillRegularAbelianCorrection h0q h0r n (k+1) hn (by omega)).continuousAt)
  intro ε hε
  obtain ⟨L,hL⟩ := exists_hillRegularAbelianCorrection_locally_small_absolute_tail h0q h0r q n hn ε hε
  refine ⟨L,?_⟩
  filter_upwards [hL] with r hr
  have hs := (summable_norm_hillRegularAbelianCorrection h0q h0r r.val r.property.1 r.property.2 n hn)
  have htail := (summable_nat_add_iff L).mpr hs
  exact (norm_tsum_le_tsum_norm htail).trans hr

end NLS.KdV
