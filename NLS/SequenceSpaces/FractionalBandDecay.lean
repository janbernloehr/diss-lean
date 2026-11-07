import NLS.SequenceSpaces.NegativeSobolevFrequencyBands
import NLS.FunctionalAnalysis.CompactSummableBlocks
import Mathlib.Analysis.SpecificLimits.Normed

/-! Endpoint operator bounds give a summable dyadic estimate for an
already bounded intermediate operator. Only its output norm is interpolated. -/
noncomputable section
open Filter
namespace NLS.WeightedCoeff

private theorem geometric_common_factor (M L N t : ℝ) (hM : 0 ≤ M)
    (hL : 0 ≤ L) (hN : 0 < N) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    (M*(N^(-1:ℝ)*L))^(1-t)*(M*L)^t = M*N^(-(1-t))*L := by
  rw [Real.mul_rpow hM (mul_nonneg (by positivity) hL),
    Real.mul_rpow (by positivity : 0 ≤ N^(-1:ℝ)) hL, Real.mul_rpow hM hL]
  calc
    _ = (M^(1-t)*M^t)*((N^(-1:ℝ))^(1-t))*(L^(1-t)*L^t) := by ring
    _ = _ := by
      rw [← Real.rpow_add_of_nonneg hM (sub_nonneg.mpr ht1) ht,
        ← Real.rpow_add_of_nonneg hL (sub_nonneg.mpr ht1) ht,
        ← Real.rpow_mul hN.le]
      simp only [sub_add_cancel, Real.rpow_one, neg_one_mul]

private theorem band_power_cancel (r N : ℝ) (hN : 0 < N) :
    N^(-(1-(1-r)/2))*(2*N)^r = (2:ℝ)^r*N^(-((1-r)/2)) := by
  rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hN.le]
  calc
    _ = (2:ℝ)^r*(N^(-(1-(1-r)/2))*N^r) := by ring
    _ = _ := by rw [← Real.rpow_add hN]; congr 2; ring

theorem norm_fractional_band_le (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (B₀ : WeightedCoeff (Weight.sobolev (-1)) 2 →L[ℂ]
      WeightedCoeff (Weight.signedSobolev (-1/2)) 2)
    (B₁ : WeightedCoeff (Weight.sobolev 0) 2 →L[ℂ]
      WeightedCoeff (Weight.signedSobolev (3/2)) 2)
    (B : WeightedCoeff (Weight.sobolev (-r)) 2 →L[ℂ]
      WeightedCoeff (Weight.signedSobolev (1/2-r)) 2)
    (N : ℕ) (hN : 1 ≤ N) (a : WeightedCoeff (Weight.sobolev (-r)) 2)
    (h₀ : ∀ k, (B₀ (frequencyBand (Weight.sobolev (-1)) N a.val)).val k =
      (B (frequencyBand (Weight.sobolev (-r)) N a.val)).val k)
    (h₁ : ∀ k, (B₁ (frequencyBand (Weight.sobolev 0) N a.val)).val k =
      (B (frequencyBand (Weight.sobolev (-r)) N a.val)).val k) :
    ‖B (frequencyBand (Weight.sobolev (-r)) N a.val)‖ ≤
      ((‖B₀‖+‖B₁‖+1)*(2:ℝ)^r)*(N:ℝ)^(-((1-r)/2))*‖a‖ := by
  let t := (1-r)/2
  let M := ‖B₀‖+‖B₁‖+1
  let L := ‖frequencyBand (Weight.sobolev 0) N a.val‖
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have ht1 : t ≤ 1 := by dsimp [t]; linarith
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hL : 0 ≤ L := norm_nonneg _
  have hNp : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hzero : ‖B₀ (frequencyBand (Weight.sobolev (-1)) N a.val)‖ ≤ M*((N:ℝ)^(-1:ℝ)*L) := by
    calc
      _ ≤ ‖B₀‖*‖frequencyBand (Weight.sobolev (-1)) N a.val‖ := B₀.le_opNorm _
      _ ≤ ‖B₀‖*((N:ℝ)^(-1:ℝ)*L) := mul_le_mul_of_nonneg_left
        (norm_frequencyBand_minusOne_le N hN a.val) (norm_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_right (by dsimp [M]; linarith [norm_nonneg B₁]) (by positivity)
  have hone : ‖B₁ (frequencyBand (Weight.sobolev 0) N a.val)‖ ≤ M*L := by
    exact (B₁.le_opNorm _).trans (mul_le_mul_of_nonneg_right
      (by dsimp [M]; linarith [norm_nonneg B₀]) hL)
  have hgeom := norm_le_weighted_geometric (Weight.signedSobolev (-1/2))
    (Weight.signedSobolev (3/2)) (Weight.signedSobolev (1/2-r)) t ht ht1
    (fun k => by
      change (max 1 |(k:ℝ)|)^(1/2-r) =
        ((max 1 |(k:ℝ)|)^(-1/2:ℝ))^(1-t)*((max 1 |(k:ℝ)|)^(3/2:ℝ))^t
      rw [← Real.rpow_mul (by positivity), ← Real.rpow_mul (by positivity),
        ← Real.rpow_add (by positivity)]
      congr 1
      dsimp [t]
      ring)
    (B₀ (frequencyBand (Weight.sobolev (-1)) N a.val))
    (B₁ (frequencyBand (Weight.sobolev 0) N a.val))
    (B (frequencyBand (Weight.sobolev (-r)) N a.val)) h₀ h₁
  calc
    _ ≤ (M*((N:ℝ)^(-1:ℝ)*L))^(1-t)*(M*L)^t := hgeom.trans
      (mul_le_mul (Real.rpow_le_rpow (norm_nonneg _) hzero (sub_nonneg.mpr ht1))
        (Real.rpow_le_rpow (norm_nonneg _) hone ht) (by positivity) (by positivity))
    _ = M*(N:ℝ)^(-(1-t))*L := geometric_common_factor M L N t hM hL hNp ht ht1
    _ ≤ M*(N:ℝ)^(-(1-t))*(((2*N:ℕ):ℝ)^r*‖a‖) :=
      mul_le_mul_of_nonneg_left (norm_frequencyBand_zero_le r hr N hN a) (by positivity)
    _ = _ := by
      rw [Nat.cast_mul, Nat.cast_ofNat]
      calc
        _ = M*((N:ℝ)^(-(1-(1-r)/2))*(2*(N:ℝ))^r)*‖a‖ := by dsimp [t]; ring
        _ = _ := by rw [band_power_cancel r (N:ℝ) hNp]; dsimp [M]; ring

end NLS.WeightedCoeff
