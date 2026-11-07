import NLS.KdV.FreeHillWideGeometry
import NLS.KdV.PseudomeasureMultiplication

/-!
# Comparison of the actual wide and narrow endpoint inverses

A diagonal multiplier compares a radius12n point with its narrow-strip center
line, preserving every raw coefficient and every signed endpoint shift. Its
norm is at most13. The wide inverse still takes values in the entire original
H1 domain, and its potential term is the actual original multiplication.
-/
noncomputable section
open scoped ENNReal
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.SmoothPeriodicTest NLS.Fourier.PeriodicFourierLebesgue

/-- Move only the real part to the free resonant center. -/
def wideHillCenter (n : ℕ) (z : ℂ) : ℂ := ⟨freeHillValue n,z.im⟩

/-- The comparison center lies in the original corrected narrow strip. -/
theorem wideHillCenter_mem (n : ℕ) (z : ℂ) : wideHillCenter n z ∈ reducedHillStrip n := by
  change |freeHillValue n-freeHillValue n| ≤ 6*(n:ℝ)
  simp only [sub_self,abs_zero]
  positivity

/-- The comparison changes the point by at most the wide-strip radius. -/
theorem norm_wideHillCenter_sub_le (n : ℕ) (z : ℂ) (hz : z ∈ wideHillStrip n) :
    ‖wideHillCenter n z-z‖ ≤ 12*(n:ℝ) := by
  have he : wideHillCenter n z-z = ((freeHillValue n-z.re:ℝ):ℂ) := by
    apply Complex.ext <;> simp [wideHillCenter]
  rw [he,Complex.norm_real,Real.norm_eq_abs,abs_sub_comm]
  exact hz

/-- The actual complementary reciprocal coefficients, also outside the narrow strip. -/
def wideHillSymbol (n : ℕ) (z : ℂ) (k : ℤ) : ℂ :=
  if k.natAbs = n then 0 else (z-(freeHillValue k:ℂ))⁻¹

/-- The bounded comparison ratio; resonant entries are harmless identities. -/
def wideHillRatio (n : ℕ) (z : ℂ) (k : ℤ) : ℂ :=
  if k.natAbs = n then 1 else (wideHillCenter n z-(freeHillValue k:ℂ))/(z-(freeHillValue k:ℂ))

/-- Every retained wide denominator is at least the positive mode index. -/
theorem wideHill_denominator_ge (n : ℕ) (hn : 2 ≤ n) (z : ℂ)
    (hz : z ∈ wideHillStrip n) (k : ℤ) (hk : k.natAbs ≠ n) :
    (n:ℝ) ≤ ‖z-(freeHillValue k:ℂ)‖ :=
  (nat_le_abs_sq_sub_sq (by omega) hk).trans (freeHill_denominator_lower_wide hn hz hk)

/-- All retained actual wide denominators are nonzero. -/
theorem wideHill_denominator_ne_zero (n : ℕ) (hn : 2 ≤ n) (z : ℂ)
    (hz : z ∈ wideHillStrip n) (k : ℤ) (hk : k.natAbs ≠ n) : z-(freeHillValue k:ℂ) ≠ 0 := by
  have hnR : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  exact norm_pos_iff.mp (hnR.trans_le (wideHill_denominator_ge n hn z hz k hk))

/-- The ratio has the same bound at every frequency, independently of the weight. -/
theorem norm_wideHillRatio_le (n : ℕ) (hn : 2 ≤ n) (z : ℂ)
    (hz : z ∈ wideHillStrip n) (k : ℤ) : ‖wideHillRatio n z k‖ ≤ 13 := by
  by_cases hk : k.natAbs = n
  · simp only [wideHillRatio,if_pos hk,norm_one]
    norm_num
  have hd := wideHill_denominator_ge n hn z hz k hk
  have hd0 : 0 < ‖z-(freeHillValue k:ℂ)‖ := norm_pos_iff.mpr
    (wideHill_denominator_ne_zero n hn z hz k hk)
  have he : wideHillRatio n z k = 1+(wideHillCenter n z-z)/(z-(freeHillValue k:ℂ)) := by
    rw [wideHillRatio,if_neg hk]
    field_simp [wideHill_denominator_ne_zero n hn z hz k hk]
    ring
  rw [he]
  apply (norm_add_le _ _).trans
  rw [norm_one,norm_div]
  have hb : ‖wideHillCenter n z-z‖ / ‖z-(freeHillValue k:ℂ)‖ ≤ 12 := by
    apply (div_le_iff₀ hd0).mpr
    nlinarith [norm_wideHillCenter_sub_le n z hz]
  linarith

/-- The comparison gives exactly the original wide reciprocal, including both removed modes. -/
theorem reducedHillSymbol_mul_wideHillRatio (n : ℕ) (hn : 2 ≤ n) (z : ℂ) (k : ℤ) :
    reducedHillSymbol n (by omega) (wideHillCenter n z) (wideHillCenter_mem n z) k *
      wideHillRatio n z k = wideHillSymbol n z k := by
  by_cases hk : k.natAbs = n
  · simp only [reducedHillSymbol,wideHillRatio,wideHillSymbol,if_pos hk,zero_mul]
  · simp only [reducedHillSymbol,wideHillRatio,wideHillSymbol,if_neg hk]
    have hc := freeHill_denominator_ne_zero (by omega : 1 ≤ n) (wideHillCenter_mem n z) hk
    field_simp [hc]

/-- The comparison acts on every original weighted exponent, including infinity. -/
def wideHillMultiplier {p : ℝ≥0∞} [Fact (1 ≤ p)] (w : Weight)
    (n : ℕ) (hn : 2 ≤ n) (z : ℂ) (hz : z ∈ wideHillStrip n) :
    WeightedCoeff w p →L[ℂ] WeightedCoeff w p :=
  WeightedCoeff.weightedMultiplierCLM w w (wideHillRatio n z) 13 (by norm_num)
    (fun k => by nlinarith [norm_wideHillRatio_le n hn z hz k,w.positive k])

@[simp] theorem wideHillMultiplier_apply {p : ℝ≥0∞} [Fact (1 ≤ p)] (w : Weight)
    (n : ℕ) (hn : 2 ≤ n) (z : ℂ) (hz : z ∈ wideHillStrip n)
    (a : WeightedCoeff w p) (k : ℤ) :
    (wideHillMultiplier w n hn z hz a).val k = wideHillRatio n z k*a.val k := rfl

/-- Its bound remains13 in every translated original endpoint norm. -/
theorem negativeShiftedNorm_wideHillMultiplier_le (w : SpectralWeight) (r : ℝ) (hr : 0 ≤ r)
    (i : ℤ) (n : ℕ) (hn : 2 ≤ n) (z : ℂ) (hz : z ∈ wideHillStrip n)
    (a : WeightedCoeff (w.negativeSobolev r) ⊤) :
    w.negativeShiftedNorm r hr i ⊤ (wideHillMultiplier (w.negativeSobolev r) n hn z hz a) ≤
      13*w.negativeShiftedNorm r hr i ⊤ a := by
  have he : w.negativeShiftEquiv r hr i ⊤ (wideHillMultiplier (w.negativeSobolev r) n hn z hz a) =
      wideHillMultiplier ((w.negativeSobolev r).shift i) n hn z hz (w.negativeShiftEquiv r hr i ⊤ a) := by
    apply Subtype.ext
    funext k
    simp only [SpectralWeight.negativeShiftEquiv_apply,wideHillMultiplier_apply]
  unfold SpectralWeight.negativeShiftedNorm
  rw [he]
  exact WeightedCoeff.norm_weightedMultiplier_le _ _ _ _ (by norm_num)
    (fun k => by nlinarith [norm_wideHillRatio_le n hn z hz k,((w.negativeSobolev r).shift i).positive k]) _

/-- The actual wide complementary inverse with values in the full original H1 domain. -/
def wideEndpointHillResolventH1 (w : SpectralWeight) (r : ℝ) (hr1 : r < 1/2)
    (n : ℕ) (hn : 2 ≤ n) (z : ℂ) (hz : z ∈ wideHillStrip n) :
    WeightedCoeff (w.negativeSobolev r) ⊤ →L[ℂ] FourierLebesgueSpace (2:ℝ) 1 2 :=
  (endpointReducedHillResolventH1Original w r hr1 n (by omega) (wideHillCenter n z)
    (wideHillCenter_mem n z)).comp (wideHillMultiplier (w.negativeSobolev r) n hn z hz)

/-- Every actual wide inverse coefficient has the required reciprocal formula. -/
theorem wideEndpointHillResolventH1_coefficient (w : SpectralWeight) (r : ℝ) (hr1 : r < 1/2)
    (n : ℕ) (hn : 2 ≤ n) (z : ℂ) (hz : z ∈ wideHillStrip n)
    (a : WeightedCoeff (w.negativeSobolev r) ⊤) (k : ℤ) :
    (wideEndpointHillResolventH1 w r hr1 n hn z hz a).val (mode (-k)) = wideHillSymbol n z k*a.val k := by
  simp only [wideEndpointHillResolventH1,ContinuousLinearMap.comp_apply,
    endpointReducedHillResolventH1Original_coefficient,wideHillMultiplier_apply]
  rw [← mul_assoc,reducedHillSymbol_mul_wideHillRatio n hn z]

/-- The wide endpoint perturbation is a bounded operator on the original carrier. -/
def wideEndpointHillPerturbation (w : SpectralWeight) (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (n : ℕ) (hn : 2 ≤ n) (z : ℂ) (hz : z ∈ wideHillStrip n)
    (q : WeightedCoeff (w.negativeSobolev r) ⊤) :
    WeightedCoeff (w.negativeSobolev r) ⊤ →L[ℂ] WeightedCoeff (w.negativeSobolev r) ⊤ :=
  (unshiftedEndpointHillPerturbation w r hr hr1 n (by omega) (wideHillCenter n z)
    (wideHillCenter_mem n z) q).comp (wideHillMultiplier (w.negativeSobolev r) n hn z hz)

/-- The wide perturbation retains the exact full original convolution rows. -/
theorem wideEndpointHillPerturbation_apply (w : SpectralWeight) (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (n : ℕ) (hn : 2 ≤ n) (z : ℂ) (hz : z ∈ wideHillStrip n)
    (q a : WeightedCoeff (w.negativeSobolev r) ⊤) (m : ℤ) :
    (wideEndpointHillPerturbation w r hr hr1 n hn z hz q a).val m =
      ∑' k : ℤ, q.val (m-k)*wideHillSymbol n z k*a.val k := by
  simp only [wideEndpointHillPerturbation,ContinuousLinearMap.comp_apply,
    unshiftedEndpointHillPerturbation_apply,wideHillMultiplier_apply]
  apply tsum_congr
  intro k
  calc
    _ = q.val (m-k)*(reducedHillSymbol n (by omega) (wideHillCenter n z)
        (wideHillCenter_mem n z) k*wideHillRatio n z k)*a.val k := by ring
    _ = _ := by rw [reducedHillSymbol_mul_wideHillRatio n hn z]

/-- Physical multiplication after the original H1 wide inverse is this exact perturbation. -/
theorem endpointH1Multiplication_wideResolvent (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (n : ℕ) (hn : 2 ≤ n) (z : ℂ) (hz : z ∈ wideHillStrip n)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) :
    (endpointH1Multiplication r hr hr1 q).comp
      (wideEndpointHillResolventH1 SpectralWeight.one r hr1 n hn z hz) =
        wideEndpointHillPerturbation SpectralWeight.one r hr hr1 n hn z hz q := by
  unfold wideEndpointHillResolventH1 wideEndpointHillPerturbation
  rw [← ContinuousLinearMap.comp_assoc,endpointH1Multiplication_resolvent]

/-- Both opposite endpoint norms retain the wide-strip decay, with explicit factor13. -/
theorem negativeShiftedNorm_wideEndpointHillPerturbation_le (w : SpectralWeight)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2) (n : ℕ) (hn : 2 ≤ n)
    (z : ℂ) (hz : z ∈ wideHillStrip n) (q a : WeightedCoeff (w.negativeSobolev r) ⊤) :
    w.negativeShiftedNorm r hr (n:ℤ) ⊤ (wideEndpointHillPerturbation w r hr hr1 n hn z hz q a) ≤
      (13*endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖)*w.negativeShiftedNorm r hr (n:ℤ) ⊤ a ∧
    w.negativeShiftedNorm r hr (-(n:ℤ)) ⊤ (wideEndpointHillPerturbation w r hr hr1 n hn z hz q a) ≤
      (13*endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖)*w.negativeShiftedNorm r hr (-(n:ℤ)) ⊤ a := by
  have h := negativeShiftedNorm_endpointHillPerturbation_le w r hr hr1 n (by omega)
    (wideHillCenter n z) (wideHillCenter_mem n z) q (wideHillMultiplier (w.negativeSobolev r) n hn z hz a)
  have hp := negativeShiftedNorm_wideHillMultiplier_le w r hr (n:ℤ) n hn z hz a
  have hm := negativeShiftedNorm_wideHillMultiplier_le w r hr (-(n:ℤ)) n hn z hz a
  have hdelta : 0 < 1-2*r := by linarith
  have hC : 0 ≤ endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ := by
    exact mul_nonneg (mul_nonneg (by unfold endpointHillConstant; positivity)
      (Real.rpow_nonneg (by positivity) _)) (norm_nonneg q)
  constructor
  · exact h.1.trans ((mul_le_mul_of_nonneg_left hp hC).trans_eq (by ring))
  · exact h.2.trans ((mul_le_mul_of_nonneg_left hm hC).trans_eq (by ring))

end NLS.KdV
