import NLS.Articles.KdVPseudomeasures.SourceSharpResonantKernel

/-! The sharp resonant Fourier-row bound for arbitrary source spectral
weights. Every row is an absolutely convergent series of actual coefficients. -/
noncomputable section
open NLS.KdV NLS.ReciprocalSeries NLS.WeightedCoeff
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures

theorem source_resonant_term_bound (w : SpectralWeight) (r : ℝ) (hr : 0≤r)
    (n : ℕ) (hn : 2≤n) (z : ℂ) (hz : z ∈ wideHillStrip n)
    (q f : WeightedCoeff (w.negativeSobolev r) ⊤) (k : ℤ) :
    w.negativeSobolev r (2*(n:ℤ))*‖q.val ((n:ℤ)-k)*wideHillSymbol n z k*f.val k‖ ≤
      (((2:ℝ)^(2*r)*(n:ℝ)^(-r))*‖q‖*w.negativeShiftedNorm r hr (n:ℤ) ⊤ f)*
        quadraticPowerKernel (1-r) n k := by
  let W := w.negativeSobolev r
  let F := w.negativeShiftEquiv r hr (n:ℤ) ⊤ f
  have hq := norm_apply_le W ⊤ q ((n:ℤ)-k)
  have hf : ‖f.val k‖ ≤ w.negativeShiftedNorm r hr (n:ℤ) ⊤ f/W (k+(n:ℤ)) := by
    change ‖f.val k‖ ≤ ‖F‖/W (k+(n:ℤ))
    simpa only [F,SpectralWeight.negativeShiftEquiv_apply,Weight.shift_apply] using
      norm_apply_le (W.shift (n:ℤ)) ⊤ F k
  have hF : 0 ≤ w.negativeShiftedNorm r hr (n:ℤ) ⊤ f := norm_nonneg _
  calc
    _ = W (2*(n:ℤ))*(‖q.val ((n:ℤ)-k)‖*‖f.val k‖)*‖wideHillSymbol n z k‖ := by
      rw [norm_mul,norm_mul]
      ring
    _ ≤ W (2*(n:ℤ))*((‖q‖/W ((n:ℤ)-k))*(w.negativeShiftedNorm r hr (n:ℤ) ⊤ f/W (k+(n:ℤ))))*
        ‖wideHillSymbol n z k‖ := by
      have hprod := mul_le_mul hq hf (norm_nonneg _) (div_nonneg (norm_nonneg q) (W.positive _).le)
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hprod (W.positive _).le) (norm_nonneg _)
    _ = ((W (2*(n:ℤ))/(W ((n:ℤ)-k)*W (k+(n:ℤ))))*‖wideHillSymbol n z k‖)*‖q‖*
        w.negativeShiftedNorm r hr (n:ℤ) ⊤ f := by ring
    _ ≤ ((Weight.sobolev r ((n:ℤ)-k)*Weight.sobolev r (k+(n:ℤ))/Weight.sobolev r (2*(n:ℤ)))*
        ‖wideHillSymbol n z k‖)*‖q‖*w.negativeShiftedNorm r hr (n:ℤ) ⊤ f :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (source_resonant_weight_ratio w r n k) (norm_nonneg _)) (norm_nonneg q)) hF
    _ ≤ (((2:ℝ)^(2*r)*(n:ℝ)^(-r))*quadraticPowerKernel (1-r) n k)*‖q‖*
        w.negativeShiftedNorm r hr (n:ℤ) ⊤ f :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (source_resonant_symbol_factor r hr n hn z hz k) (norm_nonneg q)) hF
    _ = _ := by ring

theorem source_resonant_row_sum_bound (w : SpectralWeight) (r : ℝ) (hr : 0≤r) (hr1 : r<1/2)
    (n : ℕ) (hn : 2≤n) (z : ℂ) (hz : z ∈ wideHillStrip n)
    (q f : WeightedCoeff (w.negativeSobolev r) ⊤) :
    w.negativeSobolev r (2*(n:ℤ))*
      ‖(wideEndpointHillPerturbation w r hr hr1 n hn z hz q f).val (n:ℤ)‖ ≤
        (((2:ℝ)^(2*r)*(n:ℝ)^(-r))*‖q‖*w.negativeShiftedNorm r hr (n:ℤ) ⊤ f)*
          (∑' k : ℤ, quadraticPowerKernel (1-r) n k) := by
  let W := w.negativeSobolev r (2*(n:ℤ))
  let M := ((2:ℝ)^(2*r)*(n:ℝ)^(-r))*‖q‖*w.negativeShiftedNorm r hr (n:ℤ) ⊤ f
  let a := fun k : ℤ => q.val ((n:ℤ)-k)*wideHillSymbol n z k*f.val k
  have hW : 0<W := (w.negativeSobolev r).positive _
  have hsum := (quadraticPowerKernel_twoScale_bound (1-r) (by linarith) n (by omega)).1
  have hmajor := hsum.mul_left M
  have hterm (k : ℤ) : W*‖a k‖ ≤ M*quadraticPowerKernel (1-r) n k :=
    source_resonant_term_bound w r hr n hn z hz q f k
  have hs := hmajor.of_nonneg_of_le (fun _ => mul_nonneg hW.le (norm_nonneg _)) hterm
  have hnorm : Summable (fun k : ℤ => ‖a k‖) := by
    simpa only [← mul_assoc,inv_mul_cancel₀ hW.ne',one_mul] using hs.mul_left W⁻¹
  rw [wideEndpointHillPerturbation_apply]
  calc
    _ ≤ W*(∑' k : ℤ, ‖a k‖) := mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hnorm) hW.le
    _ = ∑' k : ℤ, W*‖a k‖ := (tsum_mul_left).symm
    _ ≤ ∑' k : ℤ, M*quadraticPowerKernel (1-r) n k := hs.tsum_le_tsum hterm hmajor
    _ = _ := tsum_mul_left

end NLS.Articles.KdVPseudomeasures
