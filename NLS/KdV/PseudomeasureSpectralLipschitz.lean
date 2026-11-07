import NLS.KdV.PseudomeasureCoefficients
import NLS.KdV.PseudomeasureZeroCount

/-! # Spectral Lipschitz bounds in the singular endpoint scale

The complementary Fourier resolvent identity gives a global bound on the
corrected closed strip. Both opposite shifted endpoint norms are retained.
The diagonal bound uses the existing cutoff, with no derivative estimate or
extra regularity assumption on the singular potential.
-/
noncomputable section
open scoped ENNReal
namespace NLS.KdV

/-- A diagonal free resolvent respects every shifted signed endpoint norm. -/
theorem negativeShiftedNorm_weightedReducedHillResolvent_le (w : SpectralWeight)
    (r : ℝ) (hr : 0 ≤ r) (i : ℤ) (n : ℕ) (hn : 1 ≤ n)
    (z : ℂ) (hz : z ∈ reducedHillStrip n) (a : WeightedCoeff (w.negativeSobolev r) ⊤) :
    w.negativeShiftedNorm r hr i ⊤
      (weightedReducedHillResolvent (w.negativeSobolev r) n hn z hz a) ≤
      (n:ℝ)⁻¹*w.negativeShiftedNorm r hr i ⊤ a := by
  have he : w.negativeShiftEquiv r hr i ⊤
      (weightedReducedHillResolvent (w.negativeSobolev r) n hn z hz a) =
    weightedReducedHillResolvent ((w.negativeSobolev r).shift i) n hn z hz
      (w.negativeShiftEquiv r hr i ⊤ a) := by
    apply Subtype.ext
    funext k
    simp only [SpectralWeight.negativeShiftEquiv_apply, weightedReducedHillResolvent_apply]
  change ‖w.negativeShiftEquiv r hr i ⊤ _‖ ≤ _
  rw [he]
  exact norm_weightedReducedHillResolvent_apply_le _ n hn z hz _

/-- The literal unshifted perturbation rows are genuinely summable. -/
theorem summable_unshiftedEndpointHill_terms (w : SpectralWeight) (r : ℝ)
    (hr : 0 ≤ r) (hr1 : r < 1/2) (n : ℕ) (hn : 1 ≤ n)
    (z : ℂ) (hz : z ∈ reducedHillStrip n)
    (q a : WeightedCoeff (w.negativeSobolev r) ⊤) (m : ℤ) :
    Summable (fun k => q.val (m-k)*reducedHillSymbol n hn z hz k*a.val k) := by
  simpa only [SpectralWeight.negativeShiftEquiv_apply] using
    (summable_norm_endpointHill_terms w r hr hr1 n hn z hz q
      (w.negativeShiftEquiv r hr n ⊤ a) m).of_norm

/-- The actual endpoint perturbations obey the complementary resolvent identity. -/
theorem unshiftedEndpointHillPerturbation_sub (w : SpectralWeight) (r : ℝ)
    (hr : 0 ≤ r) (hr1 : r < 1/2) (n : ℕ) (hn : 1 ≤ n)
    (z y : ℂ) (hz : z ∈ reducedHillStrip n) (hy : y ∈ reducedHillStrip n)
    (q a : WeightedCoeff (w.negativeSobolev r) ⊤) :
    unshiftedEndpointHillPerturbation w r hr hr1 n hn z hz q a -
      unshiftedEndpointHillPerturbation w r hr hr1 n hn y hy q a =
      (y-z) • unshiftedEndpointHillPerturbation w r hr hr1 n hn z hz q
        (weightedReducedHillResolvent (w.negativeSobolev r) n hn y hy a) := by
  apply Subtype.ext
  funext m
  simp only [WeightedCoeff.sub_val, WeightedCoeff.smul_val,
    unshiftedEndpointHillPerturbation_apply, weightedReducedHillResolvent_apply]
  rw [← (summable_unshiftedEndpointHill_terms w r hr hr1 n hn z hz q a m).tsum_sub
    (summable_unshiftedEndpointHill_terms w r hr hr1 n hn y hy q a m), ← tsum_mul_left]
  apply tsum_congr
  intro k
  simp only [reducedHillSymbol]
  split_ifs with hk
  · simp
  · field_simp [freeHill_denominator_ne_zero hn hz hk, freeHill_denominator_ne_zero hn hy hk]
    ring

/-- The two source shifted bounds give the spectral variation of the actual perturbation. -/
theorem negativeShiftedNorm_endpointHillPerturbation_sub_le (w : SpectralWeight)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2) (n : ℕ) (hn : 1 ≤ n)
    (z y : ℂ) (hz : z ∈ reducedHillStrip n) (hy : y ∈ reducedHillStrip n)
    (q a : WeightedCoeff (w.negativeSobolev r) ⊤) (i : ℤ)
    (hi : i = (n:ℤ) ∨ i = -(n:ℤ)) :
    w.negativeShiftedNorm r hr i ⊤
      (unshiftedEndpointHillPerturbation w r hr hr1 n hn z hz q a -
        unshiftedEndpointHillPerturbation w r hr hr1 n hn y hy q a) ≤
      (endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖)*(n:ℝ)⁻¹*‖z-y‖*
        w.negativeShiftedNorm r hr i ⊤ a := by
  have hC := (endpointHillConstant_pos r hr1).le
  rw [unshiftedEndpointHillPerturbation_sub]
  change ‖w.negativeShiftEquiv r hr i ⊤ ((y-z) • _)‖ ≤ _
  rw [map_smul, norm_smul, norm_sub_rev]
  have ht : w.negativeShiftedNorm r hr i ⊤
      (unshiftedEndpointHillPerturbation w r hr hr1 n hn z hz q
        (weightedReducedHillResolvent (w.negativeSobolev r) n hn y hy a)) ≤
      (endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖)*w.negativeShiftedNorm r hr i ⊤
        (weightedReducedHillResolvent (w.negativeSobolev r) n hn y hy a) := by
    rcases hi with rfl | rfl
    · exact (negativeShiftedNorm_endpointHillPerturbation_le w r hr hr1 n hn z hz q _).1
    · exact (negativeShiftedNorm_endpointHillPerturbation_le w r hr hr1 n hn z hz q _).2
  calc
    _ ≤ ‖z-y‖*((endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖)*
        w.negativeShiftedNorm r hr i ⊤ (weightedReducedHillResolvent (w.negativeSobolev r) n hn y hy a)) :=
      mul_le_mul_of_nonneg_left ht (norm_nonneg _)
    _ ≤ ‖z-y‖*((endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖)*
        ((n:ℝ)⁻¹*w.negativeShiftedNorm r hr i ⊤ a)) := by
      gcongr
      exact negativeShiftedNorm_weightedReducedHillResolvent_le w r hr i n hn y hy a
    _ = _ := by ring

/-- The original-carrier tail inverses satisfy the resolvent identity. -/
theorem endpointHillTailInverse_sub (w : SpectralWeight) (r : ℝ)
    (hr : 0 ≤ r) (hr1 : r < 1/2) (n : ℕ) (hn : 1 ≤ n)
    (z y : ℂ) (hz : z ∈ reducedHillStrip n) (hy : y ∈ reducedHillStrip n)
    (q b : WeightedCoeff (w.negativeSobolev r) ⊤)
    (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2) :
    endpointHillTailInverse w r hr hr1 n hn z hz q hs b -
      endpointHillTailInverse w r hr hr1 n hn y hy q hs b =
      endpointHillTailInverse w r hr hr1 n hn z hz q hs
        (unshiftedEndpointHillPerturbation w r hr hr1 n hn z hz q
            (endpointHillTailInverse w r hr hr1 n hn y hy q hs b) -
          unshiftedEndpointHillPerturbation w r hr hr1 n hn y hy q
            (endpointHillTailInverse w r hr hr1 n hn y hy q hs b)) := by
  apply endpointHillTailInverse_unique
  rw [map_sub]
  have hz' := endpointHillTailInverse_right w r hr hr1 n hn z hz q hs b
  have hy' := endpointHillTailInverse_right w r hr hr1 n hn y hy q hs b
  calc
    _ = (endpointHillTailInverse w r hr hr1 n hn z hz q hs b-
        unshiftedEndpointHillPerturbation w r hr hr1 n hn z hz q
          (endpointHillTailInverse w r hr hr1 n hn z hz q hs b)) -
      (endpointHillTailInverse w r hr hr1 n hn y hy q hs b-
        unshiftedEndpointHillPerturbation w r hr hr1 n hn y hy q
          (endpointHillTailInverse w r hr hr1 n hn y hy q hs b)) +
      (unshiftedEndpointHillPerturbation w r hr hr1 n hn z hz q
          (endpointHillTailInverse w r hr hr1 n hn y hy q hs b) -
        unshiftedEndpointHillPerturbation w r hr hr1 n hn y hy q
          (endpointHillTailInverse w r hr hr1 n hn y hy q hs b)) := by abel
    _ = _ := by rw [hz', hy']; abel

/-- The corrected resonant columns vary Lipschitz continuously over the entire closed strip. -/
theorem negativeShiftedNorm_endpointHillCorrectedMode_sub_le (w : SpectralWeight)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2) (n : ℕ) (hn : 1 ≤ n)
    (z y : ℂ) (hz : z ∈ reducedHillStrip n) (hy : y ∈ reducedHillStrip n)
    (q : WeightedCoeff (w.negativeSobolev r) ⊤)
    (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2)
    (j : ℤ) (hj : j = (n:ℤ) ∨ j = -(n:ℤ)) :
    w.negativeShiftedNorm r hr (-j) ⊤
      (endpointHillCorrectedMode w r hr hr1 n hn z hz q hs j -
        endpointHillCorrectedMode w r hr hr1 n hn y hy q hs j) ≤
      (4*(endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖)*(n:ℝ)⁻¹*‖q‖)*‖z-y‖ := by
  have hC := (endpointHillConstant_pos r hr1).le
  have hi : -j = (n:ℤ) ∨ -j = -(n:ℤ) := by rcases hj with rfl | rfl <;> simp
  unfold endpointHillCorrectedMode
  rw [endpointHillTailInverse_sub]
  let a := endpointHillCorrectedMode w r hr hr1 n hn y hy q hs j
  let d := unshiftedEndpointHillPerturbation w r hr hr1 n hn z hz q a -
    unshiftedEndpointHillPerturbation w r hr hr1 n hn y hy q a
  have hK := negativeShiftedNorm_endpointHillTailInverse_le w r hr hr1 n hn z hz q hs d
  have hK' : w.negativeShiftedNorm r hr (-j) ⊤
      (endpointHillTailInverse w r hr hr1 n hn z hz q hs d) ≤
        2*w.negativeShiftedNorm r hr (-j) ⊤ d := by
    rcases hi with h | h
    · simpa only [h] using hK.1
    · simpa only [h] using hK.2
  apply hK'.trans
  calc
    _ ≤ 2*((endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖)*(n:ℝ)⁻¹*‖z-y‖*
      w.negativeShiftedNorm r hr (-j) ⊤ (endpointHillCorrectedMode w r hr hr1 n hn y hy q hs j)) := by
      gcongr
      exact negativeShiftedNorm_endpointHillPerturbation_sub_le w r hr hr1 n hn z y hz hy q _ (-j) hi
    _ ≤ 2*((endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖)*(n:ℝ)⁻¹*‖z-y‖*(2*‖q‖)) := by
      gcongr
      exact negativeShiftedNorm_endpointHillCorrectedMode_le w r hr hr1 n hn y hy q hs j hj
    _ = _ := by ring

/-- Global spectral variation of the actual diagonal correction in the endpoint scale. -/
theorem endpointDiagonal_sub_le (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (n : ℕ) (hn : 1 ≤ n) (z y : ℂ)
    (hz : z ∈ reducedHillStrip n) (hy : y ∈ reducedHillStrip n)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤)
    (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2) :
    ‖endpointDiagonal r hr hr1 n (q,z)-endpointDiagonal r hr hr1 n (q,y)‖ ≤
      (4*(endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖)*(n:ℝ)⁻¹*‖q‖)*‖z-y‖ := by
  have hc := negativeShiftedNorm_coefficient_le SpectralWeight.one r hr (-(n:ℤ)) n
    (endpointHillCorrectedMode SpectralWeight.one r hr hr1 n hn z hz q hs n -
      endpointHillCorrectedMode SpectralWeight.one r hr hr1 n hn y hy q hs n)
  have ht := negativeShiftedNorm_endpointHillCorrectedMode_sub_le SpectralWeight.one r hr hr1
    n hn z y hz hy q hs n (Or.inl rfl)
  have h := hc.trans ht
  rw [endpointHillCorrectedMode_pos, endpointHillCorrectedMode_pos,
    WeightedCoeff.sub_val, add_neg_cancel] at h
  unfold endpointDiagonal
  rw [endpointEffectiveFamily_eq r hr hr1 n hn (q,z) hz hs,
    endpointEffectiveFamily_eq r hr hr1 n hn (q,y) hy hs]
  simpa only [SpectralWeight.negativeSobolev_apply, SpectralWeight.one_apply,
    Weight.sobolev_apply, Int.cast_zero, abs_zero, add_zero, Real.one_rpow, div_one, one_mul] using h

/-- The original cutoff already makes the actual diagonal a strict contraction in lambda. -/
theorem endpointDiagonal_sub_le_eighth (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (n : ℕ) (hn : 1 ≤ n) (z y : ℂ)
    (hz : z ∈ reducedHillStrip n) (hy : y ∈ reducedHillStrip n)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤)
    (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2) :
    ‖endpointDiagonal r hr hr1 n (q,z)-endpointDiagonal r hr hr1 n (q,y)‖ ≤
      (1/8:ℝ)*‖z-y‖ := by
  have hnpos : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hS : 1 ≤ Weight.sobolev r (2*(n:ℤ)) :=
    Real.one_le_rpow (le_add_of_nonneg_right (abs_nonneg _)) hr
  have hM := endpoint_effective_column_small r hr hr1 n hn q hs
  have hSQ : Real.sqrt (n:ℝ) ≤ n := Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith⟩
  have hq : ‖q‖ ≤ (n:ℝ)/16 := by
    have h := mul_le_mul_of_nonneg_right hS (norm_nonneg q)
    nlinarith
  have hfrac : ‖q‖/(n:ℝ) ≤ 1/16 := (div_le_iff₀ hnpos).mpr (by linarith)
  have hc : 4*(endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖)*(n:ℝ)⁻¹*‖q‖ ≤ (1/8:ℝ) := by
    calc
      _ = 4*(endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖)*(‖q‖/(n:ℝ)) := by ring
      _ ≤ 4*(1/2:ℝ)*(‖q‖/(n:ℝ)) := by
        gcongr
      _ ≤ 4*(1/2:ℝ)*(1/16) := by gcongr
      _ = _ := by norm_num
  exact (endpointDiagonal_sub_le r hr hr1 n hn z y hz hy q hs).trans
    (mul_le_mul_of_nonneg_right hc (norm_nonneg _))

end NLS.KdV
