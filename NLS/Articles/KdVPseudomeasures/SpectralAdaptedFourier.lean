import NLS.Articles.KdVPseudomeasures.SpectralAdaptedCoefficients
import NLS.SequenceSpaces.EvenTailReplacement

/-!
The actual adapted Fourier map in the original distribution spaces.
On the verified balls its total realization has exactly the physical
couplings at alpha in every high even mode; all other modes are preserved.
-/
noncomputable section
open Set Metric
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
open NLS.Fourier NLS.Fourier.SmoothPeriodicTest NLS.Fourier.PeriodicFourierLebesgue NLS.KdV

/-- The intrinsic physical pair at alpha; the unused n=0 slot is zero. -/
def sourceAdaptedPair (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) (n : ℕ) : ℂ × ℂ :=
  if hn : 1 ≤ n then (sourceEndpointEntries r hr n (q,sourceDiagonalRoot r hr n hn q)).2 else 0

/-- Raw original Fourier coefficients of the actual adapted map. -/
def sourceAdaptedFourierValues (r : ℝ) (hr : AdmissiblePredualOrder r) (N : ℕ)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) : ℤ → ℂ :=
  evenTailReplacement N (fun k => q.val (mode (-k))) (sourceAdaptedPair r hr q)

/-- Analyticity of every actual raw coefficient in each original weighted norm. -/
theorem analyticAt_sourceAdaptedFourierValues (w : SpectralWeight) (r : ℝ)
    (hr : AdmissiblePredualOrder r) (N : ℕ)
    (q : PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev r) ⊤)
    (hs : ∀ n : ℕ, 1 ≤ n → N ≤ n → endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ < 1/2)
    (k : ℤ) : AnalyticAt ℂ (fun p => sourceAdaptedFourierValues r hr N (sourceForgetWeight w r p) k) q := by
  classical
  unfold sourceAdaptedFourierValues evenTailReplacement
  split_ifs with hk hsign
  · have ha := analyticAt_sourceAdaptedCouplings w r hr _ hk.2.1 q (hs _ hk.2.1 hk.2.2)
    have hp := (analyticAt_fst (𝕜 := ℂ) (p := sourceAdaptedCouplings w r hr (k.natAbs/2) hk.2.1 q)).comp
      (f := sourceAdaptedCouplings w r hr (k.natAbs/2) hk.2.1) ha
    simpa only [sourceAdaptedPair, dif_pos hk.2.1, sourceAdaptedCouplings,
      sourceWeightedDiagonalRoot, Function.comp_def] using hp
  · have ha := analyticAt_sourceAdaptedCouplings w r hr _ hk.2.1 q (hs _ hk.2.1 hk.2.2)
    have hp := (analyticAt_snd (𝕜 := ℂ) (p := sourceAdaptedCouplings w r hr (k.natAbs/2) hk.2.1 q)).comp
      (f := sourceAdaptedCouplings w r hr (k.natAbs/2) hk.2.1) ha
    simpa only [sourceAdaptedPair, dif_pos hk.2.1, sourceAdaptedCouplings,
      sourceWeightedDiagonalRoot, Function.comp_def] using hp
  · have he : (fun p => (sourceForgetWeight w r p).val (mode (-k))) =
        (fun p => (sourceWeightedEndpointCoefficients w r p).val k) := by
      funext p
      rw [sourceForgetWeight_val, sourceWeightedEndpointCoefficients_apply]
    rw [he]
    exact ((WeightedCoeff.evalCLM (w.negativeSobolev r) ⊤ k).analyticAt _).comp
      (f := (coefficientsIsometry (L := (2:ℝ)) (w.negativeSobolev r) ⊤
        (w.hasTemperedInverse_negativeSobolev r)).toContinuousLinearEquiv.toContinuousLinearMap)
      ((coefficientsIsometry (L := (2:ℝ)) (w.negativeSobolev r) ⊤
        (w.hasTemperedInverse_negativeSobolev r)).toContinuousLinearEquiv.toContinuousLinearMap.analyticAt q)

/-- Realization in the exact original weighted distribution space. The fallback
outside the verified domain is only used to give a total function. -/
def sourceWeightedAdaptedFourier (w : SpectralWeight) (r : ℝ)
    (hr : AdmissiblePredualOrder r) (N : ℕ)
    (q : PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev r) ⊤) :
    PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev r) ⊤ :=
  (coefficientsIsometry _ _ (w.hasTemperedInverse_negativeSobolev r)).symm
    (WeightedCoeff.ofFunctionOrZero (w.negativeSobolev r) ⊤
      (sourceAdaptedFourierValues r hr N (sourceForgetWeight w r q)))

/-- Uniform smallness of the actual physical tails produces their genuine
weighted realization and a quantitative distance from the identity. -/
theorem sourceWeightedAdaptedFourier_spec (w : SpectralWeight) (r : ℝ)
    (hr : AdmissiblePredualOrder r) (N : ℕ) (R : ℝ) (hR : 0 ≤ R)
    (hcut : ∀ n : ℕ, 1 ≤ n → N ≤ n → endpointHillConstant r*(n:ℝ)^(r-1/2)*(64*R) ≤ 1/2)
    (q : PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev r) ⊤) (hq : ‖q‖ ≤ R) :
    (∀ k : ℤ, (sourceWeightedAdaptedFourier w r hr N q).val (mode (-k)) =
      sourceAdaptedFourierValues r hr N (sourceForgetWeight w r q) k) ∧
    ‖sourceWeightedAdaptedFourier w r hr N q-q‖ ≤ R/64 := by
  have hε : 0 ≤ R/64 := by positivity
  have hb (n : ℕ) (hn : 1 ≤ n) (hN : N ≤ n) :
      (w.negativeSobolev r) (2*(n:ℤ))*‖(sourceAdaptedPair r hr (sourceForgetWeight w r q) n).1-
        (sourceWeightedEndpointCoefficients w r q).val (2*(n:ℤ))‖ ≤ R/64 ∧
      (w.negativeSobolev r) (2*(n:ℤ))*‖(sourceAdaptedPair r hr (sourceForgetWeight w r q) n).2-
        (sourceWeightedEndpointCoefficients w r q).val (-(2*(n:ℤ)))‖ ≤ R/64 := by
    let c := endpointHillConstant r*(n:ℝ)^(r-1/2)
    have hc : 0 ≤ c := by dsimp [c]; positivity [endpointHillConstant_pos r hr.2]
    have hh := hcut n hn hN
    change c*(64*R) ≤ 1/2 at hh
    have hsmall : c*‖q‖ ≤ 1/2 := by nlinarith [mul_le_mul_of_nonneg_left hq hc]
    have he := sourceAdaptedCouplings_weighted_errors w r hr n hn q hsmall
    have hbound : 2*(c*‖q‖)*‖q‖ ≤ R/64 := by
      have hsq := mul_le_mul_of_nonneg_left (mul_self_le_mul_self (norm_nonneg q) hq) hc
      have hscale := mul_le_mul_of_nonneg_right hh hR
      nlinarith
    have hp : sourceAdaptedPair r hr (sourceForgetWeight w r q) n = sourceAdaptedCouplings w r hr n hn q := by
      simp only [sourceAdaptedPair, dif_pos hn, sourceAdaptedCouplings, sourceWeightedDiagonalRoot]
    simpa only [hp, sourceWeightedEndpointCoefficients_apply, neg_neg] using
      And.intro (he.1.trans hbound) (he.2.trans hbound)
  obtain ⟨b, hbcoord, hbnd⟩ := WeightedCoeff.exists_evenTailReplacement
    (w.negativeSobolev r) (fun k => by simp only [SpectralWeight.negativeSobolev_neg])
    N (sourceWeightedEndpointCoefficients w r q) (sourceAdaptedPair r hr (sourceForgetWeight w r q))
    (R/64) hε hb
  have hcoord (k : ℤ) : b.val k = sourceAdaptedFourierValues r hr N (sourceForgetWeight w r q) k := by
    rw [hbcoord, sourceAdaptedFourierValues]
    congr 2
    funext j
    rw [sourceWeightedEndpointCoefficients_apply, sourceForgetWeight_val]
  have he : sourceWeightedEndpointCoefficients w r (sourceWeightedAdaptedFourier w r hr N q) = b := by
    unfold sourceWeightedEndpointCoefficients sourceWeightedAdaptedFourier
    rw [LinearIsometryEquiv.apply_symm_apply]
    exact WeightedCoeff.ofFunctionOrZero_eq_of_coordinates _ _ b hcoord
  refine ⟨?_, ?_⟩
  · intro k
    rw [← sourceWeightedEndpointCoefficients_apply, he, hcoord]
  · rw [← norm_sourceWeightedEndpointCoefficients w r (sourceWeightedAdaptedFourier w r hr N q-q)]
    change ‖sourceWeightedEndpointCoefficients w r (sourceWeightedAdaptedFourier w r hr N q)-
      sourceWeightedEndpointCoefficients w r q‖ ≤ R/64
    rwa [he]

/-- Banach-valued complex analyticity in the exact original weighted norm,
including exponent infinity; scalar analyticity alone is not the assertion. -/
theorem analyticOnNhd_sourceWeightedAdaptedFourier (w : SpectralWeight) (r : ℝ)
    (hr : AdmissiblePredualOrder r) (N : ℕ) (R : ℝ) (hR : 0 < R)
    (hcut : ∀ n : ℕ, 1 ≤ n → N ≤ n → endpointHillConstant r*(n:ℝ)^(r-1/2)*(64*R) ≤ 1/2) :
    AnalyticOnNhd ℂ (sourceWeightedAdaptedFourier w r hr N) (ball 0 R) := by
  have ha (k : ℤ) : AnalyticOnNhd ℂ
      (fun q => sourceAdaptedFourierValues r hr N (sourceForgetWeight w r q) k) (ball 0 R) := by
    intro q hq
    apply analyticAt_sourceAdaptedFourierValues w r hr N q _ k
    intro n hn hN
    let c := endpointHillConstant r*(n:ℝ)^(r-1/2)
    have hc : 0 ≤ c := by dsimp [c]; positivity [endpointHillConstant_pos r hr.2]
    have hh := hcut n hn hN
    change c*(64*R) ≤ 1/2 at hh
    have hqn : ‖q‖ ≤ R := (mem_ball_zero_iff.mp hq).le
    nlinarith [mul_le_mul_of_nonneg_left hqn hc]
  have hb (q : PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev r) ⊤) (hq : q ∈ ball 0 R) :
      ∃ b : WeightedCoeff (w.negativeSobolev r) ⊤,
        (∀ k, b.val k = sourceAdaptedFourierValues r hr N (sourceForgetWeight w r q) k) ∧
          ‖b‖ ≤ R/64+R := by
    have hqn : ‖q‖ ≤ R := (mem_ball_zero_iff.mp hq).le
    obtain ⟨hv, hn⟩ := sourceWeightedAdaptedFourier_spec w r hr N R hR.le hcut q hqn
    refine ⟨sourceWeightedEndpointCoefficients w r (sourceWeightedAdaptedFourier w r hr N q), ?_, ?_⟩
    · intro k
      rw [sourceWeightedEndpointCoefficients_apply, hv]
    · rw [norm_sourceWeightedEndpointCoefficients]
      exact (norm_le_norm_sub_add (sourceWeightedAdaptedFourier w r hr N q) q).trans
        (add_le_add hn hqn)
  obtain ⟨hA, _⟩ := WeightedCoeff.analytic_realization_of_bound (w.negativeSobolev r)
    (fun q => sourceAdaptedFourierValues r hr N (sourceForgetWeight w r q)) isOpen_ball ha (R/64+R) hb
  intro q hq
  exact ((coefficientsIsometry (L := (2:ℝ)) (w.negativeSobolev r) ⊤
    (w.hasTemperedInverse_negativeSobolev r)).symm.toContinuousLinearEquiv.toContinuousLinearMap.analyticAt _).comp
    (hA q hq)

@[simp] theorem sourceWeightedAdaptedFourier_zero (w : SpectralWeight) (r : ℝ)
    (hr : AdmissiblePredualOrder r) (N : ℕ) : sourceWeightedAdaptedFourier w r hr N 0 = 0 := by
  have hh := (sourceWeightedAdaptedFourier_spec w r hr N 0 le_rfl
    (by intro n hn hN; simp) 0 (by simp)).2
  simpa only [sub_zero, zero_div, norm_le_zero_iff] using hh

/-- One cutoff BEFORE BOTH weight and potential constructs the actual analytic
adapted Fourier map and its uniform near-identity bound on the full original ball. -/
theorem source_uniform_adaptedFourier (r : ℝ) (hr : AdmissiblePredualOrder r)
    (R : ℝ) (hR : 0 < R) :
    ∃ N : ℕ, 1 ≤ N ∧
      (∀ n : ℕ, 1 ≤ n → N ≤ n → endpointHillConstant r*(n:ℝ)^(r-1/2)*(64*R) ≤ 1/2) ∧
      ∀ w : SpectralWeight,
        AnalyticOnNhd ℂ (sourceWeightedAdaptedFourier w r hr N) (ball 0 R) ∧
        ∀ q : PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev r) ⊤, ‖q‖ ≤ R →
          (∀ k : ℤ, (sourceWeightedAdaptedFourier w r hr N q).val (mode (-k)) =
            sourceAdaptedFourierValues r hr N (sourceForgetWeight w r q) k) ∧
          ‖sourceWeightedAdaptedFourier w r hr N q-q‖ ≤ R/64 := by
  obtain ⟨N, hN, hcut⟩ := exists_endpointHill_cutoff r hr.2 (64*R)
  have hc := fun n (_ : 1 ≤ n) (hn : N ≤ n) => hcut n hn
  exact ⟨N, hN, hc, fun w => ⟨analyticOnNhd_sourceWeightedAdaptedFourier w r hr N R hR hc,
    sourceWeightedAdaptedFourier_spec w r hr N R hR.le hc⟩⟩

/-- The adapted map preserves the original mean and physical period-one condition. -/
theorem sourceWeightedAdaptedFourier_preserves_complex_source (w : SpectralWeight) (r : ℝ)
    (hr : AdmissiblePredualOrder r) (N : ℕ) (R : ℝ) (hR : 0 ≤ R)
    (hcut : ∀ n : ℕ, 1 ≤ n → N ≤ n → endpointHillConstant r*(n:ℝ)^(r-1/2)*(64*R) ≤ 1/2)
    (q : PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev r) ⊤) (hq : ‖q‖ ≤ R) :
    (sourceWeightedAdaptedFourier w r hr N q).val (mode 0) = q.val (mode 0) ∧
    (IsPeriodicDistribution 1 (sourceWeightedAdaptedFourier w r hr N q).val.toTempered ↔
      IsPeriodicDistribution 1 q.val.toTempered) := by
  have hv := (sourceWeightedAdaptedFourier_spec w r hr N R hR hcut q hq).1
  refine ⟨?_, ?_⟩
  · simpa only [neg_zero, sourceAdaptedFourierValues, evenTailReplacement_zero,
      sourceForgetWeight_val] using hv 0
  · rw [Distribution.toTempered_period_one_iff_odd, Distribution.toTempered_period_one_iff_odd]
    have he (k : ℤ) : (sourceWeightedAdaptedFourier w r hr N q).val (mode (-(2*k+1))) =
        q.val (mode (-(2*k+1))) := by
      simpa only [sourceAdaptedFourierValues, evenTailReplacement_odd, sourceForgetWeight_val] using hv (2*k+1)
    simp only [he]

/-- At every replaced pair these are exactly the original physical couplings
evaluated at the constructed alpha, with the source Fourier signs retained. -/
theorem sourceWeightedAdaptedFourier_high_pair (w : SpectralWeight) (r : ℝ)
    (hr : AdmissiblePredualOrder r) (N : ℕ) (R : ℝ) (hR : 0 ≤ R)
    (hcut : ∀ n : ℕ, 1 ≤ n → N ≤ n → endpointHillConstant r*(n:ℝ)^(r-1/2)*(64*R) ≤ 1/2)
    (q : PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev r) ⊤) (hq : ‖q‖ ≤ R)
    (n : ℕ) (hn : 1 ≤ n) (hN : N ≤ n) :
    (sourceWeightedAdaptedFourier w r hr N q).val (mode (-(2*(n:ℤ)))) =
        (sourceAdaptedCouplings w r hr n hn q).1 ∧
      (sourceWeightedAdaptedFourier w r hr N q).val (mode (2*(n:ℤ))) =
        (sourceAdaptedCouplings w r hr n hn q).2 := by
  have hv := (sourceWeightedAdaptedFourier_spec w r hr N R hR hcut q hq).1
  have hp : sourceAdaptedPair r hr (sourceForgetWeight w r q) n = sourceAdaptedCouplings w r hr n hn q := by
    simp only [sourceAdaptedPair, dif_pos hn, sourceAdaptedCouplings, sourceWeightedDiagonalRoot]
  constructor
  · rw [hv, sourceAdaptedFourierValues, evenTailReplacement_pos N n hn hN, hp]
  · have hh := hv (-(2*(n:ℤ)))
    simpa only [neg_neg, sourceAdaptedFourierValues, evenTailReplacement_neg N n hn hN, hp] using hh

/-- All low modes, including odd modes, agree with the entire original input distribution. -/
theorem sourceWeightedAdaptedFourier_low (w : SpectralWeight) (r : ℝ)
    (hr : AdmissiblePredualOrder r) (N : ℕ) (R : ℝ) (hR : 0 ≤ R)
    (hcut : ∀ n : ℕ, 1 ≤ n → N ≤ n → endpointHillConstant r*(n:ℝ)^(r-1/2)*(64*R) ≤ 1/2)
    (q : PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev r) ⊤) (hq : ‖q‖ ≤ R)
    (k : ℤ) (hk : k.natAbs/2 < N) :
    (sourceWeightedAdaptedFourier w r hr N q).val (mode (-k)) = q.val (mode (-k)) := by
  rw [(sourceWeightedAdaptedFourier_spec w r hr N R hR hcut q hq).1 k,
    sourceAdaptedFourierValues, evenTailReplacement_low N _ _ k hk, sourceForgetWeight_val]

/-- Changing the source weight does not change the adapted distribution.
This is equality on every original smooth test, not merely a norm comparison. -/
theorem sourceWeightedAdaptedFourier_weight_agreement (w v : SpectralWeight) (r : ℝ)
    (hr : AdmissiblePredualOrder r) (N : ℕ) (R : ℝ) (hR : 0 ≤ R)
    (hcut : ∀ n : ℕ, 1 ≤ n → N ≤ n → endpointHillConstant r*(n:ℝ)^(r-1/2)*(64*R) ≤ 1/2)
    (q : PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev r) ⊤)
    (p : PeriodicFourierLebesgue (2:ℝ) (v.negativeSobolev r) ⊤)
    (hq : ‖q‖ ≤ R) (hp : ‖p‖ ≤ R) (hval : q.val = p.val) :
    (sourceWeightedAdaptedFourier w r hr N q).val = (sourceWeightedAdaptedFourier v r hr N p).val := by
  have he : sourceForgetWeight w r q = sourceForgetWeight v r p := by
    apply Subtype.ext
    rw [sourceForgetWeight_val, sourceForgetWeight_val, hval]
  apply Distribution.ext_coefficients
  intro k
  rw [(sourceWeightedAdaptedFourier_spec w r hr N R hR hcut q hq).1 k,
    (sourceWeightedAdaptedFourier_spec v r hr N R hR hcut p hp).1 k, he]

end NLS.Articles.KdVPseudomeasures
