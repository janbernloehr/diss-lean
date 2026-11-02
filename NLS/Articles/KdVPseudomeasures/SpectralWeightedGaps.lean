import NLS.Articles.KdVPseudomeasures.SourceWeightedSpectral

/-!
# Theorem2.1(i): the full original weighted complex canonical gaps

The actual lexicographic spectral labels are used without truncation.
All source spectral weights and the exact original infinity norms are retained.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal Classical
namespace NLS.Articles.KdVPseudomeasures
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue NLS.KdV

/-- The weighted source uses exactly the same actual original canonical gaps. -/
def sourceWeightedCanonicalGapValues (w : SpectralWeight) (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev r) ⊤) (k : ℤ) : ℂ :=
  sourceComplexCanonicalGapValues r hr (sourceForgetWeight w r q) k

/-- The actual high slots retain the entire general source spectral weight. -/
theorem norm_sourceWeightedCanonicalGapValues_high_le (w : SpectralWeight) (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev r) ⊤) (N : ℕ)
    (h : SourceHillComplexLabeling r hr (sourceForgetWeight w r q) N
      (sourceHillComplexLabels r hr (sourceForgetWeight w r q)))
    (k : ℤ) (hk : N ≤ k.natAbs)
    (hs : endpointHillConstant r*(k.natAbs:ℝ)^(r-1/2)*‖q‖ ≤ 1/2) :
    ‖(w.negativeSobolev r k:ℂ)*sourceWeightedCanonicalGapValues w r hr q k‖ ≤ 6*Real.sqrt 6*‖q‖ := by
  have hN := h.cutoff_ge_two
  have hk0 : k ≠ 0 := by intro he; rw [he, Int.natAbs_zero] at hk; omega
  obtain ⟨p, hl, hrr⟩ := h.high_pair k.natAbs hk
  have hg := EndpointHillComplexPair.general_weighted_gap_le w r hr.1 hr.2 k.natAbs (by omega)
    (sourceWeightedEndpointCoefficients w r q) (by simpa only [norm_sourceWeightedEndpointCoefficients] using hs)
  rw [← sourceEndpointCoefficients_forgetWeight w r q] at hg
  have hgap := hg p
  have hW : w.negativeSobolev r k = w.negativeSobolev r (k.natAbs:ℤ) := by
    simp only [Int.natCast_natAbs, SpectralWeight.negativeSobolev_apply, SpectralWeight.apply_abs,
      Weight.sobolev_apply, Int.cast_abs, abs_abs]
  rw [sourceWeightedCanonicalGapValues, sourceComplexCanonicalGapValues, if_neg hk0,
    hl, hrr, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos ((w.negativeSobolev r).positive k), hW]
  simpa only [norm_sourceWeightedEndpointCoefficients] using hgap

/-- Explicit bound for all modes, including the finite original central block. -/
def sourceWeightedCanonicalGapBound (w : SpectralWeight) (r : ℝ) (hr : AdmissiblePredualOrder r)
    (R : ℝ) (N : ℕ) : ℝ :=
  w N*(8*sourceSpectralBound r hr R+4*freeHillValue N)+6*Real.sqrt 6*R

/-- The full actual canonical sequence has a bound in the genuine weighted infinity norm. -/
theorem norm_sourceWeightedCanonicalGapValues_le (w : SpectralWeight) (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev r) ⊤) (R : ℝ) (hq : ‖q‖ ≤ R) (N : ℕ)
    (h : SourceHillComplexLabeling r hr (sourceForgetWeight w r q) N
      (sourceHillComplexLabels r hr (sourceForgetWeight w r q)))
    (hs : ∀ n : ℕ, N ≤ n → endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2) (k : ℤ) :
    ‖(w.negativeSobolev r k:ℂ)*sourceWeightedCanonicalGapValues w r hr q k‖ ≤
      sourceWeightedCanonicalGapBound w r hr R N := by
  have hR : 0 ≤ R := (norm_nonneg q).trans hq
  have hB := sourceSpectralBound_nonneg r hr R
  have hfree : 0 ≤ freeHillValue N := by unfold freeHillValue; positivity
  have hw := (w.positive (N:ℤ)).le
  have hN := h.cutoff_ge_two
  by_cases hk : N ≤ k.natAbs
  · have ht := (norm_sourceWeightedCanonicalGapValues_high_le w r hr q N h k hk (hs k.natAbs hk)).trans
      (mul_le_mul_of_nonneg_left hq (by positivity : 0 ≤ 6*Real.sqrt 6))
    exact ht.trans (by unfold sourceWeightedCanonicalGapBound; nlinarith)
  · by_cases hk0 : k = 0
    · subst k
      simp only [sourceWeightedCanonicalGapValues, sourceComplexCanonicalGapValues_zero, mul_zero, norm_zero]
      unfold sourceWeightedCanonicalGapBound
      positivity
    · have hu (j : ℕ) (hj : j < 2*N-1) :
          ‖sourceHillComplexLabels r hr (sourceForgetWeight w r q) j‖ ≤
            2*freeHillValue N+4*sourceSpectralBound r hr R := by
        have hh := sourceHillSpectrum_norm_le_on_ball r hr R (sourceForgetWeight w r q)
          ((norm_sourceForgetWeight_le w r q).trans hq) _ (h.spectral j)
        have hc := h.central_below j hj
        linarith
      have hgap : ‖sourceWeightedCanonicalGapValues w r hr q k‖ ≤
          4*freeHillValue N+8*sourceSpectralBound r hr R := by
        rw [sourceWeightedCanonicalGapValues, sourceComplexCanonicalGapValues, if_neg hk0]
        have ht := norm_sub_le (sourceHillComplexLabels r hr (sourceForgetWeight w r q) (2*k.natAbs))
          (sourceHillComplexLabels r hr (sourceForgetWeight w r q) (2*k.natAbs-1))
        linarith [hu (2*k.natAbs) (by omega), hu (2*k.natAbs-1) (by omega)]
      have hW : w.negativeSobolev r k ≤ w N := by
        have hkw : w k ≤ w N := by
          have hh := w.monotone_nat (show k.natAbs ≤ N by omega)
          simpa only [Int.natCast_natAbs, SpectralWeight.apply_abs] using hh
        rw [SpectralWeight.negativeSobolev_eq_product]
        have hp : Weight.sobolev (-r) k ≤ 1 :=
          Real.rpow_le_one_of_one_le_of_nonpos (le_add_of_nonneg_right (abs_nonneg _)) (neg_nonpos.mpr hr.1)
        exact (mul_le_mul_of_nonneg_left hp (w.positive k).le).trans (by simpa only [mul_one] using hkw)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ((w.negativeSobolev r).positive k)]
      have he := mul_le_mul hW hgap (norm_nonneg _) hw
      exact he.trans (by unfold sourceWeightedCanonicalGapBound; nlinarith [Real.sqrt_nonneg 6])

/-- The entire original canonical gap sequence has arbitrary source-weight regularity. -/
theorem sourceWeightedCanonicalGapValues_mem (w : SpectralWeight) (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev r) ⊤) :
    Memℓp (fun k => (w.negativeSobolev r k:ℂ)*sourceWeightedCanonicalGapValues w r hr q k) ⊤ := by
  obtain ⟨N, _, hcut, hlabel⟩ := source_uniform_canonical_complex_labels_with_contraction r hr ‖q‖
  have h := hlabel (sourceForgetWeight w r q) (norm_sourceForgetWeight_le w r q)
  have hs (n : ℕ) (hn : N ≤ n) : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2 := by
    have he := hcut n hn
    have hp : 0 ≤ endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ := by
      positivity [endpointHillConstant_pos r hr.2]
    nlinarith
  apply memℓp_infty
  refine ⟨sourceWeightedCanonicalGapBound w r hr ‖q‖ N, ?_⟩
  rintro _ ⟨k, rfl⟩
  exact norm_sourceWeightedCanonicalGapValues_le w r hr q ‖q‖ le_rfl N h hs k

/-- The actual complete weighted canonical gaps, rather than an assumed or truncated sequence. -/
def sourceWeightedCanonicalGaps (w : SpectralWeight) (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev r) ⊤) : WeightedCoeff (w.negativeSobolev r) ⊤ :=
  ⟨sourceWeightedCanonicalGapValues w r hr q, sourceWeightedCanonicalGapValues_mem w r hr q⟩

@[simp] theorem sourceWeightedCanonicalGaps_apply (w : SpectralWeight) (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev r) ⊤) (k : ℤ) :
    (sourceWeightedCanonicalGaps w r hr q).val k = sourceWeightedCanonicalGapValues w r hr q k := rfl

/-- Explicit full norm bound for any common actual labeling cutoff and weighted contraction. -/
theorem norm_sourceWeightedCanonicalGaps_le (w : SpectralWeight) (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev r) ⊤) (R : ℝ) (hq : ‖q‖ ≤ R) (N : ℕ)
    (h : SourceHillComplexLabeling r hr (sourceForgetWeight w r q) N
      (sourceHillComplexLabels r hr (sourceForgetWeight w r q)))
    (hs : ∀ n : ℕ, N ≤ n → endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2) :
    ‖sourceWeightedCanonicalGaps w r hr q‖ ≤ sourceWeightedCanonicalGapBound w r hr R N := by
  have hR : 0 ≤ R := (norm_nonneg q).trans hq
  have hB := sourceSpectralBound_nonneg r hr R
  have hfree : 0 ≤ freeHillValue N := by unfold freeHillValue; positivity
  have hw := (w.positive (N:ℤ)).le
  change ‖WeightedCoeff.weightEquiv (w.negativeSobolev r) ⊤ _‖ ≤ _
  apply lp.norm_le_of_forall_le (by unfold sourceWeightedCanonicalGapBound; positivity)
  intro k
  exact norm_sourceWeightedCanonicalGapValues_le w r hr q R hq N h hs k

/-- ONE cutoff is chosen before BOTH the source weight and potential; the full actual
gap map is bounded on every exact original weighted norm ball. -/
theorem source_uniform_weighted_canonical_gap_bound (r : ℝ) (hr : AdmissiblePredualOrder r) (R : ℝ) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ w : SpectralWeight,
      ∀ q : PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev r) ⊤, ‖q‖ ≤ R →
        ‖sourceWeightedCanonicalGaps w r hr q‖ ≤ |sourceWeightedCanonicalGapBound w r hr R N| := by
  obtain ⟨N, hN, hcut, hlabel⟩ := source_uniform_canonical_complex_labels_with_contraction r hr R
  refine ⟨N, hN, fun w q hq => ?_⟩
  have h := hlabel (sourceForgetWeight w r q) ((norm_sourceForgetWeight_le w r q).trans hq)
  apply (norm_sourceWeightedCanonicalGaps_le w r hr q R hq N h ?_).trans (le_abs_self _)
  intro n hn
  have he := mul_le_mul_of_nonneg_left hq
    (show 0 ≤ endpointHillConstant r*(n:ℝ)^(r-1/2) by positivity [endpointHillConstant_pos r hr.2])
  have hp : 0 ≤ endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ := by positivity [endpointHillConstant_pos r hr.2]
  have hc := hcut n hn
  nlinarith

/-- Source Theorem2.1(i): actual canonical gaps have full general-weight endpoint
regularity,and the resulting map is bounded on every original weighted norm ball. -/
theorem sourceTheorem2_1_i (w : SpectralWeight) (r : ℝ) (hr : AdmissiblePredualOrder r) :
    (∀ q : PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev r) ⊤,
      Memℓp (fun k => (w.negativeSobolev r k:ℂ)*sourceWeightedCanonicalGapValues w r hr q k) ⊤) ∧
      ∀ R : ℝ, ∃ C : ℝ, 0 ≤ C ∧
        ∀ q : PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev r) ⊤, ‖q‖ ≤ R →
          ‖sourceWeightedCanonicalGaps w r hr q‖ ≤ C := by
  refine ⟨sourceWeightedCanonicalGapValues_mem w r hr, fun R => ?_⟩
  obtain ⟨N, _, hN⟩ := source_uniform_weighted_canonical_gap_bound r hr R
  exact ⟨|sourceWeightedCanonicalGapBound w r hr R N|, abs_nonneg _, hN w⟩

@[simp] theorem sourceWeightedCanonicalGapValues_zero (w : SpectralWeight) (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev r) ⊤) :
    sourceWeightedCanonicalGapValues w r hr q 0 = 0 :=
  sourceComplexCanonicalGapValues_zero _ _ _

theorem sourceWeightedCanonicalGapValues_neg (w : SpectralWeight) (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev r) ⊤) (k : ℤ) :
    sourceWeightedCanonicalGapValues w r hr q (-k) = sourceWeightedCanonicalGapValues w r hr q k :=
  sourceComplexCanonicalGapValues_neg _ _ _ _

/-- The positive-index target is exactly the source's gamma_n=lambda_n^+-lambda_n^-.
Both labels refer to the SAME original physical distribution by sourceForgetWeight_val. -/
theorem sourceWeightedCanonicalGaps_nat_apply (w : SpectralWeight) (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev r) ⊤) (n : ℕ) (hn : 1 ≤ n) :
    (sourceWeightedCanonicalGaps w r hr q).val n =
      sourceHillComplexLabels r hr (sourceForgetWeight w r q) (2*n)-
        sourceHillComplexLabels r hr (sourceForgetWeight w r q) (2*n-1) := by
  have hn0 : (n:ℤ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  simp only [sourceWeightedCanonicalGaps_apply, sourceWeightedCanonicalGapValues,
    sourceComplexCanonicalGapValues, if_neg hn0, Int.natAbs_natCast]

/-- Literal local boundedness of the actual canonical gap map in the ORIGINAL weighted norm topology. -/
theorem sourceWeightedCanonicalGaps_locallyBounded (w : SpectralWeight) (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev r) ⊤) :
    ∃ U ∈ 𝓝 q, ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ U, ‖sourceWeightedCanonicalGaps w r hr p‖ ≤ C := by
  obtain ⟨C, hC, hc⟩ := (sourceTheorem2_1_i w r hr).2 (‖q‖+1)
  refine ⟨Metric.ball q 1, Metric.ball_mem_nhds q (by norm_num), C, hC, fun p hp => hc p ?_⟩
  have hd : ‖p-q‖ < 1 := by simpa only [Metric.mem_ball, dist_eq_norm] using hp
  have ht := norm_le_norm_sub_add p q
  linarith

end NLS.Articles.KdVPseudomeasures
