import NLS.Articles.KdVPseudomeasures.SpectralComplexCanonical
import NLS.Articles.KdVPseudomeasures.SpectralCanonicalGaps

/-! Full actual complex canonical gaps in the endpoint infinity Sobolev space (unit extra weight). -/
noncomputable section
open Set
open scoped ENNReal Classical
namespace NLS.Articles.KdVPseudomeasures
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue NLS.KdV

/-- The actual lexicographic gaps, extended evenly to signed indices and zero at0. -/
def sourceComplexCanonicalGapValues (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) (k : ℤ) : ℂ :=
  if k = 0 then 0 else sourceHillComplexLabels r hr q (2*k.natAbs)-sourceHillComplexLabels r hr q (2*k.natAbs-1)

@[simp] theorem sourceComplexCanonicalGapValues_zero (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) : sourceComplexCanonicalGapValues r hr q 0 = 0 := by
  simp [sourceComplexCanonicalGapValues]

theorem sourceComplexCanonicalGapValues_neg (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) (k : ℤ) :
    sourceComplexCanonicalGapValues r hr q (-k) = sourceComplexCanonicalGapValues r hr q k := by
  simp only [sourceComplexCanonicalGapValues, neg_eq_zero, Int.natAbs_neg]

/-- Uniform high-slot gap control, now for the source's ACTUAL complex canonical labels. -/
theorem norm_sourceComplexCanonicalGapValues_high_le (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) (N : ℕ)
    (h : SourceHillComplexLabeling r hr q N (sourceHillComplexLabels r hr q)) (k : ℤ) (hk : N ≤ k.natAbs) :
    ‖(Weight.sobolev (-r) k:ℂ)*sourceComplexCanonicalGapValues r hr q k‖ ≤ 6*Real.sqrt 6*‖q‖ := by
  have hN := h.cutoff_ge_two
  have hk0 : k ≠ 0 := by intro he; rw [he, Int.natAbs_zero] at hk; omega
  obtain ⟨p, hl, hrr⟩ := h.high_pair k.natAbs hk
  have hsmall := endpointHill_small_of_wide_small r hr.2 k.natAbs (sourceEndpointCoefficients r q)
    (by simpa only [norm_sourceEndpointCoefficients] using h.cutoff_small k.natAbs hk)
  have hgap := EndpointHillComplexPair.weighted_gap_le r hr.1 hr.2 k.natAbs
    (sourceEndpointCoefficients r q) (by omega) hsmall p
  have hW : Weight.sobolev (-r) k = Weight.sobolev (-r) (k.natAbs:ℤ) := by
    simp only [Weight.sobolev_apply, Int.cast_natCast]
    rw [Nat.cast_natAbs, Int.cast_abs, abs_abs]
  rw [sourceComplexCanonicalGapValues, if_neg hk0, hl, hrr, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos ((Weight.sobolev (-r)).positive k), hW]
  simpa only [norm_sourceEndpointCoefficients] using hgap

/-- A bound for the entire complex gap sequence, including its actual central prefix. -/
def sourceComplexCanonicalGapBound (r : ℝ) (hr : AdmissiblePredualOrder r) (R : ℝ) (N : ℕ) : ℝ :=
  8*sourceSpectralBound r hr R+4*freeHillValue N+6*Real.sqrt 6*R

/-- Exact original potential norm balls control every weighted canonical complex gap coefficient. -/
theorem norm_sourceComplexCanonicalGapValues_le (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) (R : ℝ) (hq : ‖q‖ ≤ R) (N : ℕ)
    (h : SourceHillComplexLabeling r hr q N (sourceHillComplexLabels r hr q)) (k : ℤ) :
    ‖(Weight.sobolev (-r) k:ℂ)*sourceComplexCanonicalGapValues r hr q k‖ ≤
      sourceComplexCanonicalGapBound r hr R N := by
  have hR : 0 ≤ R := (norm_nonneg q).trans hq
  have hB := sourceSpectralBound_nonneg r hr R
  have hfree : 0 ≤ freeHillValue N := by unfold freeHillValue; positivity
  have hN := h.cutoff_ge_two
  by_cases hk : N ≤ k.natAbs
  · have ht := (norm_sourceComplexCanonicalGapValues_high_le r hr q N h k hk).trans
      (mul_le_mul_of_nonneg_left hq (by positivity : 0 ≤ 6*Real.sqrt 6))
    exact ht.trans (by unfold sourceComplexCanonicalGapBound; linarith)
  · by_cases hk0 : k = 0
    · subst k
      rw [sourceComplexCanonicalGapValues_zero, mul_zero, norm_zero]
      unfold sourceComplexCanonicalGapBound
      positivity
    · have hu (j : ℕ) (hj : j < 2*N-1) : ‖sourceHillComplexLabels r hr q j‖ ≤
          2*freeHillValue N+4*sourceSpectralBound r hr R := by
        have hs := sourceHillSpectrum_norm_le_on_ball r hr R q hq
          (sourceHillComplexLabels r hr q j) (h.spectral j)
        have hc := h.central_below j hj
        linarith
      have hgap : ‖sourceHillComplexLabels r hr q (2*k.natAbs)-sourceHillComplexLabels r hr q (2*k.natAbs-1)‖ ≤
          4*freeHillValue N+8*sourceSpectralBound r hr R := by
        have ht := norm_sub_le (sourceHillComplexLabels r hr q (2*k.natAbs))
          (sourceHillComplexLabels r hr q (2*k.natAbs-1))
        linarith [hu (2*k.natAbs) (by omega), hu (2*k.natAbs-1) (by omega)]
      have hW : Weight.sobolev (-r) k ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (le_add_of_nonneg_right (abs_nonneg _)) (neg_nonpos.mpr hr.1)
      rw [sourceComplexCanonicalGapValues, if_neg hk0, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos ((Weight.sobolev (-r)).positive k)]
      apply (mul_le_of_le_one_left (norm_nonneg _) hW).trans
      exact hgap.trans (by unfold sourceComplexCanonicalGapBound; nlinarith [Real.sqrt_nonneg 6])

/-- All actual complex canonical gaps lie in the genuine endpoint infinity space. -/
theorem sourceComplexCanonicalGapValues_mem (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) :
    Memℓp (fun k => (Weight.sobolev (-r) k:ℂ)*sourceComplexCanonicalGapValues r hr q k) ⊤ := by
  apply memℓp_infty
  refine ⟨sourceComplexCanonicalGapBound r hr ‖q‖ (sourceHillComplexLabelCutoff r hr q), ?_⟩
  rintro _ ⟨k, rfl⟩
  exact norm_sourceComplexCanonicalGapValues_le r hr q ‖q‖ le_rfl _ (sourceHillComplexLabels_spec r hr q) k

/-- The complete actual original complex canonical gap sequence, without truncation. -/
def sourceComplexCanonicalGaps (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) : WeightedCoeff (Weight.sobolev (-r)) ⊤ :=
  ⟨sourceComplexCanonicalGapValues r hr q, sourceComplexCanonicalGapValues_mem r hr q⟩

/-- An explicit full infinity norm bound on every original complex norm ball. -/
theorem norm_sourceComplexCanonicalGaps_le (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) (R : ℝ) (hq : ‖q‖ ≤ R) (N : ℕ)
    (h : SourceHillComplexLabeling r hr q N (sourceHillComplexLabels r hr q)) :
    ‖sourceComplexCanonicalGaps r hr q‖ ≤ sourceComplexCanonicalGapBound r hr R N := by
  have hR : 0 ≤ R := (norm_nonneg q).trans hq
  have hB := sourceSpectralBound_nonneg r hr R
  have hfree : 0 ≤ freeHillValue N := by unfold freeHillValue; positivity
  change ‖WeightedCoeff.weightEquiv (Weight.sobolev (-r)) ⊤ _‖ ≤ _
  apply lp.norm_le_of_forall_le (by unfold sourceComplexCanonicalGapBound; positivity)
  intro k
  exact norm_sourceComplexCanonicalGapValues_le r hr q R hq N h k

/-- The full actual complex canonical gap map is bounded on each exact original norm ball. -/
theorem source_uniform_complex_canonical_gap_bound (r : ℝ) (hr : AdmissiblePredualOrder r) (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q : FourierLebesgueSpace (2:ℝ) (-r) ⊤, ‖q‖ ≤ R →
      ‖sourceComplexCanonicalGaps r hr q‖ ≤ C := by
  obtain ⟨N, _, hN⟩ := source_uniform_canonical_complex_labels r hr R
  exact ⟨|sourceComplexCanonicalGapBound r hr R N|, abs_nonneg _, fun q hq =>
    (norm_sourceComplexCanonicalGaps_le r hr q R hq N (hN q hq)).trans (le_abs_self _)⟩

/-- On original real physical potentials, the complex gap coefficients are exactly the existing gaps. -/
theorem sourceComplexCanonicalGapValues_ofPotential (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : Potential r) (k : ℤ) : sourceComplexCanonicalGapValues r hr q.val k = sourceCanonicalGapValues r hr q k := by
  simp only [sourceComplexCanonicalGapValues, sourceCanonicalGapValues, sourceHillComplexLabels_ofPotential]
  split_ifs <;> simp only [Complex.ofReal_sub]

end NLS.Articles.KdVPseudomeasures
