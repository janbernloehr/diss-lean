import NLS.Articles.KdVPseudomeasures.SpectralCanonicalLabels

/-! The complete canonical gap sequence in the original endpoint infinity Sobolev space. -/
noncomputable section
open Set
open scoped ENNReal Classical
namespace NLS.Articles.KdVPseudomeasures
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue NLS.KdV

/-- The full actual canonical gaps, extended evenly to signed modes with zero mean. -/
def sourceCanonicalGapValues (r : ℝ) (hr : AdmissiblePredualOrder r) (q : Potential r) (k : ℤ) : ℂ :=
  if k = 0 then 0 else
    ((sourceHillLabels r hr q (2*k.natAbs)-sourceHillLabels r hr q (2*k.natAbs-1):ℝ):ℂ)

@[simp] theorem sourceCanonicalGapValues_zero (r : ℝ) (hr : AdmissiblePredualOrder r) (q : Potential r) :
    sourceCanonicalGapValues r hr q 0 = 0 := by simp [sourceCanonicalGapValues]

theorem sourceCanonicalGapValues_neg (r : ℝ) (hr : AdmissiblePredualOrder r) (q : Potential r) (k : ℤ) :
    sourceCanonicalGapValues r hr q (-k) = sourceCanonicalGapValues r hr q k := by
  simp only [sourceCanonicalGapValues,neg_eq_zero,Int.natAbs_neg]

theorem sourceCanonicalGapValues_im (r : ℝ) (hr : AdmissiblePredualOrder r) (q : Potential r) (k : ℤ) :
    (sourceCanonicalGapValues r hr q k).im = 0 := by
  unfold sourceCanonicalGapValues
  split_ifs <;> rfl

/-- A norm-ball bound on ALL canonical gaps, including the finite central prefix. -/
def sourceCanonicalGapBound (r : ℝ) (hr : AdmissiblePredualOrder r) (R : ℝ) (N : ℕ) : ℝ :=
  sourceSpectralBound r hr R+freeHillValue N+6*Real.sqrt 6*R

/-- The old local-pair gap bound now controls the canonical high slots. -/
theorem norm_sourceCanonicalGapValues_high_le (r : ℝ) (hr : AdmissiblePredualOrder r) (q : Potential r)
    (N : ℕ) (hN : 2 ≤ N)
    (hs : ∀ n : ℕ, N ≤ n → 13*endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q.val‖ ≤ 1/2)
    (k : ℤ) (hk : N ≤ k.natAbs) :
    ‖(Weight.sobolev (-r) k:ℂ)*sourceCanonicalGapValues r hr q k‖ ≤ 6*Real.sqrt 6*‖q.val‖ := by
  have hk0 : k ≠ 0 := by intro he; rw [he,Int.natAbs_zero] at hk; omega
  obtain ⟨p,hl,hrr⟩ := (sourceHillLabels_spec_at r hr q N hN hs).high_pair k.natAbs hk
  have hn : 1 ≤ k.natAbs := by omega
  have hsmall := endpointHill_small_of_wide_small r hr.2 k.natAbs (sourceEndpointCoefficients r q.val)
    (by simpa only [norm_sourceEndpointCoefficients] using hs k.natAbs hk)
  have hgap := EndpointHillRealPair.weighted_gap_le r hr.1 hr.2 k.natAbs hn
    (sourceEndpointCoefficients r q.val) hsmall p
  have hW : Weight.sobolev (-r) k = Weight.sobolev (-r) (k.natAbs:ℤ) := by
    simp only [Weight.sobolev_apply,Int.cast_natCast]
    rw [Nat.cast_natAbs,Int.cast_abs,abs_abs]
  rw [sourceCanonicalGapValues,if_neg hk0,hl,hrr,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos ((Weight.sobolev (-r)).positive k),Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr p.ordered),hW]
  simpa only [EndpointHillRealPair.gap,norm_sourceEndpointCoefficients] using hgap

/-- Original potential norm balls control the entire genuine weighted infinity gap sequence. -/
theorem norm_sourceCanonicalGapValues_le (r : ℝ) (hr : AdmissiblePredualOrder r) (q : Potential r)
    (R : ℝ) (hq : ‖q.val‖ ≤ R) (N : ℕ) (hN : 2 ≤ N)
    (hs : ∀ n : ℕ, N ≤ n → 13*endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q.val‖ ≤ 1/2)
    (k : ℤ) : ‖(Weight.sobolev (-r) k:ℂ)*sourceCanonicalGapValues r hr q k‖ ≤
      sourceCanonicalGapBound r hr R N := by
  have hR : 0 ≤ R := (norm_nonneg q.val).trans hq
  have hB := sourceSpectralBound_nonneg r hr R
  have hfree : 0 ≤ freeHillValue N := by unfold freeHillValue; positivity
  have htail : 0 ≤ 6*Real.sqrt 6*R := by positivity
  by_cases hk : N ≤ k.natAbs
  · have h := (norm_sourceCanonicalGapValues_high_le r hr q N hN hs k hk).trans
      (mul_le_mul_of_nonneg_left hq (by positivity : 0 ≤ 6*Real.sqrt 6))
    exact h.trans (by unfold sourceCanonicalGapBound; linarith)
  · by_cases hk0 : k = 0
    · subst k
      rw [sourceCanonicalGapValues_zero,mul_zero,norm_zero]
      unfold sourceCanonicalGapBound
      positivity
    · have hgap : 0 ≤ sourceHillLabels r hr q (2*k.natAbs)-sourceHillLabels r hr q (2*k.natAbs-1) :=
        sub_nonneg.mpr (monotone_sourceHillLabels r hr q (by omega))
      have hupper := (sourceHillLabels_spec_at r hr q N hN hs).central_below (2*k.natAbs) (by omega)
      have hlower := sourceHillSpectrum_re_lower_bound_on_ball r hr R q.val hq
        (sourceHillLabels r hr q (2*k.natAbs-1)) ((sourceHillLabels_spec r hr q).spectral _)
      have hW : Weight.sobolev (-r) k ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (le_add_of_nonneg_right (abs_nonneg _)) (neg_nonpos.mpr hr.1)
      rw [sourceCanonicalGapValues,if_neg hk0,norm_mul,Complex.norm_real,Real.norm_eq_abs,
        abs_of_pos ((Weight.sobolev (-r)).positive k),Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hgap]
      have he := mul_le_of_le_one_left hgap hW
      simp only [Complex.ofReal_re] at hlower
      unfold sourceCanonicalGapBound
      nlinarith

/-- Membership uses the ACTUAL canonical gaps, with no change of exponent or truncation. -/
theorem sourceCanonicalGapValues_mem (r : ℝ) (hr : AdmissiblePredualOrder r) (q : Potential r) :
    Memℓp (fun k => (Weight.sobolev (-r) k:ℂ)*sourceCanonicalGapValues r hr q k) ⊤ := by
  obtain ⟨hN,hs⟩ := sourceHillLabelCutoff_spec r hr q
  apply memℓp_infty
  refine ⟨sourceCanonicalGapBound r hr ‖q.val‖ (sourceHillLabelCutoff r hr q),?_⟩
  rintro _ ⟨k,rfl⟩
  exact norm_sourceCanonicalGapValues_le r hr q ‖q.val‖ le_rfl _ hN hs k

/-- The entire canonical gap sequence in the original source infinity Sobolev scale. -/
def sourceCanonicalGaps (r : ℝ) (hr : AdmissiblePredualOrder r) (q : Potential r) :
    WeightedCoeff (Weight.sobolev (-r)) ⊤ :=
  ⟨sourceCanonicalGapValues r hr q,sourceCanonicalGapValues_mem r hr q⟩

@[simp] theorem sourceCanonicalGaps_apply (r : ℝ) (hr : AdmissiblePredualOrder r) (q : Potential r) (k : ℤ) :
    (sourceCanonicalGaps r hr q).val k = sourceCanonicalGapValues r hr q k := rfl

/-- Explicit all-mode norm bound for any admissible original norm-ball cutoff. -/
theorem norm_sourceCanonicalGaps_le (r : ℝ) (hr : AdmissiblePredualOrder r) (q : Potential r)
    (R : ℝ) (hq : ‖q.val‖ ≤ R) (N : ℕ) (hN : 2 ≤ N)
    (hs : ∀ n : ℕ, N ≤ n → 13*endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q.val‖ ≤ 1/2) :
    ‖sourceCanonicalGaps r hr q‖ ≤ sourceCanonicalGapBound r hr R N := by
  have hR : 0 ≤ R := (norm_nonneg q.val).trans hq
  have hB := sourceSpectralBound_nonneg r hr R
  have hfree : 0 ≤ freeHillValue N := by unfold freeHillValue; positivity
  change ‖WeightedCoeff.weightEquiv (Weight.sobolev (-r)) ⊤ _‖ ≤ _
  apply lp.norm_le_of_forall_le (by unfold sourceCanonicalGapBound; positivity)
  intro k
  exact norm_sourceCanonicalGapValues_le r hr q R hq N hN hs k

/-- The canonical gap map is bounded on EVERY original endpoint potential norm ball. -/
theorem source_uniform_canonical_gap_bound (r : ℝ) (hr : AdmissiblePredualOrder r) (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q : Potential r, ‖q.val‖ ≤ R → ‖sourceCanonicalGaps r hr q‖ ≤ C := by
  obtain ⟨N,hN,hcut⟩ := exists_wideEndpointHill_cutoff r hr.2 R
  refine ⟨|sourceCanonicalGapBound r hr R N|,abs_nonneg _,fun q hq => ?_⟩
  apply (norm_sourceCanonicalGaps_le r hr q R hq N hN ?_).trans (le_abs_self _)
  intro n hn
  exact (mul_le_mul_of_nonneg_left hq (mul_nonneg
    (mul_nonneg (by norm_num) (endpointHillConstant_pos r hr.2).le)
    (Real.rpow_nonneg (by positivity) _))).trans (hcut n hn)

end NLS.Articles.KdVPseudomeasures
