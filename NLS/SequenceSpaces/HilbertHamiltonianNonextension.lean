import NLS.SequenceSpaces.PositiveFlatBlocks
import NLS.SequenceSpaces.HilbertHamiltonianValueBound

/-! # No continuous larger-exponent extension of a quadratically negative action Hamiltonian -/
noncomputable section
open Set Metric Filter Topology Complex
open scoped ENNReal
namespace NLS.Coeff

/-- Nonnegative real scaling preserves the action cone. -/
theorem nonnegative_real_smul_mem {p : ℝ≥0∞} (a : Coeff p) (ha : a ∈ nonnegativeLocus p)
    (c : ℝ) (hc : 0 ≤ c) : (c:ℂ) • a ∈ nonnegativeLocus p := by
  intro n
  change (((c:ℂ)*a n).im = 0) ∧ 0 ≤ ((c:ℂ)*a n).re
  simp only [Complex.mul_im,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    (ha n).1,mul_zero,zero_mul,add_zero,sub_zero]
  exact ⟨trivial,mul_nonneg hc (ha n).2⟩

/-- A quadratic drop in the Hilbert norm prevents continuity even relative to the positive cone
in any finite exponent above two. Agreement is needed only on summable nonnegative actions
in arbitrarily small neighborhoods of zero. -/
theorem not_continuousWithinAt_extension_of_quadratic_bound
    {q : ℝ≥0∞} [Fact (1 ≤ q)] (hq : q ≠ ⊤) (h2q : 2 < q)
    (H : Coeff 2 → ℂ) (hzero : H 0 = 0) (r : ℝ) (hr : 0 < r)
    (hbound : ∀ b ∈ nonnegativeLocus 2, ‖b‖ < r → (H b).re ≤ -‖b‖^2/2)
    (G : Coeff q → ℂ) (U : Set (Coeff q)) (hU : U ∈ 𝓝 (0:Coeff q))
    (hagree : ∀ a : Coeff 1, a ∈ nonnegativeLocus 1 →
      exponentInclusion (by exact le_trans (by norm_num : (1:ℝ≥0∞) ≤ 2) h2q.le) a ∈ U →
      ‖exponentInclusion (by norm_num : (1:ℝ≥0∞) ≤ 2) a‖ < r →
      G (exponentInclusion (by exact le_trans (by norm_num : (1:ℝ≥0∞) ≤ 2) h2q.le) a) =
        H (exponentInclusion (by norm_num : (1:ℝ≥0∞) ≤ 2) a)) :
    ¬ ContinuousWithinAt G (nonnegativeLocus q) 0 := by
  intro hG
  let c := r/2
  have hc : 0 < c := by dsimp [c]; positivity
  have hcr : c < r := by dsimp [c]; linarith
  let b := fun (p : ℝ≥0∞) (N : ℕ) => (c:ℂ) • positiveFlatBlock p N
  have hpos (p : ℝ≥0∞) (N : ℕ) : b p N ∈ nonnegativeLocus p :=
    nonnegative_real_smul_mem _ (positiveFlatBlock_mem_nonnegativeLocus p N) c hc.le
  have he {p s : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ s)] (hps : p ≤ s) (N : ℕ) :
      exponentInclusion hps (b p N) = b s N := by simp only [b,map_smul,positiveFlatBlock_exponent]
  have hn (N : ℕ) : ‖b 2 N‖ = c := by
    simp only [b,norm_smul,norm_positiveFlatBlock_two,mul_one,Complex.norm_of_nonneg hc.le]
  have ht : Tendsto (b q) atTop (𝓝 0) := by
    simpa only [b,smul_zero] using (tendsto_positiveFlatBlock hq h2q).const_smul (c:ℂ)
  have hwithin : Tendsto (b q) atTop (𝓝[nonnegativeLocus q] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨ht,Filter.Eventually.of_forall (hpos q)⟩
  have hGzero : G 0 = 0 := by
    have h := hagree 0 (zero_mem_nonnegativeLocus 1) (by simpa using mem_of_mem_nhds hU)
      (by simpa using hr)
    simpa only [map_zero,hzero] using h
  have hlim : Tendsto (fun N => (G (b q N)).re) atTop (𝓝 0) := by
    simpa only [hGzero,Complex.zero_re,Function.comp_def] using! Complex.continuous_re.continuousAt.tendsto.comp (hG.tendsto.comp hwithin)
  have hle : ∀ᶠ N in atTop, (G (b q N)).re ≤ -c^2/2 := by
    filter_upwards [ht.eventually hU] with N hNU
    have h := hagree (b 1 N) (hpos 1 N) (by simpa only [he] using! hNU)
      (by simpa only [he,hn] using hcr)
    rw [he,he] at h
    rw [h]
    simpa only [hn] using hbound (b 2 N) (hpos 2 N) (by rw [hn]; exact hcr)
  have hh := le_of_tendsto hlim hle
  nlinarith [sq_pos_of_pos hc]

end NLS.Coeff
