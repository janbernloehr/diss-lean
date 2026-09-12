import NLS.SequenceSpaces.YoungTrilinear

/-!
# Young's norm estimate for finitely supported inputs

The convolution is the existing Banach-space convolution, reinterpreted at the
chosen target exponent. Finite conjugate tests and the trilinear estimate give
the exact norm bound, uniformly in both input supports.
-/

noncomputable section
open scoped ENNReal
namespace NLS.Coeff

/-- Finite coefficients decompose into their single-frequency vectors at every exponent. -/
theorem ofFinsupp_eq_sum_single {p : ℝ≥0∞} (a : ℤ →₀ ℂ) :
    ofFinsupp (p := p) a = ∑ n ∈ a.support, lp.single p n (a n) := by
  change ofFinsupp a = truncate a.support (ofFinsupp a)
  ext n
  by_cases hn : n ∈ a.support
  · simp [truncate_apply, hn]
  · simp [truncate_apply, hn, Finsupp.notMem_support_iff.mp hn]

/-- Translating a single coefficient adds to its frequency. -/
theorem shift_single {p : ℝ≥0∞} [Fact (1 ≤ p)] (k j : ℤ) (z : ℂ) :
    shift k (lp.single p j z) = lp.single p (j + k) z := by
  ext n
  simp only [shift_apply, lp.single_apply, Pi.single_apply]
  by_cases hn : n = j + k
  · subst n; simp
  · have h₂ : n - k ≠ j := by omega
    simp [hn, h₂]

/-- Convolution of two finite inputs in a prescribed Banach target exponent. -/
def finiteConvolution (r : ℝ≥0∞) [Fact (1 ≤ r)] (a b : ℤ →₀ ℂ) : Coeff r :=
  convolution (ofFinsupp a) (ofFinsupp b)

/-- The output is the finite sum of all input frequency sums. -/
theorem finiteConvolution_eq_sum {r : ℝ≥0∞} [Fact (1 ≤ r)] (a b : ℤ →₀ ℂ) :
    finiteConvolution r a b =
      ∑ j ∈ a.support, ∑ k ∈ b.support, lp.single r (j + k) (a j * b k) := by
  unfold finiteConvolution
  rw [ofFinsupp_eq_sum_single (p := r) a, ofFinsupp_eq_sum_single (p := 1) b]
  change convolutionCLM (∑ j ∈ a.support, lp.single r j (a j))
    (∑ k ∈ b.support, lp.single 1 k (b k)) = _
  simp only [map_sum, sum_apply, convolutionCLM_apply,
    convolution_single_right, shift_single]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ext n
  simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, lp.single_apply, Pi.single_apply]
  split_ifs <;> simp [mul_comm]

/-- A single coefficient is evaluated by the corresponding dual coordinate. -/
theorem dualPairing_single_left {r t : ℝ≥0∞} [Fact (1 ≤ r)] [Fact (1 ≤ t)]
    [r.HolderConjugate t] (n : ℤ) (z : ℂ) (c : Coeff t) :
    dualPairing (lp.single r n z) c = z * c n := by
  simp [dualPairing_apply, lp.single_apply, Pi.single_apply]

/-- Testing the finite convolution gives exactly the finite trilinear kernel. -/
theorem finiteConvolution_pairing {r t : ℝ≥0∞} [Fact (1 ≤ r)] [Fact (1 ≤ t)]
    [r.HolderConjugate t] (a b c : ℤ →₀ ℂ) :
    c.sum (fun n z => finiteConvolution r a b n * z) =
      ∑ j ∈ a.support, ∑ k ∈ b.support, a j * b k * c (j + k) := by
  rw [← dualPairing_finite_right (q := t), finiteConvolution_eq_sum]
  simp only [map_sum, sum_apply, dualPairing_single_left, ofFinsupp_apply]

/-- Exact Young bound for finite inputs, with the finite dual exponent left explicit. -/
theorem norm_finiteConvolution_le {p q r t : ℝ≥0∞}
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ r)] [Fact (1 ≤ t)] [r.HolderConjugate t]
    (hp : 1 ≤ p.toReal) (hq : 1 ≤ q.toReal) (hr : 0 < r.toReal) (ht : 1 ≤ t.toReal)
    (h : 1 / p.toReal + 1 / q.toReal + 1 / t.toReal = 2) (a b : ℤ →₀ ℂ) :
    ‖finiteConvolution r a b‖ ≤ ‖ofFinsupp (p := p) a‖ * ‖ofFinsupp (p := q) b‖ := by
  apply norm_le_of_finite_dual_unit hr (zero_lt_one.trans_le ht)
    (ENNReal.toReal_pos_iff_ne_top r |>.mp hr)
  intro c hc
  rw [finiteConvolution_pairing (t := t)]
  have hb := norm_young_trilinear_le hp hq ht h
    (ofFinsupp (p := p) a) (ofFinsupp (p := q) b) (ofFinsupp (p := t) c) a.support b.support
  exact hb.trans (by simpa only [mul_one] using (mul_le_mul_of_nonneg_left hc
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))))

/-- Finite convolution is independent of the exponent used to represent its output. -/
theorem finiteConvolution_apply {r : ℝ≥0∞} [Fact (1 ≤ r)] (a b : ℤ →₀ ℂ) (n : ℤ) :
    finiteConvolution r a b n = ∑' k : ℤ, a (n - k) * b k := convolution_apply _ _ n

end NLS.Coeff
