import NLS.Articles.KdVPseudomeasures.SpectralDiagonalRoot

/-! Actual adapted Fourier coefficients b_±n(alpha_n(q),q),without an assumed root or map. -/
noncomputable section
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
open NLS.Fourier NLS.Fourier.SmoothPeriodicTest NLS.Fourier.PeriodicFourierLebesgue NLS.KdV

/-- The actual two physical couplings evaluated at the proved intrinsic diagonal root. -/
def sourceAdaptedCouplings (w : SpectralWeight) (r : ℝ) (hr : AdmissiblePredualOrder r)
    (n : ℕ) (hn : 1 ≤ n) (q : PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev r) ⊤) : ℂ × ℂ :=
  (sourceEndpointEntries r hr n (sourceForgetWeight w r q,sourceWeightedDiagonalRoot w r hr n hn q)).2

/-- Every actual adapted Fourier coefficient is analytic in the exact original weighted norm. -/
theorem analyticAt_sourceAdaptedCouplings (w : SpectralWeight) (r : ℝ) (hr : AdmissiblePredualOrder r)
    (n : ℕ) (hn : 1 ≤ n) (q : PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev r) ⊤)
    (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ < 1/2) :
    AnalyticAt ℂ (sourceAdaptedCouplings w r hr n hn) q := by
  have hsmall : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖sourceForgetWeight w r q‖ ≤ 1/2 :=
    (mul_le_mul_of_nonneg_left (norm_sourceForgetWeight_le w r q)
      (by positivity [endpointHillConstant_pos r hr.2])).trans hs.le
  have hstrip := (sourceDiagonalRoot_spec r hr n hn (sourceForgetWeight w r q) hsmall).1
  have hA := analyticAt_sourceWeightedEndpointEntries w r hr n hn q
    (sourceWeightedDiagonalRoot w r hr n hn q) hstrip hs.le
  have hroot := analyticAt_sourceWeightedDiagonalRoot w r hr n hn q hs
  have he := hA.comp (f := fun p => (p,sourceWeightedDiagonalRoot w r hr n hn p)) (analyticAt_id.prod hroot)
  exact (analyticAt_snd (𝕜 := ℂ) (p := sourceEndpointEntries r hr n
    (sourceForgetWeight w r q,sourceWeightedDiagonalRoot w r hr n hn q))).comp
      (f := fun p : PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev r) ⊤ =>
        sourceEndpointEntries r hr n (sourceForgetWeight w r p,sourceWeightedDiagonalRoot w r hr n hn p))
      (x := q) he

/-- The full source-weight errors hold at the ACTUAL analytic diagonal root. -/
theorem sourceAdaptedCouplings_weighted_errors (w : SpectralWeight) (r : ℝ) (hr : AdmissiblePredualOrder r)
    (n : ℕ) (hn : 1 ≤ n) (q : PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev r) ⊤)
    (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2) :
    w.negativeSobolev r (2*(n:ℤ))*‖(sourceAdaptedCouplings w r hr n hn q).1-q.val (mode (-(2*(n:ℤ))))‖ ≤
        2*(endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖)*‖q‖ ∧
      w.negativeSobolev r (2*(n:ℤ))*‖(sourceAdaptedCouplings w r hr n hn q).2-q.val (mode (2*(n:ℤ)))‖ ≤
        2*(endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖)*‖q‖ := by
  have hsmall : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖sourceForgetWeight w r q‖ ≤ 1/2 :=
    (mul_le_mul_of_nonneg_left (norm_sourceForgetWeight_le w r q)
      (by positivity [endpointHillConstant_pos r hr.2])).trans hs
  have hstrip := (sourceDiagonalRoot_spec r hr n hn (sourceForgetWeight w r q) hsmall).1
  exact (sourceLemma2_9_weighted_errors w r hr n hn q _ hstrip hs).2

/-- At the actual diagonal root,the original physical determinant is minus the
product of the two adapted coefficients. This root need not be an eigenvalue. -/
theorem sourceEndpointDeterminant_at_diagonalRoot (w : SpectralWeight) (r : ℝ) (hr : AdmissiblePredualOrder r)
    (n : ℕ) (hn : 1 ≤ n) (q : PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev r) ⊤)
    (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2) :
    sourceEndpointDeterminant r hr n (sourceForgetWeight w r q,sourceWeightedDiagonalRoot w r hr n hn q) =
      -((sourceAdaptedCouplings w r hr n hn q).1*(sourceAdaptedCouplings w r hr n hn q).2) := by
  have hsmall : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖sourceForgetWeight w r q‖ ≤ 1/2 :=
    (mul_le_mul_of_nonneg_left (norm_sourceForgetWeight_le w r q)
      (by positivity [endpointHillConstant_pos r hr.2])).trans hs
  obtain ⟨hstrip, hroot, _⟩ := sourceDiagonalRoot_spec r hr n hn (sourceForgetWeight w r q) hsmall
  have hf := sourceEndpointDeterminant_factorization r hr n hn (sourceForgetWeight w r q)
    (sourceWeightedDiagonalRoot w r hr n hn q) hstrip hsmall
  change sourceWeightedDiagonalRoot w r hr n hn q-(freeHillValue n:ℂ)-
    (sourceEndpointEntries r hr n (sourceForgetWeight w r q,sourceWeightedDiagonalRoot w r hr n hn q)).1 = 0 at hroot
  rw [hroot] at hf
  simpa only [sourceAdaptedCouplings, zero_pow (by decide : (2:ℕ) ≠ 0), zero_sub] using hf

/-- One cutoff BEFORE BOTH weight and potential gives actual analytic adapted
coefficients and shrinking original weighted errors on the ENTIRE norm ball. -/
theorem source_uniform_adapted_coupling_errors (r : ℝ) (hr : AdmissiblePredualOrder r) (R : ℝ) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ (n : ℕ) (hn : 1 ≤ n), N ≤ n → ∀ w : SpectralWeight,
      ∀ q : PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev r) ⊤, ‖q‖ ≤ R →
        AnalyticAt ℂ (sourceAdaptedCouplings w r hr n hn) q ∧
        w.negativeSobolev r (2*(n:ℤ))*‖(sourceAdaptedCouplings w r hr n hn q).1-q.val (mode (-(2*(n:ℤ))))‖ ≤
          2*endpointHillConstant r*(n:ℝ)^(r-1/2)*R^2 ∧
        w.negativeSobolev r (2*(n:ℤ))*‖(sourceAdaptedCouplings w r hr n hn q).2-q.val (mode (2*(n:ℤ)))‖ ≤
          2*endpointHillConstant r*(n:ℝ)^(r-1/2)*R^2 := by
  obtain ⟨N, hN, hcut⟩ := exists_endpointHill_cutoff r hr.2 (8*R)
  refine ⟨N, hN, fun n hn hnN w q hq => ?_⟩
  let c := endpointHillConstant r*(n:ℝ)^(r-1/2)
  have hc : 0 ≤ c := by dsimp [c]; positivity [endpointHillConstant_pos r hr.2]
  have hsmall : c*‖q‖ < 1/2 := by
    have hh := hcut n hnN
    change c*(8*R) ≤ 1/2 at hh
    have hi := mul_le_mul_of_nonneg_left hq hc
    linarith
  obtain ⟨hb, hd⟩ := sourceAdaptedCouplings_weighted_errors w r hr n hn q hsmall.le
  have hscale : 2*(c*‖q‖)*‖q‖ ≤ 2*endpointHillConstant r*(n:ℝ)^(r-1/2)*R^2 := by
    have hh := mul_le_mul_of_nonneg_left (mul_self_le_mul_self (norm_nonneg q) hq)
      (show 0 ≤ 2*c by positivity)
    nlinarith
  exact ⟨analyticAt_sourceAdaptedCouplings w r hr n hn q hsmall, hb.trans hscale, hd.trans hscale⟩

end NLS.Articles.KdVPseudomeasures
