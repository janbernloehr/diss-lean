import NLS.ComplexAnalysis.BanachTaylorBounds

/-!
# Local bounds for Banach-space Taylor coefficients

The Schwarz estimate only needs complex smoothness on the ball where the
function is bounded. This local version is suited to the moving-gap domain.
-/

noncomputable section
open Filter Topology Metric
open scoped ENNReal NNReal ContDiff
namespace NLS.ComplexAnalysis
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Nested balls bound the iterated derivative using smoothness only on the outer ball. -/
theorem norm_iteratedFDeriv_le_of_ball_bound_on (f : E → F)
    (c : E) (n : ℕ) (R d M : ℝ) (hd : 0 < d)
    (hf : ContDiffOn ℂ ∞ f (ball c (R+n*d)))
    (hb : ∀ y ∈ ball c (R+n*d), ‖f y‖ ≤ M) :
    ∀ x ∈ ball c R, ‖iteratedFDeriv ℂ n f x‖ ≤ (2/d)^n*M := by
  induction n generalizing R with
  | zero => simpa using hb
  | succ n ih =>
    have heq : (R+d)+(n : ℝ)*d = R+(↑(n+1) : ℝ)*d := by push_cast; ring
    have hf' : ContDiffOn ℂ ∞ f (ball c ((R+d)+n*d)) := by
      rw [heq]
      exact hf
    have hb' : ∀ y ∈ ball c ((R+d)+n*d), ‖f y‖ ≤ M := by
      rw [heq]
      exact hb
    have hn := ih (R+d) hf' hb'
    intro x hx
    rw [← norm_fderiv_iteratedFDeriv]
    have hdiff : DifferentiableOn ℂ (iteratedFDeriv ℂ n f) (ball c (R+d)) := by
      intro y hy
      have hys : y ∈ ball c (R+↑(n+1)*d) := by
        apply mem_ball.mpr
        have h := mem_ball.mp hy
        have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
        nlinarith
      exact ((hf.contDiffAt (isOpen_ball.mem_nhds hys)).differentiableAt_iteratedFDeriv
        (by exact_mod_cast ENat.natCast_lt_top n)).differentiableWithinAt
    have he := norm_fderiv_le_of_ball_bound (iteratedFDeriv ℂ n f) c x R d
      ((2/d)^n*M) hd hdiff hn hx
    apply he.trans_eq
    rw [pow_succ]
    ring

/-- A bound on a local smoothness ball controls the factorial-normalized coefficients. -/
theorem norm_complexTaylorSeries_le_on (f : E → F) (c : E) (R M : ℝ)
    (hR : 0 < R) (hM : 0 ≤ M) (hf : ContDiffOn ℂ ∞ f (ball c R))
    (hb : ∀ y ∈ ball c R, ‖f y‖ ≤ M) (n : ℕ) :
    ‖complexTaylorSeries f c n‖ ≤ (4*Real.exp 1/R)^n*M := by
  have hfac : 0 < (n.factorial : ℝ) := by positivity
  have hn : ‖complexTaylorSeries f c n‖ = ‖iteratedFDeriv ℂ n f c‖/(n.factorial : ℝ) := by
    simp [complexTaylorSeries, norm_smul, div_eq_mul_inv, mul_comm]
  rw [hn]
  by_cases hzero : n = 0
  · subst n
    simpa using hb c (mem_ball_self hR)
  have hnp : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hzero
  let d := R/(2*n)
  have hd : 0 < d := div_pos hR (by positivity)
  have he : R/2+(n : ℝ)*d = R := by dsimp [d]; field_simp; ring
  have hder := norm_iteratedFDeriv_le_of_ball_bound_on f c n (R/2) d M hd
    (by simpa only [he] using hf) (by simpa only [he] using hb)
    c (mem_ball_self (half_pos hR))
  have he' : 2/d = (4/R)*(n : ℝ) := by dsimp [d]; field_simp; ring
  rw [he'] at hder
  calc
    _ ≤ ((4/R)*(n : ℝ))^n*M/(n.factorial : ℝ) := div_le_div_of_nonneg_right hder hfac.le
    _ = (4/R)^n*((n : ℝ)^n/(n.factorial : ℝ))*M := by rw [mul_pow]; ring
    _ ≤ (4/R)^n*Real.exp (n : ℝ)*M := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Real.pow_div_factorial_le_exp (n : ℝ) hnp.le n)
          (by positivity)) hM
    _ = (4*Real.exp 1/R)^n*M := by
      rw [show (n : ℝ) = (n : ℝ)*1 by ring, Real.exp_nat_mul, ← mul_pow]
      congr 2
      ring

/-- The Fréchet Taylor series has a positive radius at a point of an open smoothness domain. -/
theorem complexTaylorSeries_radius_pos_on (f : E → F) {S : Set E}
    (hS : IsOpen S) (hf : ContDiffOn ℂ ∞ f S) {c : E} (hc : c ∈ S) :
    0 < (complexTaylorSeries f c).radius := by
  have hcont := (hf.continuousOn c hc).continuousAt (hS.mem_nhds hc)
  obtain ⟨R₀,hR₀,hb₀⟩ := Metric.mem_nhds_iff.mp
    (hcont (ball_mem_nhds (f c) (by norm_num : (0 : ℝ) < 1)))
  obtain ⟨R₁,hR₁,hb₁⟩ := Metric.mem_nhds_iff.mp (hS.mem_nhds hc)
  let R := min R₀ R₁
  have hR : 0 < R := lt_min hR₀ hR₁
  have hball : ball c R ⊆ S := (ball_subset_ball (min_le_right _ _)).trans hb₁
  let M := ‖f c‖+1
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hbound : ∀ y ∈ ball c R, ‖f y‖ ≤ M := by
    intro y hy
    have hdist : ‖f y-f c‖ < 1 := by
      simpa only [Set.mem_preimage, mem_ball, dist_eq_norm] using
        hb₀ (ball_subset_ball (min_le_left _ _) hy)
    exact (norm_le_norm_sub_add (f y) (f c)).trans (by dsimp [M]; linarith)
  let r : ℝ≥0 := ⟨R/(4*Real.exp 1),by positivity⟩
  have hr : 0 < r := by change 0 < R/(4*Real.exp 1); positivity
  apply (show (0 : ℝ≥0∞) < r by exact_mod_cast hr).trans_le
  apply (complexTaylorSeries f c).le_radius_of_bound M
  intro n
  calc
    _ ≤ ((4*Real.exp 1/R)^n*M)*(r : ℝ)^n :=
      mul_le_mul_of_nonneg_right
        (norm_complexTaylorSeries_le_on f c R M hR hM (hf.mono hball) hbound n)
        (by positivity)
    _ = M := by
      have he : (4*Real.exp 1/R)*(r : ℝ) = 1 := by
        change (4*Real.exp 1/R)*(R/(4*Real.exp 1)) = 1
        field_simp
      calc
        _ = ((4*Real.exp 1/R)*(r : ℝ))^n*M := by rw [mul_pow]; ring
        _ = M := by rw [he, one_pow, one_mul]

end NLS.ComplexAnalysis
