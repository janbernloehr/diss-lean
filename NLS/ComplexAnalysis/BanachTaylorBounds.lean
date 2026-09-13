import NLS.ComplexAnalysis.BanachHolomorphicLimit
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Complex.Exponential

/-!
# Bounds for Banach-space complex Taylor coefficients

Schwarz estimates on equally spaced nested balls control iterated Fréchet
derivatives. Dividing by factorials gives geometric coefficient bounds and
a positive convergence radius for the formal Taylor series.
-/

noncomputable section
open Filter Topology Metric
open scoped ENNReal NNReal ContDiff
namespace NLS.ComplexAnalysis
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- A uniform bound on a larger ball bounds the Fréchet derivative on a ball with fixed margin. -/
theorem norm_fderiv_le_of_ball_bound (f : E → F) (c x : E) (R d M : ℝ) (hd : 0 < d)
    (hf : DifferentiableOn ℂ f (ball c (R+d)))
    (hb : ∀ y ∈ ball c (R+d), ‖f y‖ ≤ M) (hx : x ∈ ball c R) :
    ‖fderiv ℂ f x‖ ≤ 2*M/d := by
  have hsub : ball x d ⊆ ball c (R+d) := by
    intro y hy
    have ht := dist_triangle y x c
    rw [mem_ball] at hy hx ⊢
    linarith
  apply Complex.norm_fderiv_le_div_of_mapsTo_ball (hf.mono hsub) _ hd
  intro y hy
  rw [mem_closedBall, dist_eq_norm]
  exact (norm_sub_le _ _).trans (by
    simpa only [two_mul] using add_le_add (hb y (hsub hy)) (hb x (hsub (mem_ball_self hd))))

/-- Equally spaced nested balls give exponential-in-order derivative bounds before choosing the spacing. -/
theorem norm_iteratedFDeriv_le_of_ball_bound (f : E → F) (hf : ContDiff ℂ ∞ f)
    (c : E) (n : ℕ) (R d M : ℝ) (hd : 0 < d)
    (hb : ∀ y ∈ ball c (R+n*d), ‖f y‖ ≤ M) :
    ∀ x ∈ ball c R, ‖iteratedFDeriv ℂ n f x‖ ≤ (2/d)^n*M := by
  induction n generalizing R with
  | zero => simpa using hb
  | succ n ih =>
    have hb' : ∀ y ∈ ball c ((R+d)+n*d), ‖f y‖ ≤ M := by
      rw [show (R+d)+(n : ℝ)*d = R+(↑(n+1) : ℝ)*d by push_cast; ring]
      exact hb
    have hn := ih (R+d) hb'
    intro x hx
    rw [← norm_fderiv_iteratedFDeriv]
    have he := norm_fderiv_le_of_ball_bound (iteratedFDeriv ℂ n f) c x R d ((2/d)^n*M) hd
      (hf.differentiable_iteratedFDeriv (by exact_mod_cast ENat.natCast_lt_top n)).differentiableOn hn hx
    apply he.trans_eq
    rw [pow_succ]
    ring

/-- The factorial-normalized coefficients of the complex Fréchet Taylor expansion. -/
def complexTaylorSeries (f : E → F) (c : E) : FormalMultilinearSeries ℂ E F :=
  fun n => ((n.factorial : ℂ)⁻¹) • iteratedFDeriv ℂ n f c

/-- A local bound gives a geometric bound for every factorial-normalized coefficient. -/
theorem norm_complexTaylorSeries_le (f : E → F) (hf : ContDiff ℂ ∞ f)
    (c : E) (R M : ℝ) (hR : 0 < R) (hM : 0 ≤ M)
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
  have hder := norm_iteratedFDeriv_le_of_ball_bound f hf c n (R/2) d M hd
    (by simpa only [he] using hb) c (mem_ball_self (half_pos hR))
  have he' : 2/d = (4/R)*(n : ℝ) := by dsimp [d]; field_simp; ring
  rw [he'] at hder
  calc
    _ ≤ ((4/R)*(n : ℝ))^n*M/(n.factorial : ℝ) := div_le_div_of_nonneg_right hder hfac.le
    _ = (4/R)^n*((n : ℝ)^n/(n.factorial : ℝ))*M := by rw [mul_pow]; ring
    _ ≤ (4/R)^n*Real.exp (n : ℝ)*M := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Real.pow_div_factorial_le_exp (n : ℝ) hnp.le n) (by positivity)) hM
    _ = (4*Real.exp 1/R)^n*M := by
      rw [show (n : ℝ) = (n : ℝ)*1 by ring, Real.exp_nat_mul, ← mul_pow]
      congr 2
      ring

/-- The formal Taylor series has a positive radius at every point of a globally complex smooth map. -/
theorem complexTaylorSeries_radius_pos (f : E → F) (hf : ContDiff ℂ ∞ f) (c : E) :
    0 < (complexTaylorSeries f c).radius := by
  have hcont := hf.continuous.continuousAt (x := c)
  obtain ⟨R,hR,hb⟩ := Metric.mem_nhds_iff.mp (hcont (ball_mem_nhds (f c) (by norm_num : (0 : ℝ) < 1)))
  let M := ‖f c‖+1
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hbound : ∀ y ∈ ball c R, ‖f y‖ ≤ M := by
    intro y hy
    have hdist : ‖f y-f c‖ < 1 := by simpa only [Set.mem_preimage, mem_ball, dist_eq_norm] using hb hy
    exact (norm_le_norm_sub_add (f y) (f c)).trans (by dsimp [M]; linarith)
  let r : ℝ≥0 := ⟨R/(4*Real.exp 1),by positivity⟩
  have hr : 0 < r := by change 0 < R/(4*Real.exp 1); positivity
  apply (show (0 : ℝ≥0∞) < r by exact_mod_cast hr).trans_le
  apply (complexTaylorSeries f c).le_radius_of_bound M
  intro n
  calc
    _ ≤ ((4*Real.exp 1/R)^n*M)*(r : ℝ)^n :=
      mul_le_mul_of_nonneg_right (norm_complexTaylorSeries_le f hf c R M hR hM hbound n) (by positivity)
    _ = M := by
      have he : (4*Real.exp 1/R)*(r : ℝ) = 1 := by
        change (4*Real.exp 1/R)*(R/(4*Real.exp 1)) = 1
        field_simp
      calc
        _ = ((4*Real.exp 1/R)*(r : ℝ))^n*M := by rw [mul_pow]; ring
        _ = M := by rw [he, one_pow, one_mul]

end NLS.ComplexAnalysis
