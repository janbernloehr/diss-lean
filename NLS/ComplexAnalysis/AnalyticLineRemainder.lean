import NLS.ComplexAnalysis.AnalyticLineDerivativeBounds
import Mathlib.Analysis.Complex.Schwarz

/-! # A uniform quadratic remainder for analytic line restrictions

The Schwarz estimate applied after subtracting the constant and linear
terms bounds the remainder uniformly over all sequence directions.
-/
noncomputable section
open Set Metric Filter Topology Asymptotics
namespace NLS.ComplexAnalysis
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- Local boundedness and analytic lines give a quadratic error bound,
without assuming Fréchet differentiability. -/
theorem norm_sub_lineDeriv_le_of_ball_bound
    (f : E → F) (U : Set E) (hU : IsOpen U)
    (hl : ∀ a ∈ U, ∀ v : E, AnalyticOnNhd ℂ (fun t : ℂ => f (a+t • v))
      ((fun t : ℂ => a+t • v) ⁻¹' U))
    (a : E) (R M : ℝ) (hR : 0 < R) (hball : ball a R ⊆ U)
    (hb : ∀ x ∈ ball a R, ‖f x‖ ≤ M) (h : E) (hh : ‖h‖ < R/2) :
    ‖f (a+h)-f a-lineDeriv ℂ f a h‖ ≤ (12*M/R^2)*‖h‖^2 := by
  by_cases hz : h = 0
  · simp [hz,lineDeriv_zero]
  have hn : 0 < ‖h‖ := norm_pos_iff.mpr hz
  have ha : a ∈ U := hball (mem_ball_self hR)
  have hM : 0 ≤ M := (norm_nonneg _).trans (hb a (mem_ball_self hR))
  let r : ℝ := R/(2*‖h‖)
  have hr : 0 < r := by dsimp [r]; positivity
  have hr1 : 1 < r := by dsimp [r]; rw [lt_div_iff₀ (by positivity)]; linarith
  have hrmul : r*‖h‖ = R/2 := by dsimp [r]; field_simp
  have hinto (t : ℂ) (ht : t ∈ ball 0 r) : a+t • h ∈ ball a R := by
    rw [mem_ball,dist_eq_norm,add_sub_cancel_left,norm_smul]
    have ht' : ‖t‖ < r := by simpa only [mem_ball,dist_zero_right] using ht
    calc
      ‖t‖*‖h‖ ≤ r*‖h‖ := mul_le_mul_of_nonneg_right ht'.le (norm_nonneg _)
      _ = R/2 := hrmul
      _ < R := by linarith
  let D := lineDeriv ℂ f a h
  let g : ℂ → F := fun t => f (a+t • h)-f a-t • D
  have hg0 : g 0 = 0 := by simp [g]
  have hd : ‖D‖ ≤ (2*M/R)*‖h‖ :=
    norm_lineDeriv_le_of_ball_bound f U hU hl a R M hR hball hb h
  have hg : DifferentiableOn ℂ g (ball 0 r) := by
    have hf := (hl a ha h).differentiableOn.mono (fun t ht => hball (hinto t ht))
    exact (hf.sub_const (f a)).sub (differentiable_id.smul_const D).differentiableOn
  have hmaps : MapsTo g (ball 0 r) (closedBall (g 0) (3*M)) := by
    intro t ht
    rw [mem_closedBall,hg0,dist_zero_right]
    have ht' : ‖t‖ ≤ r := (by simpa only [mem_ball,dist_zero_right] using ht : ‖t‖ < r).le
    have hs : ‖t • D‖ ≤ M := by
      rw [norm_smul]
      calc
        ‖t‖*‖D‖ ≤ r*((2*M/R)*‖h‖) := mul_le_mul ht' hd (norm_nonneg _) hr.le
        _ = M := by dsimp [r]; field_simp
    calc
      ‖g t‖ ≤ ‖f (a+t • h)‖+‖f a‖+‖t • D‖ := (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
      _ ≤ M+M+M := add_le_add (add_le_add (hb _ (hinto t ht)) (hb a (mem_ball_self hR))) hs
      _ = 3*M := by ring
  have hd0 : HasDerivAt g 0 0 := by
    have hf : HasDerivAt (fun t : ℂ => f (a+t • h)) D 0 :=
      hasLineDerivAt_of_analyticLines f U hl a ha h
    simpa only [g,Pi.sub_def,id_eq,sub_self,one_smul] using
      (hf.sub_const (f a)).sub ((hasDerivAt_id (0 : ℂ)).smul_const D)
  have ho : (fun t => g t-g 0) =o[𝓝 (0 : ℂ)] (fun t => ‖t-0‖^1) := by
    simpa only [smul_zero,sub_zero,pow_one] using hd0.isLittleO.norm_right
  have h1 : (1 : ℂ) ∈ ball 0 r := by simpa only [mem_ball,dist_zero_right,norm_one] using hr1
  have hs := Complex.dist_le_mul_div_pow_of_mapsTo_ball_of_isLittleO hg hmaps ho h1
  have he : 3*M*(1/r)^2 = (12*M/R^2)*‖h‖^2 := by dsimp [r]; field_simp; ring
  simpa only [hg0,dist_zero_right,g,one_smul,norm_one,he] using hs

end NLS.ComplexAnalysis
