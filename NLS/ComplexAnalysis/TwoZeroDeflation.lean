import NLS.ComplexAnalysis.CauchyFiniteHoles
import NLS.ComplexAnalysis.TwoRootQuotientDiscBound
import Mathlib.Analysis.Analytic.Order

/-! # Analytic deflation by two zeros, including a double zero

Two filled divided differences construct an actual analytic quotient.
Maximum modulus then bounds it on the full disc from the original
function's boundary bound. The endpoints need not be distinct.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
namespace NLS.ComplexAnalysis

def twoZeroQuotient (f : ℂ → ℂ) (a b : ℂ) : ℂ → ℂ := dslope (dslope f a) b

theorem dslope_zero_at_second_zero (f : ℂ → ℂ) (a b : ℂ)
    (ha : f a = 0) (hb : f b = 0) (hab : a = b → deriv f a = 0) : dslope f a b = 0 := by
  by_cases he : b = a
  · subst b
    simpa only [dslope_same] using hab rfl
  · rw [dslope_of_ne f he,slope_def_field,ha,hb,sub_self,zero_div]

theorem twoZeroQuotient_factor (f : ℂ → ℂ) (a b : ℂ)
    (ha : f a = 0) (hb : f b = 0) (hab : a = b → deriv f a = 0) (z : ℂ) :
    f z = (z-a)*(z-b)*twoZeroQuotient f a b z := by
  have h1 := sub_smul_dslope f a z
  have h2 := sub_smul_dslope (dslope f a) b z
  rw [dslope_zero_at_second_zero f a b ha hb hab] at h2
  simp only [smul_eq_mul,ha,sub_zero] at h1 h2
  change (z-b)*twoZeroQuotient f a b z = dslope f a z at h2
  rw [← h1,← h2]
  ring

theorem analyticOnNhd_twoZeroQuotient (f : ℂ → ℂ) (U : Set ℂ) (a b : ℂ)
    (hf : AnalyticOnNhd ℂ f U) (ha : a ∈ U) (hb : b ∈ U) :
    AnalyticOnNhd ℂ (twoZeroQuotient f a b) U :=
  analyticOnNhd_dslope_of_analytic _ U b (analyticOnNhd_dslope_of_analytic f U a hf ha) hb

/-- Exact zero multiplicities make the deflated analytic quotient a unit,
also at the endpoints of a collapsed pair. -/
theorem twoZeroQuotient_ne_zero (f : ℂ → ℂ) (U : Set ℂ) (a b z : ℂ)
    (hf : AnalyticOnNhd ℂ f U) (ha : a ∈ U) (hb : b ∈ U) (hz : z ∈ U)
    (hfa : f a = 0) (hfb : f b = 0) (hab : a = b → deriv f a = 0)
    (hzeros : f z = 0 → z = a ∨ z = b)
    (horder : f z = 0 → analyticOrderNatAt f z = ({a,b} : Multiset ℂ).count z) :
    twoZeroQuotient f a b z ≠ 0 := by
  classical
  let Q := twoZeroQuotient f a b
  let P : ℂ → ℂ := fun w => (w-a)*(w-b)
  have hQ : AnalyticAt ℂ Q z := analyticOnNhd_twoZeroQuotient f U a b hf ha hb z hz
  have hP : AnalyticAt ℂ P z := by dsimp only [P]; fun_prop
  have hPorder : analyticOrderAt P z = (({a,b} : Multiset ℂ).count z : ℕ∞) := by
    rw [show P = (fun w : ℂ => w-a)*(fun w : ℂ => w-b) from rfl,
      analyticOrderAt_mul (by fun_prop) (by fun_prop)]
    by_cases hza : z = a <;> by_cases hzb : z = b <;>
      simp_all [analyticOrderAt_id_sub_const_of_ne]
    norm_num
  intro hzero
  have hfzero : f z = 0 := by rw [twoZeroQuotient_factor f a b hfa hfb hab z,hzero,mul_zero]
  have hcount : ({a,b} : Multiset ℂ).count z ≠ 0 := by
    have hmem : z ∈ ({a,b} : Multiset ℂ) := by simpa using hzeros hfzero
    exact ne_of_gt (Multiset.count_pos.mpr hmem)
  have hfOrder : analyticOrderAt f z = (({a,b} : Multiset ℂ).count z : ℕ∞) :=
    (ENat.toNat_eq_iff hcount).mp (horder hfzero)
  have hfac : f = P*Q := funext (twoZeroQuotient_factor f a b hfa hfb hab)
  have heq : analyticOrderAt P z + analyticOrderAt Q z = analyticOrderAt P z + 0 := by
    rw [← analyticOrderAt_mul hP hQ,← hfac,hPorder,add_zero,hfOrder]
  have hQorder : analyticOrderAt Q z = 0 :=
    ENat.add_right_injective_of_ne_top (by rw [hPorder]; exact ENat.natCast_ne_top _) heq
  exact ((hQ.analyticOrderAt_eq_zero).mp hQorder) hzero

theorem norm_twoZeroQuotient_le (f : ℂ → ℂ) (a b c : ℂ) (R B : ℝ) (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (ha : a ∈ closedBall c (R/2)) (hb : b ∈ closedBall c (R/2))
    (hfa : f a = 0) (hfb : f b = 0) (hab : a = b → deriv f a = 0)
    (hbound : ∀ z ∈ sphere c R, ‖f z‖ ≤ B) :
    ∀ z ∈ closedBall c R, ‖twoZeroQuotient f a b z‖ ≤ 4*B/R^2 := by
  let Q := twoZeroQuotient f a b
  have hQR : AnalyticOnNhd ℂ Q (closedBall c R) :=
    analyticOnNhd_twoZeroQuotient f _ a b hf
      (closedBall_subset_closedBall (by linarith : R/2 ≤ R) ha)
      (closedBall_subset_closedBall (by linarith : R/2 ≤ R) hb)
  have hdc : DiffContOnCl ℂ Q (ball c R) := by
    refine ⟨fun z hz => (hQR z (ball_subset_closedBall hz)).differentiableAt.differentiableWithinAt,?_⟩
    rw [closure_ball c hR.ne']
    exact hQR.continuousOn
  intro z hz
  apply Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hdc
  · intro w hw
    rw [frontier_ball c hR.ne'] at hw
    have hlo := sq_radius_le_four_mul_norm_two_root_factor a b c w R (R/2) hR le_rfl
      (by simpa only [mem_closedBall,dist_eq_norm] using ha)
      (by simpa only [mem_closedBall,dist_eq_norm] using hb)
      (by simpa only [mem_sphere,dist_eq_norm] using hw)
    have hp : R^2/4*‖Q w‖ ≤ B := by
      calc
        _ ≤ ‖(w-a)*(w-b)‖*‖Q w‖ := mul_le_mul_of_nonneg_right hlo (norm_nonneg _)
        _ = ‖f w‖ := by rw [← norm_mul,← twoZeroQuotient_factor f a b hfa hfb hab]
        _ ≤ B := hbound w hw
    apply (le_div_iff₀ (sq_pos_of_pos hR)).mpr
    nlinarith
  · rw [closure_ball c hR.ne']
    exact hz

/-- A local disc version of the two-root model comparison. The quotient
functions need be analytic near the closed disc, rather than entire. -/
theorem norm_two_root_quotient_sub_le_on_disc
    (F F₀ Q Q₀ : ℂ → ℂ) (a b c : ℂ) (r epsilon A B : ℝ)
    (hr : 0 < r) (hepsilon : 0 ≤ epsilon) (hepsilonr : epsilon ≤ r/2) (hB : 0 ≤ B)
    (ha : ‖a-c‖ ≤ epsilon) (hb : ‖b-c‖ ≤ epsilon)
    (hQ : AnalyticOnNhd ℂ Q (closedBall c r)) (hQ₀ : AnalyticOnNhd ℂ Q₀ (closedBall c r))
    (hF : ∀ z, F z = (z-a)*(z-b)*Q z)
    (hF₀ : ∀ z, F₀ z = (z-c)^2*Q₀ z)
    (herror : ∀ z ∈ sphere c r, ‖F z-F₀ z‖ ≤ A)
    (hmodel : ∀ z ∈ sphere c r, ‖Q₀ z‖ ≤ B) :
    ∀ z ∈ closedBall c r, ‖Q z-Q₀ z‖ ≤ 4*(A+B*(2*r*epsilon+epsilon^2))/r^2 := by
  have hdc : DiffContOnCl ℂ (fun z => Q z-Q₀ z) (ball c r) := by
    refine ⟨fun z hz => ((hQ z (ball_subset_closedBall hz)).sub
      (hQ₀ z (ball_subset_closedBall hz))).differentiableAt.differentiableWithinAt,?_⟩
    rw [closure_ball c hr.ne']
    exact hQ.continuousOn.sub hQ₀.continuousOn
  intro z hz
  apply Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hdc
  · intro w hw
    rw [frontier_ball c hr.ne'] at hw
    have hwr : ‖w-c‖ = r := by simpa only [mem_sphere,dist_eq_norm] using hw
    have hlo := sq_radius_le_four_mul_norm_two_root_factor a b c w r epsilon hr hepsilonr ha hb hwr
    have hfactor := norm_two_root_factor_sub_center_sq_le a b c w r epsilon hepsilon ha hb hwr
    have hid : (Q w-Q₀ w)*((w-a)*(w-b)) =
        F w-F₀ w-Q₀ w*((w-a)*(w-b)-(w-c)^2) := by
      rw [hF w,hF₀ w]
      ring
    have hmul : ‖Q w-Q₀ w‖*(r^2/4) ≤ A+B*(2*r*epsilon+epsilon^2) := by
      calc
        _ ≤ ‖Q w-Q₀ w‖*‖(w-a)*(w-b)‖ := mul_le_mul_of_nonneg_left hlo (norm_nonneg _)
        _ = ‖F w-F₀ w-Q₀ w*((w-a)*(w-b)-(w-c)^2)‖ := by rw [← norm_mul,hid]
        _ ≤ ‖F w-F₀ w‖+‖Q₀ w*((w-a)*(w-b)-(w-c)^2)‖ := norm_sub_le _ _
        _ ≤ A+B*(2*r*epsilon+epsilon^2) := by
          rw [norm_mul]
          exact add_le_add (herror w hw) (mul_le_mul (hmodel w hw) hfactor (norm_nonneg _) hB)
    calc
      _ ≤ (A+B*(2*r*epsilon+epsilon^2))/(r^2/4) := (le_div_iff₀ (by positivity)).mpr hmul
      _ = _ := by ring
  · rw [closure_ball c hr.ne']
    exact hz

end NLS.ComplexAnalysis
