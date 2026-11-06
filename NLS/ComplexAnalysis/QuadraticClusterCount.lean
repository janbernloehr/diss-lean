import NLS.ComplexAnalysis.ZeroCountComparison
import NLS.ComplexAnalysis.ZeroMultiset

/-! # Two-root counts from a quadratic model

A uniform boundary perturbation of the free quadratic square has two
interior roots with their exact analytic multiplicities. The roots may
coincide. Nonvanishing on the full boundary is proved separately.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
open scoped Classical
namespace NLS.ComplexAnalysis

/-- A nonzero scalar factor preserves every analytic zero multiplicity. -/
theorem analyticZeroCount_nonzero_const_mul (f : ℂ → ℂ) (K : Set ℂ)
    (hf : AnalyticOnNhd ℂ f K) (a : ℂ) (ha : a ≠ 0) :
    analyticZeroCount (fun z => a*f z) K = analyticZeroCount f K := by
  unfold analyticZeroCount
  apply finsum_congr
  intro z
  by_cases hz : z ∈ K
  · simp only [if_pos hz]
    have he : analyticOrderAt (fun z => a*f z) z = analyticOrderAt f z := by
      have hm := analyticOrderAt_mul (f := fun _ : ℂ => a) (g := f) analyticAt_const (hf z hz)
      have hefun : ((fun _ : ℂ => a)*f) = (fun w : ℂ => a*f w) := by funext w; rfl
      rw [hefun] at hm
      have hc : analyticOrderAt (fun _ : ℂ => a) z = 0 :=
        analyticOrderAt_eq_zero.mpr (Or.inr ha)
      simpa only [hc,zero_add] using hm
    exact congrArg ENat.toNat he
  · simp only [if_neg hz]

/-- Rouché counts both roots of the free quadratic model with multiplicity. -/
theorem analyticZeroCount_eq_two_of_quadratic_model
    (c r : ℝ) (hc : 0 < c) (hr : 0 < r) (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (closedBall ((c : ℂ)^2) (c*r)))
    (herror : ∀ z ∈ sphere ((c : ℂ)^2) (c*r),
      ‖f z- (-(z-(c : ℂ)^2)^2/(4*(c : ℂ)^2))‖ ≤ r^2/16) :
    analyticZeroCount f (closedBall ((c : ℂ)^2) (c*r)) = 2 := by
  let a : ℂ := -4*(c : ℂ)^2
  have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have ha : a ≠ 0 := by dsimp [a]; exact mul_ne_zero (by norm_num) (pow_ne_zero _ hcC)
  have hnorma : ‖a‖ = 4*c^2 := by simp [a,abs_of_pos hc]
  have hcount : analyticZeroCount (fun z => a*f z) (closedBall ((c : ℂ)^2) (c*r)) = 2 := by
    apply analyticZeroCount_eq_degree_of_boundary_lt 2 (mul_pos hc hr)
      (analyticOnNhd_const.mul hf)
    intro z hz
    have hmodel : a*(-(z-(c : ℂ)^2)^2/(4*(c : ℂ)^2)) = (z-(c : ℂ)^2)^2 := by
      dsimp [a]
      field_simp [hcC]
    have he : a*f z-(z-(c : ℂ)^2)^2 =
        a*(f z- (-(z-(c : ℂ)^2)^2/(4*(c : ℂ)^2))) := by rw [mul_sub,hmodel]
    have hboundary : ‖z-(c : ℂ)^2‖ = c*r := by simpa only [mem_sphere,dist_eq_norm] using hz
    rw [he,norm_mul,hnorma,norm_pow,hboundary]
    calc
      _ ≤ 4*c^2*(r^2/16) := mul_le_mul_of_nonneg_left (herror z hz) (by positivity)
      _ < (c*r)^2 := by nlinarith [mul_pos (sq_pos_of_pos hc) (sq_pos_of_pos hr)]
  rw [analyticZeroCount_nonzero_const_mul f _ hf a ha] at hcount
  exact hcount

/-- The same perturbation is nonzero on the entire boundary. -/
theorem quadratic_model_boundary_ne_zero
    (c r : ℝ) (hc : 0 < c) (hr : 0 < r) (f : ℂ → ℂ)
    (herror : ∀ z ∈ sphere ((c : ℂ)^2) (c*r),
      ‖f z- (-(z-(c : ℂ)^2)^2/(4*(c : ℂ)^2))‖ ≤ r^2/16) :
    ∀ z ∈ sphere ((c : ℂ)^2) (c*r), f z ≠ 0 := by
  intro z hz hfz
  have he := herror z hz
  have hd : ‖z-(c : ℂ)^2‖ = c*r := by
    simpa only [mem_sphere,dist_eq_norm] using hz
  have hden : ‖(4 : ℂ)*(c : ℂ)^2‖ = 4*c^2 := by simp [abs_of_pos hc]
  rw [hfz,zero_sub,norm_neg,norm_div,norm_neg,norm_pow,hd,hden] at he
  have hmodel : (c*r)^2/(4*c^2) = r^2/4 := by field_simp
  rw [hmodel] at he
  nlinarith [sq_pos_of_pos hr]

/-- Two genuine roots, with repetition and exact analytic multiplicities,
lie in the open model disc. -/
theorem exists_two_zeros_of_quadratic_model
    (c r : ℝ) (hc : 0 < c) (hr : 0 < r) (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (closedBall ((c : ℂ)^2) (c*r)))
    (herror : ∀ z ∈ sphere ((c : ℂ)^2) (c*r),
      ‖f z- (-(z-(c : ℂ)^2)^2/(4*(c : ℂ)^2))‖ ≤ r^2/16) :
    ∃ l ∈ ball ((c : ℂ)^2) (c*r), ∃ u ∈ ball ((c : ℂ)^2) (c*r),
      f l = 0 ∧ f u = 0 ∧
      (∀ z, (if z ∈ closedBall ((c : ℂ)^2) (c*r) then analyticOrderNatAt f z else 0) =
        ({l,u} : Multiset ℂ).count z) ∧
      ∀ z ∈ closedBall ((c : ℂ)^2) (c*r), f z = 0 ↔ z = l ∨ z = u := by
  classical
  have hR := mul_pos hc hr
  have hb := quadratic_model_boundary_ne_zero c r hc hr f herror
  let b : ℂ := (c : ℂ)^2 + (c*r : ℝ)
  have hbS : b ∈ sphere ((c : ℂ)^2) (c*r) := by
    simp [b,abs_of_pos hc,abs_of_pos hr]
  have hbK := sphere_subset_closedBall hbS
  have hconn := isConnected_closedBall (x := (c : ℂ)^2) hR.le
  have hs := analyticZeroCount_hasFiniteSupport (isCompact_closedBall _ _) hconn hf hbK (hb b hbS)
  obtain ⟨l,hl,u,hu,hfl,hfu,hm⟩ := exists_two_analytic_zeros hs
    (analyticZeroCount_eq_two_of_quadratic_model c r hc hr f hf herror)
  have hopen (z : ℂ) (hz : z ∈ closedBall ((c : ℂ)^2) (c*r)) (hzero : f z = 0) :
      z ∈ ball ((c : ℂ)^2) (c*r) := lt_of_le_of_ne hz (fun he => hb z he hzero)
  refine ⟨l,hopen l hl hfl,u,hopen u hu hfu,hfl,hfu,hm,?_⟩
  intro z hz
  constructor
  · intro hzero
    have hfinite := analyticOrderAt_ne_top_on_connected hconn.isPreconnected hf hbK (hb b hbS) hz
    have hpos := analyticOrderNatAt_pos_of_zero (hf z hz) hfinite hzero
    have hmz := hm z
    rw [if_pos hz] at hmz
    have hmem : z ∈ ({l,u} : Multiset ℂ) := Multiset.count_pos.mp (hmz ▸ hpos)
    simpa using hmem
  · rintro (rfl | rfl) <;> assumption

end NLS.ComplexAnalysis
