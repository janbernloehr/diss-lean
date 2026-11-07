import NLS.ComplexAnalysis.CoupledQuadraticError
import NLS.ComplexAnalysis.ZeroCountComparison

/-! Rouché isolates one zero near each root of a coupled quadratic.
No analytic square-root branch is needed. -/
noncomputable section
open Set Metric
open scoped Classical
namespace NLS.ComplexAnalysis

theorem coupledRootDisc_subset (α u : ℂ) :
    closedBall (α+u) (‖u‖/2)⊆closedBall α (2*‖u‖) := by
  intro z hz
  have hd : ‖z-(α+u)‖≤‖u‖/2 := by simpa only [mem_closedBall,dist_eq_norm] using hz
  rw [mem_closedBall,dist_eq_norm]
  have ht := norm_sub_le_norm_sub_add_norm_sub z (α+u) α
  simp only [add_sub_cancel_left] at ht
  linarith [norm_nonneg u]

theorem coupledQuadratic_boundary_lower (α u z : ℂ)
    (hz : z ∈ sphere (α+u) (‖u‖/2)) :
    3*‖u‖^2/4≤‖(z-α)^2-u^2‖ := by
  have hfirst : ‖z-α-u‖=‖u‖/2 := by
    have hh : ‖z-(α+u)‖=‖u‖/2 := by simpa only [mem_sphere,dist_eq_norm] using hz
    simpa only [sub_add_eq_sub_sub] using hh
  have htwo : 2*‖u‖≤‖z-α+u‖+‖z-α-u‖ := by
    calc
      _ = ‖(2:ℂ)*u‖ := by rw [norm_mul]; norm_num
      _ = ‖(z-α+u)-(z-α-u)‖ := by congr 1; ring
      _ ≤ _ := norm_sub_le _ _
  have hsecond : 3*‖u‖/2≤‖z-α+u‖ := by linarith
  have he : (z-α)^2-u^2=(z-α-u)*(z-α+u) := by ring
  rw [he,norm_mul,hfirst]
  nlinarith [mul_le_mul_of_nonneg_left hsecond (show 0≤‖u‖/2 by positivity)]

theorem analyticZeroCount_coupledQuadratic_one (α u : ℂ) (hu : u≠0) :
    analyticZeroCount (fun z : ℂ => (z-α)^2-u^2) (closedBall (α+u) (‖u‖/2))=1 := by
  have hρ : 0<‖u‖ := norm_pos_iff.mpr hu
  have hcenter : α+u ∈ closedBall (α+u) (‖u‖/2) := mem_closedBall_self (by positivity)
  rw [analyticZeroCount_eq_sum {α+u} (by simpa only [Finset.coe_singleton,Set.singleton_subset_iff] using hcenter) ?_]
  · simp only [Finset.sum_singleton]
    have ha : AnalyticAt ℂ (fun z : ℂ => (z-α)^2-u^2) (α+u) := by fun_prop
    have hz0 : (α+u-α)^2-u^2=0 := by ring
    have hd : HasDerivAt (fun z : ℂ => (z-α)^2-u^2) (2*u) (α+u) := by
      simpa using ((((hasDerivAt_id (α+u)).sub_const α).pow 2).sub_const (u^2))
    have ho := ha.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hz0 (by
      rw [hd.deriv]
      exact mul_ne_zero (by norm_num) hu)
    change (analyticOrderAt (fun z : ℂ => (z-α)^2-u^2) (α+u)).toNat=1
    rw [ho]
    rfl
  · intro z hz
    have hf : (z-α-u)*(z-α+u)=0 := by
      calc
        _ = (z-α)^2-u^2 := by ring
        _ = 0 := hz.2
    rcases mul_eq_zero.mp hf with hp | hm
    · have he : z=α+u := by linear_combination hp
      simpa only [Finset.mem_coe,Finset.mem_singleton] using he
    · have he : z=α-u := by linear_combination hm
      have hd : ‖z-(α+u)‖≤‖u‖/2 := by simpa only [mem_closedBall,dist_eq_norm] using hz.1
      have heq : z-(α+u)=(-2:ℂ)*u := by rw [he]; ring
      rw [heq,norm_mul] at hd
      norm_num only [norm_neg,Complex.norm_ofNat] at hd
      linarith

theorem exists_zero_of_analyticZeroCount_ne_zero (f : ℂ → ℂ) (K : Set ℂ)
    (h : analyticZeroCount f K≠0) : ∃ z ∈ K, f z=0 := by
  by_contra hn
  push Not at hn
  apply h
  unfold analyticZeroCount
  apply finsum_eq_zero_of_forall_eq_zero
  intro z
  by_cases hz : z ∈ K
  · rw [if_pos hz]
    by_contra ho
    exact hn z hz (apply_eq_zero_of_analyticOrderNatAt_ne_zero ho)
  · exact if_neg hz

theorem exists_zero_near_coupled_root (f : ℂ → ℂ) (α u : ℂ) (hu : u≠0)
    (hf : AnalyticOnNhd ℂ f (closedBall (α+u) (‖u‖/2)))
    (hb : ∀ z ∈ sphere (α+u) (‖u‖/2), ‖f z-((z-α)^2-u^2)‖≤‖u‖^2/3) :
    ∃ z ∈ closedBall (α+u) (‖u‖/2), f z=0 := by
  have hρ : 0<‖u‖ := norm_pos_iff.mpr hu
  have hcount := analyticZeroCount_eq_of_boundary_lt (show 0<‖u‖/2 by positivity)
    (show AnalyticOnNhd ℂ (fun z : ℂ => (z-α)^2-u^2) (closedBall (α+u) (‖u‖/2)) from by
      intro z _; fun_prop) hf (fun z hz => (hb z hz).trans_lt (by
        have hlo := coupledQuadratic_boundary_lower α u z hz
        nlinarith [sq_pos_of_pos hρ]))
  rw [analyticZeroCount_coupledQuadratic_one α u hu] at hcount
  exact exists_zero_of_analyticZeroCount_ne_zero f _ (by omega)

end NLS.ComplexAnalysis
