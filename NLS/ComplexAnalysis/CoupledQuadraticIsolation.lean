import NLS.ComplexAnalysis.CoupledRootDiscs

/-! Complex root separation for a nearly constant coupled quadratic.
The two isolated discs provide both bounds without selecting a branch. -/
noncomputable section
open Set Metric
namespace NLS.ComplexAnalysis

theorem coupledQuadratic_isolated_roots (f d b c : ℂ → ℂ) (α u b₀ c₀ : ℂ)
    (hu : u≠0) (hu₂ : u^2=b₀*c₀)
    (hf : AnalyticOnNhd ℂ f (closedBall α (2*‖u‖)))
    (he : ∀ z ∈ closedBall α (2*‖u‖), f z=(z-α-d z)^2-b z*c z)
    (hb₀ : ‖b₀‖≤3*‖u‖) (hc₀ : ‖c₀‖≤3*‖u‖)
    (hsmall : ∀ z ∈ closedBall α (2*‖u‖),
      ‖d z‖≤‖u‖/44 ∧ ‖b z-b₀‖≤‖u‖/44 ∧ ‖c z-c₀‖≤‖u‖/44) :
    ∃ x ∈ closedBall (α+u) (‖u‖/2), ∃ y ∈ closedBall (α-u) (‖u‖/2),
      f x=0 ∧ f y=0 ∧ ‖u‖≤‖x-y‖ ∧ ‖x-y‖≤3*‖u‖ := by
  have hbound (z : ℂ) (hz : z ∈ closedBall α (2*‖u‖)) :
      ‖f z-((z-α)^2-u^2)‖≤‖u‖^2/3 := by
    rw [he z hz,hu₂]
    have hx : ‖z-α‖≤2*‖u‖ := by simpa only [mem_closedBall,dist_eq_norm] using hz
    obtain ⟨hd,hb,hc⟩ := hsmall z hz
    exact coupledQuadraticError_le ‖u‖ (norm_nonneg u) (z-α) (d z) (b z) (c z) b₀ c₀ hx hd hb hc hb₀ hc₀
  obtain ⟨x,hx,hfx⟩ := exists_zero_near_coupled_root f α u hu
    (hf.mono (coupledRootDisc_subset α u)) (fun z hz =>
      hbound z (coupledRootDisc_subset α u (sphere_subset_closedBall hz)))
  have hminus : ∃ y ∈ closedBall (α-u) (‖u‖/2), f y=0 := by
    have hs : closedBall (α+ -u) (‖-u‖/2)⊆closedBall α (2*‖u‖) := by
      simpa only [norm_neg] using coupledRootDisc_subset α (-u)
    have hh := exists_zero_near_coupled_root f α (-u) (neg_ne_zero.mpr hu) (hf.mono hs) (fun z hz => by
      simpa only [norm_neg,neg_sq] using hbound z (hs (sphere_subset_closedBall hz)))
    simpa only [norm_neg,sub_eq_add_neg] using hh
  obtain ⟨y,hy,hfy⟩ := hminus
  have hcent : dist (α+u) (α-u)=2*‖u‖ := by
    rw [dist_eq_norm,show α+u-(α-u)=(2:ℂ)*u by ring,norm_mul]
    norm_num
  have hx' : dist x (α+u)≤‖u‖/2 := hx
  have hy' : dist y (α-u)≤‖u‖/2 := hy
  refine ⟨x,hx,y,hy,hfx,hfy,?_,?_⟩
  · have h₁ := dist_triangle (α+u) x (α-u)
    have h₂ := dist_triangle x y (α-u)
    rw [hcent,dist_comm (α+u) x] at h₁
    rw [← dist_eq_norm]
    linarith
  · have h₁ := dist_triangle x (α+u) y
    have h₂ := dist_triangle (α+u) (α-u) y
    rw [hcent,dist_comm (α-u) y] at h₂
    rw [← dist_eq_norm]
    linarith

end NLS.ComplexAnalysis
