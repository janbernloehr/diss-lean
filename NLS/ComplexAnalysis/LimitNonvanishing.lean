import NLS.ComplexAnalysis.EntireLimit

/-!
# Nonvanishing limits from boundary bounds

For holomorphic approximants without zeros on a closed disc, a positive
boundary lower bound propagates to the center by applying the maximum
modulus principle to the reciprocals.
-/

noncomputable section
open Filter Topology Metric
namespace NLS.ComplexAnalysis

/-- A uniform boundary limit which is nonzero on the circle cannot acquire a zero at the center
when the holomorphic approximants have no zeros on the closed disc. -/
theorem limit_ne_zero_of_nonzero_on_closedBall (F : ℕ → ℂ → ℂ) (g : ℂ → ℂ)
    (c : ℂ) (r : ℝ) (hr : 0 < r)
    (hF : ∀ n, Differentiable ℂ (F n))
    (hFn : ∀ n, ∀ z ∈ closedBall c r, F n z ≠ 0)
    (hc : ContinuousOn g (sphere c r)) (hg : ∀ z ∈ sphere c r, g z ≠ 0)
    (h : TendstoUniformlyOn F g atTop (sphere c r))
    (hlim : Tendsto (fun n => F n c) atTop (𝓝 (g c))) : g c ≠ 0 := by
  obtain ⟨δ,hδ,hb⟩ := (isCompact_sphere c r).exists_forall_le' hc.norm
    (fun z hz => norm_pos_iff.mpr (hg z hz))
  have he := (Metric.tendstoUniformlyOn_iff.mp h) (δ/2) (half_pos hδ)
  have hbound : ∀ᶠ n : ℕ in atTop, 1 ≤ ‖F n c‖*(2/δ) := by
    filter_upwards [he] with n hn
    have hi : ‖(F n c)⁻¹‖ ≤ 2/δ := by
      apply Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball
        (show DiffContOnCl ℂ (fun z => (F n z)⁻¹) (ball c r) from
          (((hF n).differentiableOn).inv (fun z hz => hFn n z
            (by simpa only [closure_ball c (ne_of_gt hr)] using hz))).diffContOnCl)
      · intro z hz
        rw [frontier_ball c (ne_of_gt hr)] at hz
        have hd : δ/2 ≤ ‖F n z‖ := by
          have hn' := hn z hz
          rw [dist_eq_norm] at hn'
          have ht' : ‖g z‖ ≤ ‖g z-F n z‖+‖F n z‖ := by
            simpa only [sub_add_cancel] using norm_add_le (g z-F n z) (F n z)
          linarith [hb z hz]
        rw [norm_inv]
        calc
          ‖F n z‖⁻¹ ≤ (δ/2)⁻¹ := inv_anti₀ (half_pos hδ) hd
          _ = 2/δ := by field_simp
      · simp [closure_ball c (ne_of_gt hr), hr.le]
    have hn0 : F n c ≠ 0 := hFn n c (mem_closedBall_self hr.le)
    have hm := mul_le_mul_of_nonneg_left hi (norm_nonneg (F n c))
    simpa only [← norm_mul, mul_inv_cancel₀ hn0, norm_one] using hm
  have hle : 1 ≤ ‖g c‖*(2/δ) := ge_of_tendsto (hlim.norm.mul_const (2/δ)) hbound
  intro hzero
  norm_num [hzero] at hle

/-- A small circle about any center can avoid a countable exceptional set. -/
theorem exists_small_sphere_subset_compl_countable (S : Set ℂ) (hS : S.Countable)
    (c : ℂ) (R : ℝ) (hR : 0 < R) :
    ∃ r : ℝ, 0 < r ∧ r < R ∧ sphere c r ⊆ Sᶜ := by
  obtain ⟨r,hr,hrange⟩ := ((hS.image (fun z : ℂ => dist z c)).dense_compl ℝ).exists_mem_open
    isOpen_Ioo (Set.nonempty_Ioo.mpr hR)
  refine ⟨r,hrange.1,hrange.2,?_⟩
  intro z hz hzs
  exact hr ⟨z,hzs,by simpa only [mem_sphere] using hz⟩

end NLS.ComplexAnalysis
