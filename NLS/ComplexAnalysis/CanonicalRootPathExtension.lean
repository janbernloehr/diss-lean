import NLS.ComplexAnalysis.ContinuousSquareRootPath
import NLS.ComplexAnalysis.QuadraticRootPrimitive
import Mathlib.Topology.Order.ExtendFrom

/-!
# Continued square roots with prescribed terminal values

A canonical root on the interior of an admissible path extends
continuously to a zero initial endpoint and any prescribed square root
at its terminal. A local regular sheet fixes the global sign when the
terminal is nonzero. Squaring controls the limit at zero endpoints.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped unitInterval
namespace NLS.ComplexAnalysis

private theorem continuousOn_Icc_of_open_limits (f : ℝ → ℂ)
    (hf : ContinuousOn f (Ioo (0:ℝ) 1))
    (h0 : Tendsto f (𝓝[Ioo (0:ℝ) 1] 0) (𝓝 (f 0)))
    (h1 : Tendsto f (𝓝[Ioo (0:ℝ) 1] 1) (𝓝 (f 1))) :
    ContinuousOn f (Icc (0:ℝ) 1) := by
  have hcl : Icc (0:ℝ) 1 ⊆ closure (Ioo (0:ℝ) 1) := by
    rw [closure_Ioo (by norm_num : (0:ℝ) ≠ 1)]
  have hl (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : Tendsto f (𝓝[Ioo (0:ℝ) 1] t) (𝓝 (f t)) := by
    rcases eq_endpoints_or_mem_Ioo_of_mem_Icc ht with rfl | rfl | hi
    · exact h0
    · exact h1
    · exact hf t hi
  exact (continuousOn_extendFrom hcl (fun t ht => ⟨f t,hl t ht⟩)).congr
    (fun t ht => (extendFrom_eq (hcl ht) (hl t ht)).symm)

private theorem exists_root_path_terminal_sign (F R : ℂ → ℂ) (D : Set ℂ)
    (hF : AnalyticOnNhd ℂ F univ) (hR : ContinuousOn R D)
    (hsq : ∀ z ∈ D, R z^2 = F z) {a b : ℂ} (γ : Path a b)
    (hγ : ∀ t ∈ Ioo (0:ℝ) 1, γ.extend t ∈ D)
    (w : ℂ) (hw : F b = w^2) :
    ∃ κ : ℂ, (κ = 1 ∨ κ = -1) ∧
      Tendsto (fun t : ℝ => κ*R (γ.extend t)) (𝓝[Ioo (0:ℝ) 1] 1) (𝓝 w) := by
  have hγlim : Tendsto γ.extend (𝓝[Ioo (0:ℝ) 1] 1) (𝓝 b) := by
    simpa only [Path.extend_one] using (γ.continuous_extend.tendsto 1).mono_left nhdsWithin_le_nhds
  by_cases hw0 : w = 0
  · subst w
    refine ⟨1,Or.inl rfl,?_⟩
    simp only [one_mul]
    apply tendsto_zero_of_sq_tendsto_zero
    have hh : Tendsto (fun t : ℝ => F (γ.extend t)) (𝓝[Ioo (0:ℝ) 1] 1) (𝓝 0) := by
      simpa only [Function.comp_def,hw,zero_pow (by norm_num : 2 ≠ 0)] using
        (hF b (mem_univ _)).continuousAt.tendsto.comp hγlim
    apply hh.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (hsq _ (hγ t ht)).symm
  let G := prescribedSquareRoot F w
  let V := prescribedSquareRootDomain F w
  have hbV : b ∈ V := mem_prescribedSquareRootDomain F w hw0 b hw
  have hG := analyticOnNhd_prescribedSquareRoot F w hF
  have hGb : G b = w := prescribedSquareRoot_base F w hw0 b hw
  have hevent : ∀ᶠ t : ℝ in 𝓝 1, γ.extend t ∈ V := by
    apply (γ.continuous_extend.tendsto 1).eventually
    exact (isOpen_prescribedSquareRootDomain F w hF.continuous).mem_nhds (by simpa using hbV)
  obtain ⟨ε,hε,hεV⟩ := Metric.mem_nhds_iff.mp hevent
  let c := max 0 (1-ε)
  have hc : c < 1 := max_lt (by norm_num) (by linarith)
  have hsub : Ioo c 1 ⊆ Ioo (0:ℝ) 1 := fun _ ht => ⟨(le_max_left _ _).trans_lt ht.1,ht.2⟩
  have hmem (t : ℝ) (ht : t ∈ Ioo c 1) : γ.extend t ∈ V := by
    apply hεV
    rw [mem_ball,Real.dist_eq,abs_of_neg (sub_neg.mpr ht.2)]
    have := (le_max_right 0 (1-ε)).trans_lt ht.1
    linarith
  obtain ⟨κ,hκ,hκeq⟩ := exists_fixed_sign_of_sq_eq_on_preconnected
    (fun t : ℝ => R (γ.extend t)) (fun t : ℝ => G (γ.extend t)) (Ioo c 1)
    (convex_Ioo c 1).isPreconnected
    (hR.comp γ.continuous_extend.continuousOn (fun t ht => hγ t (hsub ht)))
    (hG.continuousOn.comp γ.continuous_extend.continuousOn hmem)
    (fun t ht => (hsq _ (hγ t (hsub ht))).trans (prescribedSquareRoot_sq F w hw0 _).symm)
    (fun t ht => prescribedSquareRoot_ne_zero F w hw0 _ (hmem t ht))
  refine ⟨κ,hκ,?_⟩
  have hlim : Tendsto (fun t : ℝ => G (γ.extend t)) (𝓝[Ioo (0:ℝ) 1] 1) (𝓝 w) := by
    have hh := (hG b hbV).continuousAt.tendsto.comp hγlim
    change Tendsto (fun t : ℝ => G (γ.extend t)) (𝓝[Ioo (0:ℝ) 1] 1) (𝓝 (G b)) at hh
    rwa [hGb] at hh
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin,nhdsWithin_le_nhds (Ioi_mem_nhds hc)] with t ht hct
  rw [hκeq t ⟨hct,ht.2⟩]
  rcases hκ with rfl | rfl <;> simp

/-- Extend the canonical interior root with any valid terminal value and zero initial value. -/
theorem exists_continuous_canonical_path_root (F R : ℂ → ℂ) (D : Set ℂ)
    (hF : AnalyticOnNhd ℂ F univ) (hR : ContinuousOn R D)
    (hsq : ∀ z ∈ D, R z^2 = F z) {a b : ℂ} (γ : Path a b)
    (ha : a ∉ D) (hFa : F a = 0)
    (hγ : ∀ t ∈ Ioo (0:ℝ) 1, γ.extend t ∈ D)
    (w : ℂ) (hw : F b = w^2) :
    ∃ Q : ℂ → ℂ, ContinuousOn (fun t : ℝ => Q (γ.extend t)) (Icc 0 1) ∧
      (∀ t ∈ Icc (0:ℝ) 1, Q (γ.extend t)^2 = F (γ.extend t)) ∧
      Q a = 0 ∧ Q b = w ∧
      ∃ κ : ℂ, (κ = 1 ∨ κ = -1) ∧ ∀ t ∈ Ioo (0:ℝ) 1,
        Q (γ.extend t) = κ*R (γ.extend t) := by
  classical
  obtain ⟨κ,hκ,hlim1⟩ := exists_root_path_terminal_sign F R D hF hR hsq γ hγ w hw
  let f : ℝ → ℂ := fun t => κ*R (γ.extend t)
  have hsquare (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) : f t^2 = F (γ.extend t) := by
    dsimp only [f]
    rw [mul_pow,hsq _ (hγ t ht)]
    rcases hκ with rfl | rfl <;> simp
  have hlim0 : Tendsto f (𝓝[Ioo (0:ℝ) 1] 0) (𝓝 0) := by
    apply tendsto_zero_of_sq_tendsto_zero
    have hγ0 : Tendsto γ.extend (𝓝[Ioo (0:ℝ) 1] 0) (𝓝 a) := by
      simpa only [Path.extend_zero] using (γ.continuous_extend.tendsto 0).mono_left nhdsWithin_le_nhds
    have hlim := (hF a (mem_univ _)).continuousAt.tendsto.comp hγ0
    simp only [Function.comp_def,hFa] at hlim
    apply hlim.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (hsquare t ht).symm
  have hbb (hb : b ∈ D) : κ*R b = w := by
    have hlim : Tendsto (fun t : ℝ => κ*R (γ.extend t)) (𝓝[Ioo (0:ℝ) 1] 1) (𝓝 (κ*R b)) := by
      apply tendsto_const_nhds.mul
      apply (hR b hb).tendsto.comp
      apply tendsto_nhdsWithin_iff.mpr
      exact ⟨by simpa only [Path.extend_one] using
        (γ.continuous_extend.tendsto 1).mono_left nhdsWithin_le_nhds,
        Filter.Eventually.mono self_mem_nhdsWithin hγ⟩
    have : NeBot (𝓝[Ioo (0:ℝ) 1] 1) := by
      rw [nhdsWithin_Ioo_eq_nhdsLT zero_lt_one]
      infer_instance
    exact tendsto_nhds_unique hlim hlim1
  let Q : ℂ → ℂ := fun z => if z = a then 0 else if z = b then w else κ*R z
  have hQa : Q a = 0 := by simp [Q]
  have hQb : Q b = w := by
    by_cases hba : b = a
    · have hw0 : w = 0 := by apply sq_eq_zero_iff.mp; rw [← hw,hba,hFa]
      simp [Q,hba,hw0]
    · simp [Q,hba]
  have hQf (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) : Q (γ.extend t) = f t := by
    have hna : γ.extend t ≠ a := fun h => ha (h ▸ hγ t ht)
    by_cases hnb : γ.extend t = b
    · have hb := hnb ▸ hγ t ht
      simp only [hnb,hQb,f]
      exact (hbb hb).symm
    · simp [Q,hna,hnb,f]
  have hcont : ContinuousOn f (Ioo (0:ℝ) 1) :=
    continuousOn_const.mul (hR.comp γ.continuous_extend.continuousOn hγ)
  refine ⟨Q,?_,?_,hQa,hQb,κ,hκ,hQf⟩
  · apply continuousOn_Icc_of_open_limits
    · exact hcont.congr hQf
    · simp only [Path.extend_zero,hQa]
      apply hlim0.congr'
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact (hQf t ht).symm
    · simp only [Path.extend_one,hQb]
      apply hlim1.congr'
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact (hQf t ht).symm
  · intro t ht
    rcases eq_endpoints_or_mem_Ioo_of_mem_Icc ht with rfl | rfl | hi
    · simp [hQa,hFa]
    · simp [hQb,hw]
    · rw [hQf t hi]
      exact hsquare t hi

end NLS.ComplexAnalysis
