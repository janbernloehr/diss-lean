import NLS.ZakharovShabat.SourceStandardRootEllipsePeriod

/-!
# Maximum and real mean-value estimates for local gap contours

The exact cosine-average formula gives both conclusions of Lemma 12.3.
In particular, arbitrary analytic gap neighborhoods admit actual ellipse
contours satisfying the estimates, without a filled-disk hypothesis.
-/

noncomputable section
open Set Metric Complex Filter MeasureTheory NLS.ComplexAnalysis
open scoped Topology
namespace NLS.ZakharovShabat

/-- The maximum estimate follows from the gap-average formula. -/
theorem norm_standardRoot_gap_period_le (τ δ : ℂ) (f : ℂ → ℂ) (J : ℂ) (M : ℝ)
    (hbound : ∀ z ∈ standardRootGapSegment τ δ, ‖f z‖ ≤ M)
    (hJ : J = (-(2*(Real.pi:ℂ))*Complex.I)*
      (∫ t in (0:ℝ)..1, f (τ+δ*(Real.cos ((2*Real.pi)*t):ℂ)))) :
    ‖(2*(Real.pi:ℂ))⁻¹*J‖ ≤ M := by
  have hi : ‖∫ t in (0:ℝ)..1, f (τ+δ*(Real.cos ((2*Real.pi)*t):ℂ))‖ ≤ M := by
    simpa using (intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0:ℝ)) (b := 1) (C := M) (fun t _ =>
        hbound _ ⟨Real.cos ((2*Real.pi)*t),Real.cos_mem_Icc _,rfl⟩))
  rw [hJ]
  simp only [norm_mul,norm_inv,norm_neg,norm_I,mul_one]
  rw [← mul_assoc,inv_mul_cancel₀ (mul_ne_zero (by simp) (by simp [Real.pi_ne_zero])),one_mul]
  exact hi

/-- A numerator real on the gap attains its cosine average somewhere on that gap. -/
theorem standardRoot_gap_period_real_mean_value (τ δ : ℂ) (f : ℂ → ℂ) (J : ℂ)
    (hf : ContinuousOn f (standardRootGapSegment τ δ))
    (hreal : ∀ z ∈ standardRootGapSegment τ δ, (f z).im = 0)
    (hJ : J = (-(2*(Real.pi:ℂ))*Complex.I)*
      (∫ t in (0:ℝ)..1, f (τ+δ*(Real.cos ((2*Real.pi)*t):ℂ)))) :
    ∃ z ∈ standardRootGapSegment τ δ, (2*(Real.pi:ℂ)*Complex.I)⁻¹*J = -f z := by
  let q : ℝ → ℂ := fun t => τ+δ*(Real.cos ((2*Real.pi)*t):ℂ)
  let F : ℝ → ℝ := fun t => (f (q t)).re
  have hFc : Continuous F := Complex.continuous_re.comp
    ((gapSidePath_continuous τ δ f hf).comp (show Continuous (fun t : ℝ => (2*Real.pi)*t) by fun_prop))
  obtain ⟨t,_,hm⟩ := exists_eq_const_mul_intervalIntegral_of_nonneg
    (a := (0:ℝ)) (b := 1) (f := F) (g := fun _ : ℝ => (1:ℝ)) (μ := volume)
    hFc.continuousOn intervalIntegrable_const (by intro x hx; norm_num)
  have hm' : (∫ x in (0:ℝ)..1, F x) = F t := by simpa using hm
  have hpoint (x : ℝ) : f (q x) = (F x:ℂ) := by
    apply Complex.ext
    · rfl
    · simp only [Complex.ofReal_im]
      exact hreal _ ⟨Real.cos ((2*Real.pi)*x),Real.cos_mem_Icc _,rfl⟩
  have hmean : (∫ x in (0:ℝ)..1, f (q x)) = f (q t) := by
    simp_rw [hpoint]
    rw [intervalIntegral.integral_ofReal,hm']
  refine ⟨q t,⟨Real.cos ((2*Real.pi)*t),Real.cos_mem_Icc _,rfl⟩,?_⟩
  rw [hJ]
  change (2*(Real.pi:ℂ)*Complex.I)⁻¹*
    ((-(2*(Real.pi:ℂ))*Complex.I)*(∫ x in (0:ℝ)..1, f (q x))) = _
  rw [hmean]
  have hπ : (2*(Real.pi:ℂ)*Complex.I) ≠ 0 := by simp [Real.pi_ne_zero]
  field_simp

/-- Both local estimates hold on all sufficiently small actual ellipse contours.
The maximum is attained at one point, chosen independently of the ellipse radius. -/
theorem exists_standardRootEllipse_local_estimates (τ δ : ℂ) (hδ : δ ≠ 0)
    (U : Set ℂ) (hU : IsOpen U) (hgap : standardRootGapSegment τ δ ⊆ U)
    (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f U) :
    ∃ R : ℝ, 1 < R ∧ ∃ z ∈ standardRootGapSegment τ δ,
      IsMaxOn (fun w => ‖f w‖) (standardRootGapSegment τ δ) z ∧
      ∀ r : ℝ, ∀ hr : 1 < r, r ≤ R →
        (standardRootEllipseLoop τ δ r (by linarith)).Inside (U \ standardRootGapSegment τ δ) ∧
        ‖(2*(Real.pi:ℂ))⁻¹*(standardRootEllipseLoop τ δ r (by linarith)).integral
          (fun w => f w/normalizedStandardRoot τ ((2*δ)^2) w)‖ ≤ ‖f z‖ ∧
        ((∀ w ∈ standardRootGapSegment τ δ, (f w).im = 0) →
          ∃ μ ∈ standardRootGapSegment τ δ,
            (standardRootEllipseLoop τ δ r (by linarith)).normalizedIntegral
              (fun w => f w/normalizedStandardRoot τ ((2*δ)^2) w) = -f μ) := by
  have hfc : ContinuousOn f (standardRootGapSegment τ δ) := hf.continuousOn.mono hgap
  have hne : (standardRootGapSegment τ δ).Nonempty := ⟨τ,⟨0,by norm_num,by simp⟩⟩
  obtain ⟨z,hz,hmax⟩ := (standardRootGapSegment_compact τ δ).exists_isMaxOn hne hfc.norm
  obtain ⟨R,hR,hperiod⟩ := exists_standardRootEllipse_local_period τ δ hδ U hU hgap f hf
  refine ⟨R,hR,z,hz,hmax,fun r hr hrR => ?_⟩
  obtain ⟨hin,he⟩ := hperiod r hr hrR
  refine ⟨hin,norm_standardRoot_gap_period_le τ δ f _ _ hmax he,?_⟩
  intro hreal
  exact standardRoot_gap_period_real_mean_value τ δ f _ hfc hreal he

end NLS.ZakharovShabat
