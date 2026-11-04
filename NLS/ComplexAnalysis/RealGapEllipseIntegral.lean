import NLS.ComplexAnalysis.RealGapEllipseHomotopy

/-! # Angular integral and limiting sides of a real-gap ellipse -/

noncomputable section
open Set Metric Complex Filter
open scoped unitInterval Topology
namespace NLS.ComplexAnalysis

private theorem deriv_scaled_realGapEllipse (c d ε t : ℝ) :
    deriv (fun x : ℝ => realGapEllipse c d ε ((2 * Real.pi) * x)) t =
      (2 * Real.pi) • deriv (realGapEllipse c d ε) ((2 * Real.pi) * t) := by
  have h := (hasDerivAt_realGapEllipse c d ε ((2 * Real.pi) * t)).scomp t
    (hasDerivAt_const_mul (2 * Real.pi))
  rw [(hasDerivAt_realGapEllipse c d ε _).deriv]
  simpa [Function.comp_def, smul_eq_mul, mul_comm] using h.deriv

/-- The ellipse curve integral written with its original angle parameter. -/
theorem curveIntegral_realGapEllipse_eq_intervalIntegral (f : ℂ → ℂ) (c d ε : ℝ) :
    (∫ᶜ z in realGapEllipsePath c d ε, holomorphicOneForm f z) =
      ∫ θ in (0 : ℝ)..(2 * Real.pi),
        deriv (realGapEllipse c d ε) θ * f (realGapEllipse c d ε θ) := by
  let q : ℝ := 2 * Real.pi
  let g : ℝ → ℂ := fun θ =>
    deriv (realGapEllipse c d ε) θ * f (realGapEllipse c d ε θ)
  have hpath (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
      (realGapEllipsePath c d ε).extend t = realGapEllipse c d ε (q * t) := by
    rw [(realGapEllipsePath c d ε).extend_apply ⟨ht.1.le, ht.2.le⟩]
    rfl
  have hderiv (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
      deriv (realGapEllipsePath c d ε).extend t =
        q • deriv (realGapEllipse c d ε) (q * t) := by
    have heq : (realGapEllipsePath c d ε).extend =ᶠ[𝓝 t]
        (fun x : ℝ => realGapEllipse c d ε (q * x)) :=
      eventually_of_mem (isOpen_Ioo.mem_nhds ht) (fun x hx => hpath x hx)
    rw [heq.deriv_eq]
    exact deriv_scaled_realGapEllipse c d ε t
  calc
    _ = ∫ t in (0 : ℝ)..1, q • g (q * t) := by
      rw [curveIntegral_eq_intervalIntegral_deriv]
      apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
      intro t ht
      simp only [holomorphicOneForm_apply]
      rw [hpath t ht, hderiv t ht]
      dsimp [g]
      ring
    _ = q • ∫ t in (0 : ℝ)..1, g (q * t) := by
      rw [intervalIntegral.integral_smul]
    _ = ∫ θ in (0 : ℝ)..q, g θ := by
      simpa only [mul_zero, mul_one] using
        (intervalIntegral.smul_integral_comp_mul_left (f := g) (a := 0) (b := 1) q)

/-- Every limiting real point lies on the enclosed gap. -/
theorem realGapEllipse_limit_mem_Icc (c d θ : ℝ) (hd : 0 ≤ d) :
    c + d * Real.cos θ ∈ Icc (c - d) (c + d) := by
  constructor <;> nlinarith [Real.neg_one_le_cos θ, Real.cos_le_one θ]

/-- The first half of a clockwise ellipse approaches the lower side. -/
theorem tendsto_realGapEllipse_lower (c d θ : ℝ) (hθ : θ ∈ Ioo 0 Real.pi) :
    Tendsto (fun ε => realGapEllipse c d ε θ) (𝓝[>] 0)
      (𝓝[{z : ℂ | z.im < 0}] (((c + d * Real.cos θ : ℝ) : ℂ))) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨(tendsto_realGapEllipse c d θ).mono_left nhdsWithin_le_nhds, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with ε hε
  rw [realGapEllipse_im]
  exact mul_neg_of_neg_of_pos (neg_neg_of_pos hε)
    (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2)

/-- The second half approaches the upper side. -/
theorem tendsto_realGapEllipse_upper (c d θ : ℝ)
    (hθ : θ ∈ Ioo Real.pi (2 * Real.pi)) :
    Tendsto (fun ε => realGapEllipse c d ε θ) (𝓝[>] 0)
      (𝓝[{z : ℂ | 0 < z.im}] (((c + d * Real.cos θ : ℝ) : ℂ))) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨(tendsto_realGapEllipse c d θ).mono_left nhdsWithin_le_nhds, ?_⟩
  have hs : Real.sin θ < 0 := by
    have hp := Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1] : 0 < θ - Real.pi)
      (by linarith [hθ.2] : θ - Real.pi < Real.pi)
    rw [Real.sin_sub_pi] at hp
    linarith
  filter_upwards [self_mem_nhdsWithin] with ε hε
  rw [realGapEllipse_im]
  exact mul_pos_of_neg_of_neg (neg_neg_of_pos hε) hs

/-- The tangent converges to the oriented real cosine tangent. -/
theorem tendsto_deriv_realGapEllipse (c d θ : ℝ) :
    Tendsto (fun ε => deriv (realGapEllipse c d ε) θ) (𝓝 0)
      (𝓝 (((-d * Real.sin θ : ℝ) : ℂ))) := by
  simp_rw [(hasDerivAt_realGapEllipse c d _ θ).deriv]
  have hc : Continuous (fun ε : ℝ =>
      (((-(d + ε) * Real.sin θ : ℝ) : ℂ) -
        ((ε * Real.cos θ : ℝ) : ℂ) * Complex.I)) := by fun_prop
  simpa only [add_zero, zero_mul, ofReal_zero, sub_zero] using
    hc.continuousAt.tendsto (x := 0)

/-- A uniform tangent bound, independent of the angular parameter. -/
theorem norm_deriv_realGapEllipse_le (c d ε θ : ℝ) (hd : 0 ≤ d) (hε : 0 ≤ ε) :
    ‖deriv (realGapEllipse c d ε) θ‖ ≤ d + 2 * ε := by
  rw [(hasDerivAt_realGapEllipse c d ε θ).deriv]
  calc
    _ ≤ ‖((-(d + ε) * Real.sin θ : ℝ) : ℂ)‖ +
        ‖((ε * Real.cos θ : ℝ) : ℂ) * Complex.I‖ := norm_sub_le _ _
    _ = (d + ε) * |Real.sin θ| + ε * |Real.cos θ| := by
      simp only [norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs,
        abs_neg, abs_of_nonneg (add_nonneg hd hε), abs_of_nonneg hε]
    _ ≤ (d + ε) * 1 + ε * 1 := add_le_add
      (mul_le_mul_of_nonneg_left (Real.abs_sin_le_one θ) (add_nonneg hd hε))
      (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one θ) hε)
    _ = _ := by ring

end NLS.ComplexAnalysis
