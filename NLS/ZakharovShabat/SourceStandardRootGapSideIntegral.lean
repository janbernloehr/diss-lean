import NLS.ZakharovShabat.SourceStandardRootGapSideJoint
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/- The cosine parametrization of a gap side removes the inverse-square-root
   endpoint singularity in Lemma 10.4. Here `upper = true` selects the upper
   boundary value; `false` selects the lower one. -/

noncomputable section
open Complex MeasureTheory intervalIntegral
open scoped Topology

namespace NLS.ZakharovShabat

/-- The closed gap with midpoint `τ` and complex half-gap `δ`. -/
def standardRootGapSegment (τ δ : ℂ) : Set ℂ :=
  (fun r : ℝ => τ+δ*(r:ℂ)) '' Set.Icc (-1:ℝ) 1

/-- Every standard-root gap segment is compact, including a collapsed one. -/
theorem standardRootGapSegment_compact (τ δ : ℂ) :
    IsCompact (standardRootGapSegment τ δ) := by
  unfold standardRootGapSegment
  exact isCompact_Icc.image (by fun_prop)

theorem gapSidePath_continuous (τ δ : ℂ) (f : ℂ → ℂ)
    (hf : ContinuousOn f (standardRootGapSegment τ δ)) :
    Continuous (fun θ : ℝ => f (τ+δ*(Real.cos θ:ℂ))) := by
  have hpath : Continuous (fun θ : ℝ => τ+δ*(Real.cos θ:ℂ)) := by fun_prop
  have hmem : ∀ θ : ℝ, τ+δ*(Real.cos θ:ℂ) ∈ standardRootGapSegment τ δ := by
    intro θ
    exact ⟨Real.cos θ, Real.cos_mem_Icc θ, rfl⟩
  simpa only [Function.comp_def] using hf.comp_continuous hpath hmem

/-- The regularized side primitive. The cosine substitution turns the
    square-root weighted integral from `-1` to `t` into this ordinary integral. -/
def gapSidePrimitive (τ δ : ℂ) (f : ℂ → ℂ) (t : ℝ) (upper : Bool) : ℂ :=
  (if upper then I else -I) *
    ∫ θ in Real.arccos t..Real.pi, f (τ+δ*(Real.cos θ:ℂ))

theorem gapSidePath_intervalIntegrable (τ δ : ℂ) (f : ℂ → ℂ)
    (hf : ContinuousOn f (standardRootGapSegment τ δ)) (t : ℝ) :
    IntervalIntegrable (fun θ : ℝ => f (τ+δ*(Real.cos θ:ℂ))) volume
      (Real.arccos t) Real.pi :=
  (gapSidePath_continuous τ δ f hf).intervalIntegrable _ _

theorem gapSidePrimitive_norm_le (τ δ : ℂ) (f : ℂ → ℂ) (t M : ℝ)
    (hM : 0 ≤ M)
    (hf : ∀ r ∈ Set.Icc (-1:ℝ) 1, ‖f (τ+δ*(r:ℂ))‖ ≤ M)
    (upper : Bool) :
    ‖gapSidePrimitive τ δ f t upper‖ ≤ Real.pi * M := by
  have hi : ‖∫ θ in Real.arccos t..Real.pi,
      f (τ+δ*(Real.cos θ:ℂ))‖ ≤ M * |Real.pi-Real.arccos t| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro θ hθ
    exact hf (Real.cos θ) (Real.cos_mem_Icc θ)
  have hangle : |Real.pi-Real.arccos t| ≤ Real.pi := by
    rw [abs_of_nonneg (sub_nonneg.mpr (Real.arccos_le_pi t))]
    linarith [Real.arccos_nonneg t]
  have hnorm : ‖gapSidePrimitive τ δ f t upper‖ =
      ‖∫ θ in Real.arccos t..Real.pi,
        f (τ+δ*(Real.cos θ:ℂ))‖ := by
    simp [gapSidePrimitive]
    split <;> simp
  rw [hnorm]
  calc
    _ ≤ M * |Real.pi-Real.arccos t| := hi
    _ ≤ M * Real.pi := mul_le_mul_of_nonneg_left hangle hM
    _ = Real.pi * M := mul_comm _ _

theorem gapSidePrimitive_normalized_norm_le (τ δ : ℂ) (f : ℂ → ℂ) (t M : ℝ)
    (hM : 0 ≤ M)
    (hf : ∀ r ∈ Set.Icc (-1:ℝ) 1, ‖f (τ+δ*(r:ℂ))‖ ≤ M)
    (upper : Bool) :
    ‖gapSidePrimitive τ δ f t upper / (Real.pi:ℂ)‖ ≤ M := by
  have h := gapSidePrimitive_norm_le τ δ f t M hM hf upper
  have hπ : 0 < Real.pi := Real.pi_pos
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hπ, div_le_iff₀ hπ]
  simpa [mul_comm] using h

theorem upper_side_kernel_cos (δ : ℂ) (θ : ℝ) (hδ : δ ≠ 0)
    (hθ0 : 0 < θ) (hθπ : θ < Real.pi) :
    (δ * (Real.sin θ:ℂ)) /
      (-δ*I*(Real.sqrt (1-(Real.cos θ)^2):ℂ)) = I := by
  rw [← Real.sin_eq_sqrt_one_sub_cos_sq hθ0.le hθπ.le]
  have hs : (Real.sin θ:ℂ) ≠ 0 := by
    exact_mod_cast (Real.sin_pos_of_pos_of_lt_pi hθ0 hθπ).ne'
  field_simp [hδ, hs]
  norm_num

theorem lower_side_kernel_cos (δ : ℂ) (θ : ℝ) (hδ : δ ≠ 0)
    (hθ0 : 0 < θ) (hθπ : θ < Real.pi) :
    (δ * (Real.sin θ:ℂ)) /
      (δ*I*(Real.sqrt (1-(Real.cos θ)^2):ℂ)) = -I := by
  rw [← Real.sin_eq_sqrt_one_sub_cos_sq hθ0.le hθπ.le]
  have hs : (Real.sin θ:ℂ) ≠ 0 := by
    exact_mod_cast (Real.sin_pos_of_pos_of_lt_pi hθ0 hθπ).ne'
  field_simp [hδ, hs]
  norm_num

/-- The oriented side integral pulled back by `λ(θ) = τ + δ cos θ`. The
    numerator is the positive reversed-orientation Jacobian `δ sin θ`;
    the denominator is the upper or lower boundary value from (2.12).
    Endpoint values of the integrand are irrelevant to the integral. -/
def gapSideBoundaryIntegral (τ δ : ℂ) (f : ℂ → ℂ) (t : ℝ)
    (upper : Bool) : ℂ :=
  ∫ θ in Real.arccos t..Real.pi,
    f (τ+δ*(Real.cos θ:ℂ)) *
      ((δ*(Real.sin θ:ℂ)) /
        ((if upper then -δ*I else δ*I) *
          (Real.sqrt (1-(Real.cos θ)^2):ℂ)))

/-- Cancellation of the side-root boundary value against the cosine
    Jacobian gives the `±i` factor in the proof of Lemma 10.4. -/
theorem gapSideBoundaryIntegral_eq_primitive (τ δ : ℂ) (f : ℂ → ℂ)
    (t : ℝ) (hδ : δ ≠ 0) (upper : Bool) :
    gapSideBoundaryIntegral τ δ f t upper =
      gapSidePrimitive τ δ f t upper := by
  have hangle : Real.arccos t ≤ Real.pi := Real.arccos_le_pi t
  cases upper with
  | true =>
      have heq :
          (∫ θ in Real.arccos t..Real.pi,
            f (τ+δ*(Real.cos θ:ℂ)) *
              ((δ*(Real.sin θ:ℂ)) /
                (-δ*I*(Real.sqrt (1-(Real.cos θ)^2):ℂ)))) =
          ∫ θ in Real.arccos t..Real.pi, f (τ+δ*(Real.cos θ:ℂ)) * I := by
        apply intervalIntegral.integral_congr_Ioo_of_le hangle
        intro θ hθ
        have hθ0 : 0 < θ := lt_of_le_of_lt (Real.arccos_nonneg t) hθ.1
        dsimp only
        rw [upper_side_kernel_cos δ θ hδ hθ0 hθ.2]
      simp only [gapSideBoundaryIntegral, gapSidePrimitive, ite_true]
      rw [heq, intervalIntegral.integral_mul_const]
      ring
  | false =>
      have heq :
          (∫ θ in Real.arccos t..Real.pi,
            f (τ+δ*(Real.cos θ:ℂ)) *
              ((δ*(Real.sin θ:ℂ)) /
                (δ*I*(Real.sqrt (1-(Real.cos θ)^2):ℂ)))) =
          ∫ θ in Real.arccos t..Real.pi, f (τ+δ*(Real.cos θ:ℂ)) * (-I) := by
        apply intervalIntegral.integral_congr_Ioo_of_le hangle
        intro θ hθ
        have hθ0 : 0 < θ := lt_of_le_of_lt (Real.arccos_nonneg t) hθ.1
        dsimp only
        rw [lower_side_kernel_cos δ θ hδ hθ0 hθ.2]
      simp only [gapSideBoundaryIntegral, gapSidePrimitive, Bool.false_eq_true, ite_false]
      rw [heq, intervalIntegral.integral_mul_const]
      ring

/-- The normalized side integral is bounded by the maximum of `‖f‖` on
    the gap, uniformly in the endpoint and in the choice of side. -/
theorem gapSideBoundaryIntegral_uniform_max_bound (τ δ : ℂ) (f : ℂ → ℂ)
    (hδ : δ ≠ 0) (hf : ContinuousOn f (standardRootGapSegment τ δ)) :
    ∃ z ∈ standardRootGapSegment τ δ,
      (∀ w ∈ standardRootGapSegment τ δ, ‖f w‖ ≤ ‖f z‖) ∧
      ∀ (t : ℝ) (upper : Bool),
        ‖gapSideBoundaryIntegral τ δ f t upper / (Real.pi:ℂ)‖ ≤ ‖f z‖ := by
  have hne : (standardRootGapSegment τ δ).Nonempty := by
    refine ⟨τ, ?_⟩
    exact ⟨0, by norm_num, by simp⟩
  obtain ⟨z, hz, hmax⟩ :=
    (standardRootGapSegment_compact τ δ).exists_isMaxOn hne hf.norm
  refine ⟨z, hz, hmax, ?_⟩
  intro t upper
  rw [gapSideBoundaryIntegral_eq_primitive τ δ f t hδ upper]
  apply gapSidePrimitive_normalized_norm_le τ δ f t (‖f z‖) (norm_nonneg _) ?_ upper
  intro r hr
  exact hmax ⟨r, hr, rfl⟩

/-- The apparent endpoint singularities are removable almost everywhere;
    the side integrand is genuinely interval integrable for continuous `f`. -/
theorem gapSideBoundaryIntegrand_intervalIntegrable (τ δ : ℂ) (f : ℂ → ℂ)
    (hδ : δ ≠ 0) (hf : ContinuousOn f (standardRootGapSegment τ δ))
    (t : ℝ) (upper : Bool) :
    IntervalIntegrable
      (fun θ : ℝ => f (τ+δ*(Real.cos θ:ℂ)) *
        ((δ*(Real.sin θ:ℂ)) /
          ((if upper then -δ*I else δ*I) *
            (Real.sqrt (1-(Real.cos θ)^2):ℂ))))
      volume (Real.arccos t) Real.pi := by
  have hangle : Real.arccos t ≤ Real.pi := Real.arccos_le_pi t
  cases upper with
  | true =>
      have hbase := (gapSidePath_intervalIntegrable τ δ f hf t).mul_const I
      apply hbase.congr_uIoo
      intro θ hθ
      have hθ' : θ ∈ Set.Ioo (Real.arccos t) Real.pi := by
        simpa only [Set.uIoo_of_le hangle] using hθ
      have hθ0 : 0 < θ := lt_of_le_of_lt (Real.arccos_nonneg t) hθ'.1
      dsimp only
      simp only [ite_true]
      rw [upper_side_kernel_cos δ θ hδ hθ0 hθ'.2]
  | false =>
      have hbase := (gapSidePath_intervalIntegrable τ δ f hf t).mul_const (-I)
      apply hbase.congr_uIoo
      intro θ hθ
      have hθ' : θ ∈ Set.Ioo (Real.arccos t) Real.pi := by
        simpa only [Set.uIoo_of_le hangle] using hθ
      have hθ0 : 0 < θ := lt_of_le_of_lt (Real.arccos_nonneg t) hθ'.1
      dsimp only
      simp only [Bool.false_eq_true, ite_false]
      rw [lower_side_kernel_cos δ θ hδ hθ0 hθ'.2]

end NLS.ZakharovShabat
