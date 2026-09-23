import NLS.ZakharovShabat.SourceStandardRootGapSideNegative

/-!
# Standard-root boundary values at the midpoint of a real gap

The radicand in the normalized formula diverges at the midpoint as
the transverse offset tends to zero. For a positive real half-gap,
its product with the vanishing linear factor simplifies to a continuous
real square-root expression. Reflection yields the opposite side.
-/

noncomputable section
open Complex Filter ComplexOrder
open scoped Topology

namespace NLS.ZakharovShabat

/-- Explicit standard-root value directly above the midpoint. -/
theorem normalizedStandardRoot_gap_midpoint_upper_value (τ : ℂ) (d ε : ℝ)
    (hd : 0 < d) (hε : 0 < ε) :
    normalizedStandardRoot τ ((2*(d:ℂ))^2)
      (τ+(d:ℂ)*((ε:ℂ)*I)) =
      -(d:ℂ)*I*(Real.sqrt (1+ε^2):ℂ) := by
  unfold normalizedStandardRoot
  have hdC : (d:ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hd
  have hεC : (ε:ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hε
  have hrad : 1-(2*(d:ℂ))^2/(4*(τ-(τ+(d:ℂ)*((ε:ℂ)*I)))^2) =
      ((1+ε⁻¹^2:ℝ):ℂ) := by
    have hlin : τ-(τ+(d:ℂ)*((ε:ℂ)*I)) = -(d:ℂ)*((ε:ℂ)*I) := by ring
    rw [hlin]
    push_cast
    have hi : I^2 = (-1:ℂ) := by simp
    field_simp [hdC, hεC, hi]
    rw [hi]
    ring
  have hnonneg : 0 ≤ ((1+ε⁻¹^2:ℝ):ℂ) := by
    exact_mod_cast (by positivity : 0 ≤ (1+ε⁻¹^2:ℝ))
  rw [hrad, Complex.sqrt_of_nonneg hnonneg]
  simp only [Complex.ofReal_re]
  have hsqrt : ε*Real.sqrt (1+ε⁻¹^2) = Real.sqrt (1+ε^2) := by
    have heq : 1+ε⁻¹^2 = (1+ε^2)/ε^2 := by
      field_simp
      ring
    rw [heq, Real.sqrt_div' _ (sq_nonneg ε), Real.sqrt_sq hε.le]
    field_simp
  rw [← hsqrt]
  push_cast
  ring

/-- Upper midpoint limit in equation (2.12) for a positive real gap. -/
theorem normalizedStandardRoot_tendsto_gap_upper_zero (τ : ℂ) (d : ℝ) (hd : 0 < d) :
    Tendsto (fun ε : ℝ =>
      normalizedStandardRoot τ ((2*(d:ℂ))^2)
        (τ+(d:ℂ)*((ε:ℂ)*I)))
      (𝓝[>] (0:ℝ)) (𝓝 (-(d:ℂ)*I)) := by
  have hc : ContinuousAt (fun ε : ℝ =>
      -(d:ℂ)*I*(Real.sqrt (1+ε^2):ℂ)) 0 := by fun_prop
  have hlim : Tendsto (fun ε : ℝ =>
      -(d:ℂ)*I*(Real.sqrt (1+ε^2):ℂ)) (𝓝[>] (0:ℝ))
      (𝓝 (-(d:ℂ)*I)) := by
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (normalizedStandardRoot_gap_midpoint_upper_value τ d ε hd hε).symm

/-- Lower midpoint limit in equation (2.12) for a positive real gap. -/
theorem normalizedStandardRoot_tendsto_gap_lower_zero (τ : ℂ) (d : ℝ) (hd : 0 < d) :
    Tendsto (fun ε : ℝ =>
      normalizedStandardRoot τ ((2*(d:ℂ))^2)
        (τ-(d:ℂ)*((ε:ℂ)*I)))
      (𝓝[>] (0:ℝ)) (𝓝 ((d:ℂ)*I)) := by
  have h := (normalizedStandardRoot_tendsto_gap_upper_zero τ d hd).neg
  have heq : (fun ε : ℝ =>
      normalizedStandardRoot τ ((2*(d:ℂ))^2)
        (τ-(d:ℂ)*((ε:ℂ)*I))) =
      (fun ε : ℝ =>
        -normalizedStandardRoot τ ((2*(d:ℂ))^2)
          (τ+(d:ℂ)*((ε:ℂ)*I))) := by
    funext ε
    have hz : τ-(d:ℂ)*((ε:ℂ)*I) =
        2*τ-(τ+(d:ℂ)*((ε:ℂ)*I)) := by ring
    rw [hz, normalizedStandardRoot_reflect]
  rw [heq]
  simpa only [neg_mul, neg_neg] using h

end NLS.ZakharovShabat
