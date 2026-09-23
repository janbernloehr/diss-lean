import NLS.ZakharovShabat.SourceStandardRootGapSideReal

/-!
# Standard-root boundary values along an arbitrary complex gap

The normalized root is equivariant under translation and nonzero
complex scaling of the gap. Applying this to the complete real-gap
formula gives equation (2.12) for every complex midpoint and nonzero
complex half-gap, including the midpoint and both endpoints.
-/

noncomputable section
open Complex Filter
open scoped Topology

namespace NLS.ZakharovShabat

/-- Affine scaling of the normalized root from the standard gap `[-1,1]`. -/
theorem normalizedStandardRoot_affine_scale (τ δ u : ℂ) (hδ : δ ≠ 0) :
    normalizedStandardRoot τ ((2*δ)^2) (τ+δ*u) =
      δ*normalizedStandardRoot 0 4 u := by
  by_cases hu : u = 0
  · subst u
    simp [normalizedStandardRoot]
  · unfold normalizedStandardRoot
    have hlin : τ-(τ+δ*u) = -δ*u := by ring
    rw [hlin]
    have hrad : 1-(2*δ)^2/(4*(-δ*u)^2) =
        1-4/(4*(0-u)^2) := by
      field_simp [hδ, hu]
      ring
    rw [hrad]
    ring

/-- Upper boundary value in equation (2.12) for a complex gap. -/
theorem normalizedStandardRoot_tendsto_gap_upper_complex (τ δ : ℂ) (t : ℝ)
    (hδ : δ ≠ 0) (htl : -1 ≤ t) (htr : t ≤ 1) :
    Tendsto (fun ε : ℝ => normalizedStandardRoot τ ((2*δ)^2)
      (τ+δ*((t:ℂ)+(ε:ℂ)*I))) (𝓝[>] (0:ℝ))
      (𝓝 (-δ*I*(Real.sqrt (1-t^2):ℂ))) := by
  have hreal := normalizedStandardRoot_tendsto_gap_upper_real 0 1 t
    (by norm_num) htl htr
  have hscaled := hreal.const_mul δ
  have hlim : Tendsto (fun ε : ℝ =>
      δ*normalizedStandardRoot 0 4 ((t:ℂ)+(ε:ℂ)*I))
      (𝓝[>] (0:ℝ)) (𝓝 (-δ*I*(Real.sqrt (1-t^2):ℂ))) := by
    convert hscaled using 1
    all_goals norm_num
    all_goals ring
  exact hlim.congr' (Filter.Eventually.of_forall fun ε =>
    (normalizedStandardRoot_affine_scale τ δ ((t:ℂ)+(ε:ℂ)*I) hδ).symm)

/-- Lower boundary value in equation (2.12) for a complex gap. -/
theorem normalizedStandardRoot_tendsto_gap_lower_complex (τ δ : ℂ) (t : ℝ)
    (hδ : δ ≠ 0) (htl : -1 ≤ t) (htr : t ≤ 1) :
    Tendsto (fun ε : ℝ => normalizedStandardRoot τ ((2*δ)^2)
      (τ+δ*((t:ℂ)-(ε:ℂ)*I))) (𝓝[>] (0:ℝ))
      (𝓝 (δ*I*(Real.sqrt (1-t^2):ℂ))) := by
  have hreal := normalizedStandardRoot_tendsto_gap_lower_real 0 1 t
    (by norm_num) htl htr
  have hscaled := hreal.const_mul δ
  have hlim : Tendsto (fun ε : ℝ =>
      δ*normalizedStandardRoot 0 4 ((t:ℂ)-(ε:ℂ)*I))
      (𝓝[>] (0:ℝ)) (𝓝 (δ*I*(Real.sqrt (1-t^2):ℂ))) := by
    convert hscaled using 1
    all_goals norm_num
    all_goals ring
  exact hlim.congr' (Filter.Eventually.of_forall fun ε =>
    (normalizedStandardRoot_affine_scale τ δ ((t:ℂ)-(ε:ℂ)*I) hδ).symm)

end NLS.ZakharovShabat
