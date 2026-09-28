import NLS.ZakharovShabat.SourcePsiLimitRegularFactor

/-!
# Uniform limit of the deleted-index ratio

The factor `π(n-m)/(πn-z)` tends to one uniformly on each fixed
free-centered disc as the deleted index escapes in either direction.
This is the elementary uniform estimate needed before passing the
selected-index integrands through a fixed contour integral.
-/

noncomputable section
open Filter Topology Complex Metric Set
namespace NLS.ZakharovShabat

/-- The error in the deleted-index ratio is the displacement from the
fixed free center divided by the distance to the omitted free center. -/
theorem sourcePsiDeletedIndexRatio_sub_one
    (n m : ℤ) (z : ℂ)
    (hden : (Real.pi : ℂ) * n - z ≠ 0) :
    sourcePsiDeletedIndexRatio n m z - 1 =
      (z - (Real.pi : ℂ) * m) / ((Real.pi : ℂ) * n - z) := by
  unfold sourcePsiDeletedIndexRatio
  have hnum : (Real.pi : ℂ) * ((n-m : ℤ) : ℂ) =
      (Real.pi : ℂ) * n - (Real.pi : ℂ) * m := by
    push_cast
    ring
  rw [hnum]
  field_simp [hden]
  ring

/-- The deleted-index ratio converges to one uniformly on any fixed
closed disc about the free center of the retained row. -/
theorem tendstoUniformlyOn_sourcePsiDeletedIndexRatio
    (m : ℤ) (R : ℝ) (hR : 0 ≤ R) :
    TendstoUniformlyOn (fun n : ℤ => sourcePsiDeletedIndexRatio n m)
      (fun _ : ℂ => (1 : ℂ))
      (Filter.comap Int.natAbs Filter.atTop)
      (closedBall ((Real.pi : ℂ) * m) R) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hfar := (tendsto_norm_freeCenter_sub_at_natAbs
    ((Real.pi : ℂ) * m)).eventually_ge_atTop (R + R / ε + 1)
  filter_upwards [hfar] with n hn z hz
  have hzR : ‖z - (Real.pi : ℂ) * m‖ ≤ R := by
    simpa only [mem_closedBall, dist_eq_norm] using hz
  have htri : ‖(Real.pi : ℂ) * n - (Real.pi : ℂ) * m‖ ≤
      ‖(Real.pi : ℂ) * n - z‖ + ‖z - (Real.pi : ℂ) * m‖ := by
    calc
      ‖(Real.pi : ℂ) * n - (Real.pi : ℂ) * m‖ =
          ‖((Real.pi : ℂ) * n - z) + (z - (Real.pi : ℂ) * m)‖ := by
            congr 1
            ring
      _ ≤ _ := norm_add_le _ _
  have hdenpos : 0 < ‖(Real.pi : ℂ) * n - z‖ := by
    nlinarith [div_nonneg hR (le_of_lt hε)]
  have hden : (Real.pi : ℂ) * n - z ≠ 0 :=
    norm_ne_zero_iff.mp (ne_of_gt hdenpos)
  rw [dist_eq_norm, norm_sub_rev, sourcePsiDeletedIndexRatio_sub_one n m z hden,
    norm_div]
  apply (div_lt_iff₀ hdenpos).2
  have hεid : ε * (R / ε) = R := by field_simp
  nlinarith

/-- For a fixed contour, sufficiently distant omitted free centers
lie away from every point of that contour, so the ratio is continuous
there. -/
theorem eventually_continuousOn_sourcePsiDeletedIndexRatio
    (m : ℤ) (R : ℝ) :
    ∀ᶠ n : ℤ in Filter.comap Int.natAbs Filter.atTop,
      ContinuousOn (sourcePsiDeletedIndexRatio n m)
        (sphere ((Real.pi : ℂ) * m) R) := by
  have hfar := (tendsto_norm_freeCenter_sub_at_natAbs
    ((Real.pi : ℂ) * m)).eventually_ge_atTop (R + 1)
  filter_upwards [hfar] with n hn
  have hden : ∀ z ∈ sphere ((Real.pi : ℂ) * m) R,
      (Real.pi : ℂ) * n - z ≠ 0 := by
    intro z hz
    have hzR : ‖z - (Real.pi : ℂ) * m‖ ≤ R := by
      simpa only [mem_sphere, dist_eq_norm] using le_of_eq hz
    have htri : ‖(Real.pi : ℂ) * n - (Real.pi : ℂ) * m‖ ≤
        ‖(Real.pi : ℂ) * n - z‖ + ‖z - (Real.pi : ℂ) * m‖ := by
      calc
        ‖(Real.pi : ℂ) * n - (Real.pi : ℂ) * m‖ =
            ‖((Real.pi : ℂ) * n - z) + (z - (Real.pi : ℂ) * m)‖ := by
              congr 1
              ring
        _ ≤ _ := norm_add_le _ _
    have hdenpos : 0 < ‖(Real.pi : ℂ) * n - z‖ := by linarith
    exact norm_ne_zero_iff.mp (ne_of_gt hdenpos)
  change ContinuousOn (fun z : ℂ =>
    ((Real.pi : ℂ) * ((n-m : ℤ) : ℂ)) / ((Real.pi : ℂ) * n-z)) _
  exact
    (continuousOn_const.div
      (continuousOn_const.sub continuousOn_id) hden)

/-- Uniform convergence of the elementary ratio passes through a
fixed free-centered contour integral. -/
theorem tendsto_circleIntegral_sourcePsiDeletedIndexRatio
    (m : ℤ) (R : ℝ) (hR : 0 ≤ R) :
    Tendsto (fun n : ℤ =>
      ∮ z in C((Real.pi : ℂ) * m, R), sourcePsiDeletedIndexRatio n m z)
      (Filter.comap Int.natAbs Filter.atTop)
      (𝓝 (∮ _z in C((Real.pi : ℂ) * m, R), (1 : ℂ))) := by
  exact ((tendstoUniformlyOn_sourcePsiDeletedIndexRatio m R hR).mono
    sphere_subset_closedBall).tendsto_circleIntegral_of_continuousOn hR
      (eventually_continuousOn_sourcePsiDeletedIndexRatio m R)

/-- The ratio also converges uniformly on a disc with an arbitrary
fixed center, since that disc lies in a larger free-centered disc. -/
theorem tendstoUniformlyOn_sourcePsiDeletedIndexRatio_anyDisc
    (m : ℤ) (c : ℂ) (R : ℝ) (hR : 0 ≤ R) :
    TendstoUniformlyOn (fun n : ℤ => sourcePsiDeletedIndexRatio n m)
      (fun _ : ℂ => (1 : ℂ))
      (Filter.comap Int.natAbs Filter.atTop)
      (closedBall c R) := by
  have hlarge : 0 ≤ R + dist c ((Real.pi : ℂ) * m) := by positivity
  exact (tendstoUniformlyOn_sourcePsiDeletedIndexRatio m
    (R + dist c ((Real.pi : ℂ) * m)) hlarge).mono
      (closedBall_subset_closedBall' le_rfl)

/-- On any fixed contour, sufficiently distant omitted free centers
avoid every point of the circle. -/
theorem eventually_continuousOn_sourcePsiDeletedIndexRatio_anyCircle
    (m : ℤ) (c : ℂ) (R : ℝ) :
    ∀ᶠ n : ℤ in Filter.comap Int.natAbs Filter.atTop,
      ContinuousOn (sourcePsiDeletedIndexRatio n m) (sphere c R) := by
  have hfar := (tendsto_norm_freeCenter_sub_at_natAbs c).eventually_ge_atTop
    (R + 1)
  filter_upwards [hfar] with n hn
  have hden : ∀ z ∈ sphere c R,
      (Real.pi : ℂ) * n - z ≠ 0 := by
    intro z hz
    have hzR : ‖z-c‖ ≤ R := by
      simpa only [mem_sphere, dist_eq_norm] using le_of_eq hz
    have htri : ‖(Real.pi : ℂ) * n-c‖ ≤
        ‖(Real.pi : ℂ) * n-z‖ + ‖z-c‖ := by
      calc
        ‖(Real.pi : ℂ) * n-c‖ =
            ‖((Real.pi : ℂ) * n-z)+(z-c)‖ := by
              congr 1
              ring
        _ ≤ _ := norm_add_le _ _
    have hdenpos : 0 < ‖(Real.pi : ℂ) * n-z‖ := by linarith
    exact norm_ne_zero_iff.mp (ne_of_gt hdenpos)
  change ContinuousOn (fun z : ℂ =>
    ((Real.pi : ℂ) * ((n-m : ℤ) : ℂ)) / ((Real.pi : ℂ) * n-z)) _
  exact continuousOn_const.div
    (continuousOn_const.sub continuousOn_id) hden

end NLS.ZakharovShabat
