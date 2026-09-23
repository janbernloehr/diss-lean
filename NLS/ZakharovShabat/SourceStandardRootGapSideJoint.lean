/- Joint one-sided gap limits for the normalized standard root. The spectral
   parameter can approach a gap point from anywhere in the corresponding open
   side, including while its longitudinal coordinate varies. -/
import NLS.ZakharovShabat.SourceStandardRootGapSideSource
import NLS.ZakharovShabat.SourceStandardRootAnalytic
import Mathlib.Topology.Algebra.Field

noncomputable section
open Complex Filter Set ComplexOrder
open scoped Topology

namespace NLS.ZakharovShabat

private def upper : Set ℂ := {z | 0 < z.im}

private theorem upper_preconnected : IsPreconnected upper := by
  have h : Convex ℝ upper := by
    intro x hx y hy a b ha hb hab
    change 0 < (a • x + b • y).im
    change 0 < x.im at hx
    change 0 < y.im at hy
    simp only [Complex.add_im]
    simp only [Complex.real_smul, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero]
    by_cases ha0 : a = 0
    · subst a
      have hb1 : b = 1 := by linarith
      simp [hb1, hy]
    · have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
      have hax : 0 < a*x.im := mul_pos ha' hx
      have hby : 0 ≤ b*y.im := mul_nonneg hb hy.le
      linarith
  exact h.isPreconnected

private theorem not_mem_segment (u : ℂ) (hu : u ∈ upper) :
    u ∉ segment ℝ (-1:ℂ) 1 := by
  intro hs
  rcases hs with ⟨a,b,ha,hb,hab,heq⟩
  have him : u.im = 0 := by
    rw [← heq]
    simp
  exact (ne_of_gt hu) him

private theorem root_continuous_upper (u : ℂ) (hu : u ∈ upper) :
    ContinuousAt (normalizedStandardRoot 0 4) u := by
  have hs := NLS.ComplexAnalysis.gap_radicand_mem_slitPlane
    (-1:ℂ) 1 u (not_mem_segment u hu)
  have hrad : 1-4/(4*(0-u)^2) ∈ Complex.slitPlane := by
    convert hs using 1
    all_goals norm_num
  have hne : (0:ℂ) ≠ u := by
    intro he
    have : u.im = 0 := by simp [← he]
    exact (ne_of_gt hu) this
  exact (normalizedStandardRoot_analyticAt_of_slit 0 4 u hne hrad).continuousAt

private theorem candidate_slit (u : ℂ) (hu : u ∈ upper) :
    1-u^2 ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  by_cases hre : u.re = 0
  · left
    have h : (1-u^2).re = 1+u.im^2 := by
      simp [Complex.sub_re, Complex.mul_re, pow_two, hre]
    rw [h]
    positivity
  · right
    have h : (1-u^2).im = -2*u.re*u.im := by
      simp [Complex.sub_im, Complex.mul_im, pow_two]
      ring
    rw [h]
    exact mul_ne_zero (mul_ne_zero (by norm_num) hre) (ne_of_gt hu)

private theorem candidate_continuous_upper (u : ℂ) (hu : u ∈ upper) :
    ContinuousAt (fun z : ℂ => -I*Complex.sqrt (1-z^2)) u := by
  have hs : ContinuousAt Complex.sqrt (1-u^2) :=
    Complex.continuousAt_sqrt ((Complex.mem_slitPlane_iff.mp (candidate_slit u hu)).imp le_of_lt id)
  have hrad : ContinuousAt (fun z : ℂ => 1-z^2) u := by fun_prop
  have hscomp : ContinuousAt (fun z : ℂ => Complex.sqrt (1-z^2)) u := by
    have htmp := ContinuousAt.comp (f := fun z : ℂ => 1-z^2)
      (g := Complex.sqrt) hs hrad
    simpa only [Function.comp_def] using htmp
  exact continuousAt_const.mul hscomp

private theorem sqrt_sq_complex (z : ℂ) : Complex.sqrt z ^ 2 = z := by
  have h := Complex.cpow_nat_inv_pow z (Nat.succ_ne_zero 1)
  norm_num at h
  simpa [Complex.sqrt] using h

private theorem root_candidate_sq (u : ℂ) (hu : u ∈ upper) :
    normalizedStandardRoot 0 4 u ^ 2 =
      (-I*Complex.sqrt (1-u^2))^2 := by
  have hu0 : u ≠ 0 := by
    intro he
    have : (0:ℝ) < 0 := by simpa [upper, he] using hu
    exact (lt_irrefl 0) this
  have hf : normalizedStandardRoot 0 4 u ^ 2 = u^2-1 := by
    rw [normalizedStandardRoot_sq 0 4 u hu0.symm]
    norm_num
  have hg : (-I*Complex.sqrt (1-u^2))^2 = u^2-1 := by
    rw [mul_pow, sqrt_sq_complex]
    simp
  rw [hf, hg]

private theorem candidate_ne_zero (u : ℂ) (hu : u ∈ upper) :
    -I*Complex.sqrt (1-u^2) ≠ 0 := by
  have hs : u^2 ≠ 1 := by
    intro he
    rcases sq_eq_one_iff.mp he with h | h
    · have : (0:ℝ) < 0 := by simpa [upper, h] using hu
      exact (lt_irrefl 0) this
    · have : (0:ℝ) < 0 := by simpa [upper, h] using hu
      exact (lt_irrefl 0) this
  have hrad : 1-u^2 ≠ 0 := sub_ne_zero.mpr hs.symm
  have hsqrt : Complex.sqrt (1-u^2) ≠ 0 := by
    intro he
    have hsq := sqrt_sq_complex (1-u^2)
    rw [he] at hsq
    have hz : 1-u^2=0 := by simpa using hsq.symm
    exact hrad hz
  exact mul_ne_zero (by simp) hsqrt

private theorem root_anchor :
    normalizedStandardRoot 0 4 I = -I*Complex.sqrt (1-I^2) := by
  have h := normalizedStandardRoot_gap_midpoint_upper_value
    (0:ℂ) 1 1 (by norm_num) (by norm_num)
  simp only [ofReal_one, one_mul, zero_add] at h
  have hs : Complex.sqrt (1-I^2) = (Real.sqrt 2 : ℂ) := by
    have he : 1-I^2 = (2:ℂ) := by norm_num
    rw [he, Complex.sqrt_of_nonneg (by norm_num : (0:ℂ) ≤ 2)]
    simp
  norm_num at h
  rw [hs]
  simpa using h

private theorem root_eq_candidate_upper (u : ℂ) (hu : u ∈ upper) :
    normalizedStandardRoot 0 4 u = -I*Complex.sqrt (1-u^2) := by
  have hf : ContinuousOn (normalizedStandardRoot 0 4) upper :=
    fun z hz => (root_continuous_upper z hz).continuousWithinAt
  have hg : ContinuousOn (fun z : ℂ => -I*Complex.sqrt (1-z^2)) upper :=
    fun z hz => (candidate_continuous_upper z hz).continuousWithinAt
  have hsq : EqOn ((normalizedStandardRoot 0 4)^2)
      ((fun z : ℂ => -I*Complex.sqrt (1-z^2))^2) upper :=
    fun z hz => root_candidate_sq z hz
  have hne : ∀ {z : ℂ}, z ∈ upper → -I*Complex.sqrt (1-z^2) ≠ 0 :=
    fun {z} hz => candidate_ne_zero z hz
  exact upper_preconnected.eq_of_sq_eq hf hg hsq hne
    (by simp [upper]) root_anchor hu

private theorem root_eq_candidate_lower (u : ℂ) (hu : u.im < 0) :
    normalizedStandardRoot 0 4 u = I*Complex.sqrt (1-u^2) := by
  have hupper : -u ∈ upper := by simpa [upper] using hu
  have h := root_eq_candidate_upper (-u) hupper
  have href : normalizedStandardRoot 0 4 (-u) =
      -normalizedStandardRoot 0 4 u := by
    simpa using normalizedStandardRoot_reflect 0 4 u
  calc
    normalizedStandardRoot 0 4 u = -normalizedStandardRoot 0 4 (-u) := by
      rw [href]
      simp
    _ = I*Complex.sqrt (1-u^2) := by
      rw [h]
      simp

private theorem candidate_continuous_at_gap (t : ℝ)
    (htl : -1 ≤ t) (htr : t ≤ 1) :
    ContinuousAt (fun z : ℂ => Complex.sqrt (1-z^2)) (t:ℂ) := by
  have hnonneg : 0 ≤ 1-t^2 := by nlinarith
  have hpowre : ((t:ℂ)^2).re = t^2 := by
    simp [pow_two, Complex.mul_re]
  have hrad_re : 0 ≤ (1-(t:ℂ)^2).re := by
    rw [Complex.sub_re, Complex.one_re, hpowre]
    exact hnonneg
  have hs : ContinuousAt Complex.sqrt (1-(t:ℂ)^2) :=
    Complex.continuousAt_sqrt (Or.inl hrad_re)
  have hrad : ContinuousAt (fun z : ℂ => 1-z^2) (t:ℂ) := by fun_prop
  have htmp := ContinuousAt.comp (f := fun z : ℂ => 1-z^2)
    (g := Complex.sqrt) hs hrad
  simpa only [Function.comp_def] using htmp

private theorem candidate_gap_value (t : ℝ)
    (htl : -1 ≤ t) (htr : t ≤ 1) :
    Complex.sqrt (1-(t:ℂ)^2) = (Real.sqrt (1-t^2):ℂ) := by
  have hnonneg : 0 ≤ 1-t^2 := by nlinarith
  have hpowre : ((t:ℂ)^2).re = t^2 := by
    simp [pow_two, Complex.mul_re]
  have hnonnegC : (0:ℂ) ≤ 1-(t:ℂ)^2 := by
    exact_mod_cast hnonneg
  rw [Complex.sqrt_of_nonneg hnonnegC]
  rw [Complex.sub_re, Complex.one_re, hpowre]

private theorem root_joint_upper (t : ℝ)
    (htl : -1 ≤ t) (htr : t ≤ 1) :
    Tendsto (normalizedStandardRoot 0 4)
      (𝓝[upper] (t:ℂ))
      (𝓝 (-I*(Real.sqrt (1-t^2):ℂ))) := by
  have hc : ContinuousAt (fun z : ℂ => -I*Complex.sqrt (1-z^2)) (t:ℂ) :=
    continuousAt_const.mul (candidate_continuous_at_gap t htl htr)
  have hv : -I*Complex.sqrt (1-(t:ℂ)^2) =
      -I*(Real.sqrt (1-t^2):ℂ) := by rw [candidate_gap_value t htl htr]
  rw [← hv]
  apply (hc.tendsto.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin] with u hu
  exact (root_eq_candidate_upper u hu).symm

private theorem root_joint_lower (t : ℝ)
    (htl : -1 ≤ t) (htr : t ≤ 1) :
    Tendsto (normalizedStandardRoot 0 4)
      (𝓝[{z : ℂ | z.im < 0}] (t:ℂ))
      (𝓝 (I*(Real.sqrt (1-t^2):ℂ))) := by
  have hc : ContinuousAt (fun z : ℂ => I*Complex.sqrt (1-z^2)) (t:ℂ) :=
    continuousAt_const.mul (candidate_continuous_at_gap t htl htr)
  have hv : I*Complex.sqrt (1-(t:ℂ)^2) =
      I*(Real.sqrt (1-t^2):ℂ) := by rw [candidate_gap_value t htl htr]
  rw [← hv]
  apply (hc.tendsto.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin] with u hu
  exact (root_eq_candidate_lower u hu).symm

private theorem root_joint_upper_complex (τ δ : ℂ) (t : ℝ)
    (hδ : δ ≠ 0) (htl : -1 ≤ t) (htr : t ≤ 1) :
    Tendsto (fun u : ℂ => normalizedStandardRoot τ ((2*δ)^2) (τ+δ*u))
      (𝓝[upper] (t:ℂ))
      (𝓝 (-δ*I*(Real.sqrt (1-t^2):ℂ))) := by
  have h := (root_joint_upper t htl htr).const_mul δ
  have hlim : Tendsto (fun u : ℂ => δ*normalizedStandardRoot 0 4 u)
      (𝓝[upper] (t:ℂ))
      (𝓝 (-δ*I*(Real.sqrt (1-t^2):ℂ))) := by
    convert h using 1
    all_goals ring
  exact hlim.congr' (Filter.Eventually.of_forall fun u =>
    (normalizedStandardRoot_affine_scale τ δ u hδ).symm)

private theorem root_joint_lower_complex (τ δ : ℂ) (t : ℝ)
    (hδ : δ ≠ 0) (htl : -1 ≤ t) (htr : t ≤ 1) :
    Tendsto (fun u : ℂ => normalizedStandardRoot τ ((2*δ)^2) (τ+δ*u))
      (𝓝[{z : ℂ | z.im < 0}] (t:ℂ))
      (𝓝 (δ*I*(Real.sqrt (1-t^2):ℂ))) := by
  have h := (root_joint_lower t htl htr).const_mul δ
  have hlim : Tendsto (fun u : ℂ => δ*normalizedStandardRoot 0 4 u)
      (𝓝[{z : ℂ | z.im < 0}] (t:ℂ))
      (𝓝 (δ*I*(Real.sqrt (1-t^2):ℂ))) := by
    convert h using 1
    all_goals ring
  exact hlim.congr' (Filter.Eventually.of_forall fun u =>
    (normalizedStandardRoot_affine_scale τ δ u hδ).symm)

/-- The open upper side of the oriented gap with midpoint `τ` and half-gap `δ`. -/
def standardRootGapUpperSide (τ δ : ℂ) : Set ℂ :=
  {z | 0 < ((z-τ)/δ).im}

/-- The open lower side of the oriented gap with midpoint `τ` and half-gap `δ`. -/
def standardRootGapLowerSide (τ δ : ℂ) : Set ℂ :=
  {z | ((z-τ)/δ).im < 0}

private theorem coord_tendsto_upper (τ δ : ℂ) (t : ℝ) (hδ : δ ≠ 0) :
    Tendsto (fun z : ℂ => (z-τ)/δ)
      (𝓝[standardRootGapUpperSide τ δ] (τ+δ*(t:ℂ)))
      (𝓝[upper] (t:ℂ)) := by
  have hval : ((τ+δ*(t:ℂ))-τ)/δ = (t:ℂ) := by
    field_simp [hδ]
    ring
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have hc : ContinuousAt (fun z : ℂ => (z-τ)/δ) (τ+δ*(t:ℂ)) := by
      fun_prop (disch := exact hδ)
    simpa only [hval] using hc.tendsto.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with z hz
    exact hz

private theorem coord_tendsto_lower (τ δ : ℂ) (t : ℝ) (hδ : δ ≠ 0) :
    Tendsto (fun z : ℂ => (z-τ)/δ)
      (𝓝[standardRootGapLowerSide τ δ] (τ+δ*(t:ℂ)))
      (𝓝[{z : ℂ | z.im < 0}] (t:ℂ)) := by
  have hval : ((τ+δ*(t:ℂ))-τ)/δ = (t:ℂ) := by
    field_simp [hδ]
    ring
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have hc : ContinuousAt (fun z : ℂ => (z-τ)/δ) (τ+δ*(t:ℂ)) := by
      fun_prop (disch := exact hδ)
    simpa only [hval] using hc.tendsto.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with z hz
    exact hz

/-- The standard root has the upper boundary value (2.12) under an arbitrary
    approach through the upper side, including at the gap endpoints. -/
theorem normalizedStandardRoot_tendsto_gap_upper_side (τ δ : ℂ) (t : ℝ)
    (hδ : δ ≠ 0) (htl : -1 ≤ t) (htr : t ≤ 1) :
    Tendsto (normalizedStandardRoot τ ((2*δ)^2))
      (𝓝[standardRootGapUpperSide τ δ] (τ+δ*(t:ℂ)))
      (𝓝 (-δ*I*(Real.sqrt (1-t^2):ℂ))) := by
  have h := (root_joint_upper_complex τ δ t hδ htl htr).comp
    (coord_tendsto_upper τ δ t hδ)
  have hpoint (z : ℂ) : τ+δ*((z-τ)/δ) = z := by
    field_simp [hδ]
    ring
  simpa only [Function.comp_def, hpoint] using h

/-- The standard root has the lower boundary value (2.12) under an arbitrary
    approach through the lower side, including at the gap endpoints. -/
theorem normalizedStandardRoot_tendsto_gap_lower_side (τ δ : ℂ) (t : ℝ)
    (hδ : δ ≠ 0) (htl : -1 ≤ t) (htr : t ≤ 1) :
    Tendsto (normalizedStandardRoot τ ((2*δ)^2))
      (𝓝[standardRootGapLowerSide τ δ] (τ+δ*(t:ℂ)))
      (𝓝 (δ*I*(Real.sqrt (1-t^2):ℂ))) := by
  have h := (root_joint_lower_complex τ δ t hδ htl htr).comp
    (coord_tendsto_lower τ δ t hδ)
  have hpoint (z : ℂ) : τ+δ*((z-τ)/δ) = z := by
    field_simp [hδ]
    ring
  simpa only [Function.comp_def, hpoint] using h

end NLS.ZakharovShabat
