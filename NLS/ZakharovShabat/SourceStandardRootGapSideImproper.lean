import NLS.ZakharovShabat.SourceStandardRootGapSideIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/- The side integral of Lemma 10.4 in the linear gap parameter. The endpoint
   weight is integrable, and the resulting path integral is the limit of
   integrals with the singular endpoints omitted. -/

noncomputable section
open Complex Filter MeasureTheory intervalIntegral
open scoped Topology

namespace NLS.ZakharovShabat

private theorem integral_cos_subst (g : ℝ → ℂ) (t : ℝ)
    (htl : -1 ≤ t) (htr : t ≤ 1) :
    (∫ r in (-1:ℝ)..t, g r) =
      ∫ θ in Real.arccos t..Real.pi, (Real.sin θ) • g (Real.cos θ) := by
  have hangle : Real.arccos t ≤ Real.pi := Real.arccos_le_pi t
  have hcont : ContinuousOn Real.cos (Set.uIcc (Real.arccos t) Real.pi) :=
    Real.continuous_cos.continuousOn
  have hderiv : ∀ x ∈ Set.Ioo (min (Real.arccos t) Real.pi)
      (max (Real.arccos t) Real.pi),
      HasDerivAt Real.cos (-Real.sin x) x := by
    intro x hx
    exact Real.hasDerivAt_cos x
  have hnonpos : ∀ x ∈ Set.Ioo (min (Real.arccos t) Real.pi)
      (max (Real.arccos t) Real.pi), -Real.sin x ≤ 0 := by
    intro x hx
    rw [min_eq_left hangle, max_eq_right hangle] at hx
    have hx0 : 0 ≤ x := (Real.arccos_nonneg t).trans hx.1.le
    exact neg_nonpos.mpr (Real.sin_nonneg_of_nonneg_of_le_pi hx0 hx.2.le)
  have hsub := intervalIntegral.integral_deriv_smul_comp_of_deriv_nonpos
    (a := Real.arccos t) (b := Real.pi) (f := Real.cos)
    (f' := fun x => -Real.sin x) (g := g) hcont hderiv hnonpos
  rw [Real.cos_arccos htl htr, Real.cos_pi] at hsub
  calc
    (∫ r in (-1:ℝ)..t, g r) = -(∫ r in t..(-1:ℝ), g r) := by
      rw [intervalIntegral.integral_symm]
    _ = -(∫ θ in Real.arccos t..Real.pi,
        (-Real.sin θ) • g (Real.cos θ)) := by
      simpa only [Function.comp_def] using
        congrArg (fun z : ℂ => -z) hsub.symm
    _ = ∫ θ in Real.arccos t..Real.pi,
        (Real.sin θ) • g (Real.cos θ) := by
      rw [← intervalIntegral.integral_neg]
      congr 1
      funext θ
      simp

/-- Substitution `r = cos θ` turns the inverse-square-root weighted gap
    integral into an ordinary cosine-parameter integral. -/
theorem gap_weighted_integral_eq_cos (τ δ : ℂ) (f : ℂ → ℂ) (t : ℝ)
    (htl : -1 ≤ t) (htr : t ≤ 1) :
    (∫ r in (-1:ℝ)..t,
      f (τ+δ*(r:ℂ)) / (Real.sqrt (1-r^2):ℂ)) =
    ∫ θ in Real.arccos t..Real.pi,
      f (τ+δ*(Real.cos θ:ℂ)) := by
  rw [integral_cos_subst
    (fun r : ℝ => f (τ+δ*(r:ℂ)) / (Real.sqrt (1-r^2):ℂ))
    t htl htr]
  apply intervalIntegral.integral_congr_Ioo_of_le (Real.arccos_le_pi t)
  intro θ hθ
  dsimp only
  have hθ0 : 0 < θ := lt_of_le_of_lt (Real.arccos_nonneg t) hθ.1
  have hsqrt : Real.sqrt (1-(Real.cos θ)^2) = Real.sin θ :=
    (Real.sin_eq_sqrt_one_sub_cos_sq hθ0.le hθ.2.le).symm
  rw [hsqrt]
  have hsin : (Real.sin θ:ℂ) ≠ 0 := by
    exact_mod_cast (Real.sin_pos_of_pos_of_lt_pi hθ0 hθ.2).ne'
  change (Real.sin θ:ℂ) *
    (f (τ+δ*(Real.cos θ:ℂ)) / (Real.sin θ:ℂ)) =
    f (τ+δ*(Real.cos θ:ℂ))
  field_simp [hsin]

/-- Continuous data on the gap make the singular-looking weighted
    integrand genuinely interval integrable, including at both endpoints. -/
theorem gap_weighted_intervalIntegrable (τ δ : ℂ) (f : ℂ → ℂ)
    (hf : ContinuousOn f (standardRootGapSegment τ δ)) (t : ℝ)
    (htl : -1 ≤ t) (htr : t ≤ 1) :
    IntervalIntegrable (fun r : ℝ =>
      f (τ+δ*(r:ℂ)) / (Real.sqrt (1-r^2):ℂ))
      volume (-1) t := by
  let g : ℝ → ℂ := fun r => f (τ+δ*(r:ℂ)) / (Real.sqrt (1-r^2):ℂ)
  have hangle : Real.arccos t ≤ Real.pi := Real.arccos_le_pi t
  have hcont : ContinuousOn Real.cos (Set.uIcc (Real.arccos t) Real.pi) :=
    Real.continuous_cos.continuousOn
  have hderiv : ∀ x ∈ Set.Ioo (min (Real.arccos t) Real.pi)
      (max (Real.arccos t) Real.pi),
      HasDerivAt Real.cos (-Real.sin x) x := by
    intro x hx
    exact Real.hasDerivAt_cos x
  have hnonpos : ∀ x ∈ Set.Ioo (min (Real.arccos t) Real.pi)
      (max (Real.arccos t) Real.pi), -Real.sin x ≤ 0 := by
    intro x hx
    rw [min_eq_left hangle, max_eq_right hangle] at hx
    have hx0 : 0 ≤ x := (Real.arccos_nonneg t).trans hx.1.le
    exact neg_nonpos.mpr (Real.sin_nonneg_of_nonneg_of_le_pi hx0 hx.2.le)
  have hiff := intervalIntegral.integrable_deriv_smul_comp_iff_of_deriv_nonpos
    (a := Real.arccos t) (b := Real.pi) (f := Real.cos)
    (f' := fun x => -Real.sin x) (g := g) hcont hderiv hnonpos
  rw [Real.cos_arccos htl htr, Real.cos_pi] at hiff
  have hfi := (gapSidePath_intervalIntegrable τ δ f hf t).neg
  have hleft : IntervalIntegrable
      (fun θ => (-Real.sin θ) • g (Real.cos θ)) volume (Real.arccos t) Real.pi := by
    apply hfi.congr_uIoo
    intro θ hθ
    have hθ' : θ ∈ Set.Ioo (Real.arccos t) Real.pi := by
      simpa only [Set.uIoo_of_le hangle] using hθ
    have hθ0 : 0 < θ := lt_of_le_of_lt (Real.arccos_nonneg t) hθ'.1
    have hsqrt : Real.sqrt (1-(Real.cos θ)^2) = Real.sin θ :=
      (Real.sin_eq_sqrt_one_sub_cos_sq hθ0.le hθ'.2.le).symm
    have hsin : (Real.sin θ:ℂ) ≠ 0 := by
      exact_mod_cast (Real.sin_pos_of_pos_of_lt_pi hθ0 hθ'.2).ne'
    dsimp only [g, Function.comp_def]
    rw [hsqrt]
    simp only [Pi.neg_apply, Complex.real_smul, Complex.ofReal_neg]
    change -(f (τ+δ*(Real.cos θ:ℂ))) =
      (-Real.sin θ:ℂ) *
        (f (τ+δ*(Real.cos θ:ℂ)) / (Real.sin θ:ℂ))
    field_simp [hsin]
  have hright := hiff.mp hleft
  exact hright.symm

/-- The signed weighted integral appearing explicitly in (2.12) and the
    proof of Lemma 10.4. -/
def gapSideWeightedIntegral (τ δ : ℂ) (f : ℂ → ℂ) (t : ℝ)
    (upper : Bool) : ℂ :=
  (if upper then I else -I) *
    ∫ r in (-1:ℝ)..t,
      f (τ+δ*(r:ℂ)) / (Real.sqrt (1-r^2):ℂ)

/-- The weighted `r`-integral equals the cosine-pulled boundary integral. -/
theorem gapSideWeightedIntegral_eq_boundary (τ δ : ℂ) (f : ℂ → ℂ)
    (t : ℝ) (hδ : δ ≠ 0) (htl : -1 ≤ t) (htr : t ≤ 1)
    (upper : Bool) :
    gapSideWeightedIntegral τ δ f t upper =
      gapSideBoundaryIntegral τ δ f t upper := by
  rw [gapSideBoundaryIntegral_eq_primitive τ δ f t hδ upper]
  unfold gapSideWeightedIntegral gapSidePrimitive
  rw [gap_weighted_integral_eq_cos τ δ f t htl htr]

/-- Lemma 10.4's maximum bound for the weighted integral, uniformly in
    the stopping point and the chosen side. -/
theorem gapSideWeightedIntegral_uniform_max_bound (τ δ : ℂ) (f : ℂ → ℂ)
    (hδ : δ ≠ 0) (hf : ContinuousOn f (standardRootGapSegment τ δ)) :
    ∃ z ∈ standardRootGapSegment τ δ,
      (∀ w ∈ standardRootGapSegment τ δ, ‖f w‖ ≤ ‖f z‖) ∧
      ∀ (t : ℝ), -1 ≤ t → t ≤ 1 → ∀ (upper : Bool),
        ‖gapSideWeightedIntegral τ δ f t upper / (Real.pi:ℂ)‖ ≤ ‖f z‖ := by
  obtain ⟨z,hz,hmax,hbound⟩ :=
    gapSideBoundaryIntegral_uniform_max_bound τ δ f hδ hf
  refine ⟨z,hz,hmax,?_⟩
  intro t htl htr upper
  rw [gapSideWeightedIntegral_eq_boundary τ δ f t hδ htl htr upper]
  exact hbound t upper

private theorem gapSideCosIntegral_continuous_lower (τ δ : ℂ) (f : ℂ → ℂ)
    (hf : ContinuousOn f (standardRootGapSegment τ δ)) :
    Continuous (fun a : ℝ =>
      ∫ θ in a..Real.pi, f (τ+δ*(Real.cos θ:ℂ))) := by
  have hpath := gapSidePath_continuous τ δ f hf
  have hbase : Continuous (fun a : ℝ =>
      ∫ θ in Real.pi..a, f (τ+δ*(Real.cos θ:ℂ))) :=
    intervalIntegral.continuous_primitive
      (fun a b => hpath.intervalIntegrable a b) Real.pi
  have hneg := hbase.neg
  convert hneg using 1
  ext a
  rw [intervalIntegral.integral_symm]
  rfl

private theorem gapSideWeighted_small_tendsto_zero (τ δ : ℂ) (f : ℂ → ℂ)
    (hf : ContinuousOn f (standardRootGapSegment τ δ)) :
    Filter.Tendsto
      (fun ε : ℝ => ∫ r in (-1:ℝ)..(-1+ε),
        f (τ+δ*(r:ℂ)) / (Real.sqrt (1-r^2):ℂ))
      (𝓝[>] (0:ℝ)) (𝓝 (0:ℂ)) := by
  have hε : Filter.Tendsto (fun ε : ℝ => (-1:ℝ)+ε)
      (𝓝[>] (0:ℝ)) (𝓝 (-1:ℝ)) := by
    have hid : Tendsto (fun ε : ℝ => ε) (𝓝[>] (0:ℝ)) (𝓝 (0:ℝ)) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    simpa using (tendsto_const_nhds.add hid)
  have ha : Filter.Tendsto (fun ε : ℝ => Real.arccos (-1+ε))
      (𝓝[>] (0:ℝ)) (𝓝 Real.pi) := by
    have h := (Real.continuous_arccos.tendsto (-1:ℝ)).comp hε
    simpa only [Function.comp_def, Real.arccos_neg_one] using h
  have hc := (gapSideCosIntegral_continuous_lower τ δ f hf).tendsto Real.pi
  have hlim : Filter.Tendsto (fun ε : ℝ =>
      ∫ θ in Real.arccos (-1+ε)..Real.pi,
        f (τ+δ*(Real.cos θ:ℂ)))
      (𝓝[>] (0:ℝ)) (𝓝 (0:ℂ)) := by
    simpa only [Function.comp_def, intervalIntegral.integral_same] using hc.comp ha
  apply hlim.congr'
  have hevent : ∀ᶠ ε : ℝ in 𝓝[>] (0:ℝ),
      -1 ≤ (-1+ε) ∧ (-1+ε) ≤ 1 := by
    filter_upwards [self_mem_nhdsWithin,
      (show Set.Iio (2:ℝ) ∈ 𝓝[>] (0:ℝ) from
        mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num)))] with ε hpos hlt
    change 0 < ε at hpos
    change ε < 2 at hlt
    constructor <;> linarith
  filter_upwards [hevent] with ε he
  exact (gap_weighted_integral_eq_cos τ δ f (-1+ε) he.1 he.2).symm

private theorem gapSideWeighted_upper_trunc_tendsto (τ δ : ℂ) (f : ℂ → ℂ)
    (hf : ContinuousOn f (standardRootGapSegment τ δ)) :
    Tendsto (fun ε : ℝ => ∫ r in (-1:ℝ)..(1-ε),
      f (τ+δ*(r:ℂ)) / (Real.sqrt (1-r^2):ℂ))
      (𝓝[>] (0:ℝ))
      (𝓝 (∫ r in (-1:ℝ)..1,
        f (τ+δ*(r:ℂ)) / (Real.sqrt (1-r^2):ℂ))) := by
  have hε : Tendsto (fun ε : ℝ => (1:ℝ)-ε)
      (𝓝[>] (0:ℝ)) (𝓝 (1:ℝ)) := by
    have hid : Tendsto (fun ε : ℝ => ε) (𝓝[>] (0:ℝ)) (𝓝 (0:ℝ)) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    simpa using (tendsto_const_nhds.sub hid)
  have ha : Tendsto (fun ε : ℝ => Real.arccos (1-ε))
      (𝓝[>] (0:ℝ)) (𝓝 (0:ℝ)) := by
    have h := (Real.continuous_arccos.tendsto (1:ℝ)).comp hε
    simpa only [Function.comp_def, Real.arccos_one] using h
  have hc := (gapSideCosIntegral_continuous_lower τ δ f hf).tendsto 0
  have hcos : Tendsto (fun ε : ℝ =>
      ∫ θ in Real.arccos (1-ε)..Real.pi,
        f (τ+δ*(Real.cos θ:ℂ)))
      (𝓝[>] (0:ℝ))
      (𝓝 (∫ θ in (0:ℝ)..Real.pi,
        f (τ+δ*(Real.cos θ:ℂ)))) := by
    simpa only [Function.comp_def] using hc.comp ha
  have hfull := gap_weighted_integral_eq_cos τ δ f 1 (by norm_num) (by norm_num)
  rw [hfull]
  simp only [Real.arccos_one]
  apply hcos.congr'
  have hevent : ∀ᶠ ε : ℝ in 𝓝[>] (0:ℝ),
      -1 ≤ (1-ε) ∧ (1-ε) ≤ 1 := by
    filter_upwards [self_mem_nhdsWithin,
      (show Set.Iio (2:ℝ) ∈ 𝓝[>] (0:ℝ) from
        mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num)))] with ε hpos hlt
    change 0 < ε at hpos
    change ε < 2 at hlt
    constructor <;> linarith
  filter_upwards [hevent] with ε he
  exact (gap_weighted_integral_eq_cos τ δ f (1-ε) he.1 he.2).symm

/-- Truncating the left endpoint converges to the full weighted integral. -/
theorem gapSideWeighted_truncated_tendsto (τ δ : ℂ) (f : ℂ → ℂ)
    (hf : ContinuousOn f (standardRootGapSegment τ δ)) (t : ℝ)
    (htl : -1 ≤ t) (htr : t ≤ 1) :
    Tendsto (fun ε : ℝ => ∫ r in (-1+ε)..t,
      f (τ+δ*(r:ℂ)) / (Real.sqrt (1-r^2):ℂ))
      (𝓝[>] (0:ℝ))
      (𝓝 (∫ r in (-1:ℝ)..t,
        f (τ+δ*(r:ℂ)) / (Real.sqrt (1-r^2):ℂ))) := by
  let g : ℝ → ℂ := fun r => f (τ+δ*(r:ℂ)) / (Real.sqrt (1-r^2):ℂ)
  have hsmall := gapSideWeighted_small_tendsto_zero τ δ f hf
  have hlim : Tendsto (fun ε : ℝ =>
      (∫ r in (-1:ℝ)..t, g r) - ∫ r in (-1:ℝ)..(-1+ε), g r)
      (𝓝[>] (0:ℝ)) (𝓝 (∫ r in (-1:ℝ)..t, g r)) := by
    simpa [g] using tendsto_const_nhds.sub hsmall
  apply hlim.congr'
  have hevent : ∀ᶠ ε : ℝ in 𝓝[>] (0:ℝ),
      -1 ≤ (-1+ε) ∧ (-1+ε) ≤ 1 := by
    filter_upwards [self_mem_nhdsWithin,
      (show Set.Iio (2:ℝ) ∈ 𝓝[>] (0:ℝ) from
        mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num)))] with ε hpos hlt
    change 0 < ε at hpos
    change ε < 2 at hlt
    constructor <;> linarith
  filter_upwards [hevent] with ε he
  have hfull := gap_weighted_intervalIntegrable τ δ f hf t htl htr
  have hshort := gap_weighted_intervalIntegrable τ δ f hf (-1+ε) he.1 he.2
  simpa only [g] using
    (intervalIntegral.integral_interval_sub_left hfull hshort)

/-- The straight gap-side path integral pulled back by `r ↦ τ + δ r`.
    Its Jacobian is `δ`; the denominator is the selected side value of
    the standard root. -/
def gapSidePathIntegral (τ δ : ℂ) (f : ℂ → ℂ) (a b : ℝ)
    (upper : Bool) : ℂ :=
  ∫ r in a..b,
    f (τ+δ*(r:ℂ)) *
      (δ / ((if upper then -δ*I else δ*I) *
        (Real.sqrt (1-r^2):ℂ)))

private theorem gapSide_path_kernel (δ : ℂ) (r : ℝ) (hδ : δ ≠ 0)
    (hrl : -1 < r) (hrr : r < 1) (upper : Bool) :
    δ / ((if upper then -δ*I else δ*I) *
      (Real.sqrt (1-r^2):ℂ)) =
    (if upper then I else -I) / (Real.sqrt (1-r^2):ℂ) := by
  have hrad : 0 < 1-r^2 := by nlinarith
  have hs : (Real.sqrt (1-r^2):ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 hrad).ne'
  cases upper with
  | true =>
      simp only [ite_true]
      field_simp [hδ, hs]
      norm_num
  | false =>
      simp only [Bool.false_eq_true, ite_false]
      field_simp [hδ, hs]
      norm_num

/-- The path-integral kernel cancels to the signed weighted kernel away
    from the endpoints. -/
theorem gapSidePathIntegral_eq_weighted (τ δ : ℂ) (f : ℂ → ℂ)
    (a b : ℝ) (ha : a ∈ Set.Icc (-1:ℝ) 1)
    (hb : b ∈ Set.Icc (-1:ℝ) 1) (hδ : δ ≠ 0)
    (upper : Bool) :
    gapSidePathIntegral τ δ f a b upper =
      (if upper then I else -I) *
        ∫ r in a..b,
          f (τ+δ*(r:ℂ)) / (Real.sqrt (1-r^2):ℂ) := by
  unfold gapSidePathIntegral
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr_uIoo
  intro r hr
  have hrl : -1 < r := by
    rcases le_total a b with hab | hba
    · rw [Set.uIoo_of_le hab] at hr
      exact lt_of_le_of_lt ha.1 hr.1
    · rw [Set.uIoo_of_ge hba] at hr
      exact lt_of_le_of_lt hb.1 hr.1
  have hrr : r < 1 := by
    rcases le_total a b with hab | hba
    · rw [Set.uIoo_of_le hab] at hr
      exact lt_of_lt_of_le hr.2 hb.2
    · rw [Set.uIoo_of_ge hba] at hr
      exact lt_of_lt_of_le hr.2 ha.2
  dsimp only
  rw [gapSide_path_kernel δ r hδ hrl hrr upper]
  ring

/-- The full straight side path integral equals the boundary integral
    used in the cosine proof of Lemma 10.4. -/
theorem gapSidePathIntegral_eq_boundary (τ δ : ℂ) (f : ℂ → ℂ)
    (t : ℝ) (hδ : δ ≠ 0) (htl : -1 ≤ t) (htr : t ≤ 1)
    (upper : Bool) :
    gapSidePathIntegral τ δ f (-1) t upper =
      gapSideBoundaryIntegral τ δ f t upper := by
  rw [gapSidePathIntegral_eq_weighted τ δ f (-1) t
    ⟨le_rfl, by norm_num⟩ ⟨htl,htr⟩ hδ upper]
  exact gapSideWeightedIntegral_eq_boundary τ δ f t hδ htl htr upper

/-- For continuous `f`, every bounded side-path integral is a genuine
    Bochner interval integral even when an endpoint is a branch point. -/
theorem gapSidePathIntegrand_intervalIntegrable (τ δ : ℂ) (f : ℂ → ℂ)
    (hδ : δ ≠ 0) (hf : ContinuousOn f (standardRootGapSegment τ δ))
    (a b : ℝ) (ha : a ∈ Set.Icc (-1:ℝ) 1)
    (hb : b ∈ Set.Icc (-1:ℝ) 1) (upper : Bool) :
    IntervalIntegrable
      (fun r : ℝ => f (τ+δ*(r:ℂ)) *
        (δ / ((if upper then -δ*I else δ*I) *
          (Real.sqrt (1-r^2):ℂ)))) volume a b := by
  let g : ℝ → ℂ := fun r => f (τ+δ*(r:ℂ)) / (Real.sqrt (1-r^2):ℂ)
  have hga := gap_weighted_intervalIntegrable τ δ f hf a ha.1 ha.2
  have hgb := gap_weighted_intervalIntegrable τ δ f hf b hb.1 hb.2
  have hab : IntervalIntegrable g volume a b := hga.symm.trans hgb
  have hconst := hab.const_mul (if upper then I else -I)
  apply hconst.congr_uIoo
  intro r hr
  have hrl : -1 < r := by
    rcases le_total a b with hab | hba
    · rw [Set.uIoo_of_le hab] at hr
      exact lt_of_le_of_lt ha.1 hr.1
    · rw [Set.uIoo_of_ge hba] at hr
      exact lt_of_le_of_lt hb.1 hr.1
  have hrr : r < 1 := by
    rcases le_total a b with hab | hba
    · rw [Set.uIoo_of_le hab] at hr
      exact lt_of_lt_of_le hr.2 hb.2
    · rw [Set.uIoo_of_ge hba] at hr
      exact lt_of_lt_of_le hr.2 ha.2
  dsimp only [g]
  rw [gapSide_path_kernel δ r hδ hrl hrr upper]
  ring

/-- Improper left-endpoint path integrals converge to the full side
    boundary integral. -/
theorem gapSidePathIntegral_tendsto_boundary (τ δ : ℂ) (f : ℂ → ℂ)
    (hδ : δ ≠ 0) (hf : ContinuousOn f (standardRootGapSegment τ δ))
    (t : ℝ) (htl : -1 ≤ t) (htr : t ≤ 1) (upper : Bool) :
    Tendsto (fun ε : ℝ =>
      gapSidePathIntegral τ δ f (-1+ε) t upper)
      (𝓝[>] (0:ℝ))
      (𝓝 (gapSideBoundaryIntegral τ δ f t upper)) := by
  have hbase := (gapSideWeighted_truncated_tendsto τ δ f hf t htl htr).const_mul
    (if upper then I else -I)
  have hlim : Tendsto (fun ε : ℝ =>
      (if upper then I else -I) *
        ∫ r in (-1+ε)..t,
          f (τ+δ*(r:ℂ)) / (Real.sqrt (1-r^2):ℂ))
      (𝓝[>] (0:ℝ))
      (𝓝 (gapSideBoundaryIntegral τ δ f t upper)) := by
    rw [← gapSideWeightedIntegral_eq_boundary τ δ f t hδ htl htr upper]
    simpa only [gapSideWeightedIntegral] using hbase
  apply hlim.congr'
  have hevent : ∀ᶠ ε : ℝ in 𝓝[>] (0:ℝ),
      (-1+ε) ∈ Set.Icc (-1:ℝ) 1 := by
    filter_upwards [self_mem_nhdsWithin,
      (show Set.Iio (2:ℝ) ∈ 𝓝[>] (0:ℝ) from
        mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num)))] with ε hpos hlt
    change 0 < ε at hpos
    change ε < 2 at hlt
    constructor <;> linarith
  filter_upwards [hevent] with ε he
  exact (gapSidePathIntegral_eq_weighted τ δ f (-1+ε) t he ⟨htl,htr⟩ hδ upper).symm

/-- At the right gap endpoint, cutting off both singular endpoints gives
    the same side boundary integral in the limit. -/
theorem gapSidePathIntegral_double_trunc_tendsto (τ δ : ℂ) (f : ℂ → ℂ)
    (hδ : δ ≠ 0) (hf : ContinuousOn f (standardRootGapSegment τ δ))
    (upper : Bool) :
    Tendsto (fun ε : ℝ =>
      gapSidePathIntegral τ δ f (-1+ε) (1-ε) upper)
      (𝓝[>] (0:ℝ))
      (𝓝 (gapSideBoundaryIntegral τ δ f 1 upper)) := by
  let g : ℝ → ℂ := fun r => f (τ+δ*(r:ℂ)) / (Real.sqrt (1-r^2):ℂ)
  have hbig := gapSideWeighted_upper_trunc_tendsto τ δ f hf
  have hsmall := gapSideWeighted_small_tendsto_zero τ δ f hf
  have hdiff : Tendsto (fun ε : ℝ =>
      (∫ r in (-1:ℝ)..(1-ε), g r) -
      ∫ r in (-1:ℝ)..(-1+ε), g r)
      (𝓝[>] (0:ℝ))
      (𝓝 (∫ r in (-1:ℝ)..1, g r)) := by
    simpa [g] using hbig.sub hsmall
  have hlim := hdiff.const_mul (if upper then I else -I)
  have hlim' : Tendsto (fun ε : ℝ =>
      (if upper then I else -I) *
        ((∫ r in (-1:ℝ)..(1-ε), g r) -
          ∫ r in (-1:ℝ)..(-1+ε), g r))
      (𝓝[>] (0:ℝ))
      (𝓝 (gapSideBoundaryIntegral τ δ f 1 upper)) := by
    rw [← gapSideWeightedIntegral_eq_boundary τ δ f 1 hδ (by norm_num) (by norm_num) upper]
    simpa only [gapSideWeightedIntegral, g] using hlim
  apply hlim'.congr'
  have hevent : ∀ᶠ ε : ℝ in 𝓝[>] (0:ℝ),
      (-1+ε) ∈ Set.Icc (-1:ℝ) 1 ∧
      (1-ε) ∈ Set.Icc (-1:ℝ) 1 := by
    filter_upwards [self_mem_nhdsWithin,
      (show Set.Iio (2:ℝ) ∈ 𝓝[>] (0:ℝ) from
        mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num)))] with ε hpos hlt
    change 0 < ε at hpos
    change ε < 2 at hlt
    constructor <;> constructor <;> linarith
  filter_upwards [hevent] with ε he
  have hleft := gap_weighted_intervalIntegrable τ δ f hf (-1+ε) he.1.1 he.1.2
  have hright := gap_weighted_intervalIntegrable τ δ f hf (1-ε) he.2.1 he.2.2
  rw [gapSidePathIntegral_eq_weighted τ δ f (-1+ε) (1-ε)
    he.1 he.2 hδ upper]
  congr 1
  simpa only [g] using (intervalIntegral.integral_interval_sub_left hright hleft)

end NLS.ZakharovShabat
