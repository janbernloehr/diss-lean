import NLS.ComplexAnalysis.SingularEndpointPathIntegrability
import NLS.ComplexAnalysis.PrimitiveRadialContinuation

/-!
# Integrable square-root singularities at both path endpoints

A t(1-t) square-root weight allows singularities at both endpoints. A
transverse distance bound for a C¹ path gives this weight for any chosen
root of a quadratic with distinct zeros. A continuous numerator then
has an integrable pulled-back one-form.
-/

noncomputable section
open Set Metric Complex Filter Topology MeasureTheory
open scoped unitInterval
namespace NLS.ComplexAnalysis

theorem integrableOn_Ioo_of_norm_mul_sqrt_endpoints_le
    (f : ℝ → ℂ) {d M : ℝ} (hd : 0 < d)
    (hmeas : AEStronglyMeasurable f (volume.restrict (Ioo (0:ℝ) 1)))
    (hbound : ∀ t ∈ Ioo (0:ℝ) 1, ‖f t * (Real.sqrt (d*(t*(1-t))) : ℂ)‖ ≤ M) :
    IntegrableOn f (Ioo (0:ℝ) 1) := by
  let g : ℝ → ℝ := fun t => t^(-1/2:ℝ)+(1-t)^(-1/2:ℝ)
  have hp : IntervalIntegrable (fun t : ℝ => t^(-1/2:ℝ)) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).2
      ((intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).2 (by norm_num))
  have hq : IntervalIntegrable (fun t : ℝ => (1-t)^(-1/2:ℝ)) volume 0 1 := by
    simpa using (hp.comp_sub_left 1).symm
  have hg : IntegrableOn (fun t => (M/Real.sqrt d)*g t) (Ioo (0:ℝ) 1) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).1 ((hp.add hq).const_mul _)
  refine hg.mono' hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  have ht0 : 0 ≤ t := ht.1.le
  have ht1 : 0 ≤ 1-t := (sub_pos.mpr ht.2).le
  have hsd : 0 < Real.sqrt d := Real.sqrt_pos.mpr hd
  have hpw (x : ℝ) (hx : 0 < x) : Real.sqrt x*x^(-1/2:ℝ) = 1 := by
    rw [Real.sqrt_eq_rpow,← Real.rpow_add hx]
    norm_num
  have hweight : 1 ≤ Real.sqrt (t*(1-t))*g t := by
    have he : Real.sqrt (t*(1-t))*g t = Real.sqrt t+Real.sqrt (1-t) := by
      rw [Real.sqrt_mul ht0]
      dsimp only [g]
      calc
        _ = Real.sqrt (1-t)*(Real.sqrt t*t^(-1/2:ℝ))+
            Real.sqrt t*(Real.sqrt (1-t)*(1-t)^(-1/2:ℝ)) := by ring
        _ = _ := by rw [hpw t ht.1,hpw (1-t) (sub_pos.mpr ht.2)]; ring
    rw [he]
    have htS := Real.sqrt_nonneg t
    have huS := Real.sqrt_nonneg (1-t)
    nlinarith [Real.sq_sqrt ht0,Real.sq_sqrt ht1,mul_nonneg htS huS]
  have hb : ‖f t‖*Real.sqrt (t*(1-t)) ≤ M/Real.sqrt d := by
    apply (le_div_iff₀ hsd).2
    have h := hbound t ht
    rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (Real.sqrt_nonneg _),Real.sqrt_mul hd.le] at h
    nlinarith only [h]
  have hg0 : 0 ≤ g t := add_nonneg (Real.rpow_nonneg ht0 _) (Real.rpow_nonneg ht1 _)
  have hf : ‖f t‖ ≤ (M/Real.sqrt d)*g t := by
    calc
      _ = ‖f t‖*1 := (mul_one _).symm
      _ ≤ ‖f t‖*(Real.sqrt (t*(1-t))*g t) := mul_le_mul_of_nonneg_left hweight (norm_nonneg _)
      _ = (‖f t‖*Real.sqrt (t*(1-t)))*g t := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hb hg0
  exact hf

theorem curveIntegrable_of_norm_mul_sqrt_endpoints_le
    {a b : ℂ} (ω : ℂ → ℂ →L[ℂ] ℂ) (γ : Path a b) {d M : ℝ} (hd : 0 < d)
    (hmeas : AEStronglyMeasurable (curveIntegralFun ω γ) (volume.restrict (Ioo (0:ℝ) 1)))
    (hbound : ∀ t ∈ Ioo (0:ℝ) 1,
      ‖curveIntegralFun ω γ t * (Real.sqrt (d*(t*(1-t))) : ℂ)‖ ≤ M) :
    CurveIntegrable ω γ :=
  (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).2
    (integrableOn_Ioo_of_norm_mul_sqrt_endpoints_le _ hd hmeas hbound)


theorem curveIntegrable_div_quadratic_root_of_transverse_bound
    {a r b : ℂ} (har : a ≠ r) (γ : Path a b)
    (hγ : ContDiffOn ℝ 1 γ.extend (Icc 0 1)) (f q : ℂ → ℂ)
    (hf : ContinuousOn (fun t : ℝ => f (γ.extend t)) (Icc 0 1))
    (hq : ContinuousOn (fun t : ℝ => q (γ.extend t)) (Ioo 0 1))
    (hsq : ∀ t ∈ Ioo (0:ℝ) 1, q (γ.extend t)^2 = (a-γ.extend t)*(r-γ.extend t))
    (k : ℝ) (hk : 0 < k)
    (hsep : ∀ t ∈ Ioo (0:ℝ) 1,
      k*t*(1-t) ≤ ‖a-γ.extend t‖ ∧ k*t*(1-t) ≤ ‖r-γ.extend t‖) :
    CurveIntegrable (holomorphicOneForm (fun z => f z/q z)) γ := by
  let d := ‖a-r‖/2*k
  have hd : 0 < d := mul_pos (div_pos (norm_pos_iff.mpr (sub_ne_zero.mpr har)) (by norm_num)) hk
  have hroot (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) :
      Real.sqrt (d*(t*(1-t))) ≤ ‖q (γ.extend t)‖ := by
    have hn : ‖q (γ.extend t)‖^2 = ‖a-γ.extend t‖*‖r-γ.extend t‖ := by
      rw [← norm_pow,hsq t ht,norm_mul]
    apply Real.sqrt_le_iff.mpr ⟨norm_nonneg _,?_⟩
    rw [hn]
    have htri : ‖a-r‖ ≤ ‖a-γ.extend t‖+‖r-γ.extend t‖ := by
      simpa only [sub_add_sub_cancel,norm_sub_rev] using norm_add_le (a-γ.extend t) (γ.extend t-r)
    have hkt : 0 ≤ k*t*(1-t) := mul_nonneg (mul_nonneg hk.le ht.1.le) (sub_pos.mpr ht.2).le
    have ha := (hsep t ht).1
    have hr := (hsep t ht).2
    by_cases hleft : ‖a-r‖/2 ≤ ‖a-γ.extend t‖
    · have hh := mul_le_mul hleft hr hkt (norm_nonneg _)
      dsimp only [d]
      nlinarith only [hh]
    · have hright : ‖a-r‖/2 ≤ ‖r-γ.extend t‖ := by linarith
      have hh := mul_le_mul ha hright (by positivity : 0 ≤ ‖a-r‖/2) (norm_nonneg _)
      dsimp only [d]
      nlinarith only [hh]
  have hne (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) : q (γ.extend t) ≠ 0 := by
    apply norm_pos_iff.mp
    exact (Real.sqrt_pos.mpr (mul_pos hd (mul_pos ht.1 (sub_pos.mpr ht.2)))).trans_le (hroot t ht)
  obtain ⟨M₀,hM₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  let M := max M₀ 0
  have hM : 0 ≤ M := le_max_right _ _
  have hboundF (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) : ‖f (γ.extend t)‖ ≤ M :=
    (hM₀ t (Ioo_subset_Icc_self ht)).trans (le_max_left _ _)
  have hderiv : ContinuousOn (fun t => derivWithin γ.extend (Icc 0 1) t) (Icc 0 1) :=
    hγ.continuousOn_derivWithin uniqueDiffOn_Icc_zero_one le_rfl
  obtain ⟨D₀,hD₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hderiv
  let D := max D₀ 0
  have hD : 0 ≤ D := le_max_right _ _
  have hspeed (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) : ‖derivWithin γ.extend (Icc 0 1) t‖ ≤ D :=
    (hD₀ t (Ioo_subset_Icc_self ht)).trans (le_max_left _ _)
  let ω := holomorphicOneForm (fun z => f z/q z)
  have hcont : ContinuousOn (curveIntegralFun ω γ) (Ioo (0:ℝ) 1) := by
    have hquot := (hf.mono Ioo_subset_Icc_self).div hq hne
    apply (hquot.mul (hderiv.mono Ioo_subset_Icc_self)).congr
    intro t ht
    rw [curveIntegralFun_def,holomorphicOneForm_apply]
    rfl
  apply curveIntegrable_of_norm_mul_sqrt_endpoints_le ω γ hd
    (hcont.aestronglyMeasurable measurableSet_Ioo)
  intro t ht
  have hb : ‖(f (γ.extend t)/q (γ.extend t))*(Real.sqrt (d*(t*(1-t))) : ℂ)‖ ≤ M :=
    by
      rw [norm_mul,norm_div,Complex.norm_real,Real.norm_of_nonneg (Real.sqrt_nonneg _)]
      calc
        _ ≤ (‖f (γ.extend t)‖/‖q (γ.extend t)‖)*‖q (γ.extend t)‖ :=
          mul_le_mul_of_nonneg_left (hroot t ht) (by positivity)
        _ = ‖f (γ.extend t)‖ := div_mul_cancel₀ _ (norm_ne_zero_iff.mpr (hne t ht))
        _ ≤ M := hboundF t ht
  rw [curveIntegralFun_def,holomorphicOneForm_apply]
  calc
    _ = ‖(f (γ.extend t)/q (γ.extend t))*(Real.sqrt (d*(t*(1-t))) : ℂ)‖*
        ‖derivWithin γ.extend (Icc 0 1) t‖ := by simp only [norm_mul]; ring
    _ ≤ M*D := mul_le_mul hb (hspeed t ht) (norm_nonneg _) hM


/-- Absolute curve integrability gives the joint limit as both endpoints
are truncated independently; singular endpoint values do not contribute. -/
theorem tendsto_curveIntegral_truncations {a b : ℂ}
    (ω : ℂ → ℂ →L[ℂ] ℂ) (γ : Path a b) (hint : CurveIntegrable ω γ) :
    Tendsto (fun u : ℝ × ℝ => ∫ t in u.1..u.2, curveIntegralFun ω γ t)
      ((𝓝[>] (0:ℝ)) ×ˢ (𝓝[<] (1:ℝ))) (𝓝 (∫ᶜ z in γ, ω z)) := by
  let f := curveIntegralFun ω γ
  let P : ℝ → ℂ := fun u => ∫ t in (0:ℝ)..u, f t
  have hP : ContinuousOn P (Icc (0:ℝ) 1) := by
    simpa only [uIcc_of_le zero_le_one] using
      intervalIntegral.continuousOn_primitive_interval' hint left_mem_uIcc
  have hl0 : Tendsto P (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have hh := (hP 0 (by norm_num)).tendsto.mono_left
      (nhdsWithin_le_iff.mpr (Icc_mem_nhdsGT (by norm_num : (0:ℝ) < 1)))
    simpa only [P,intervalIntegral.integral_same] using hh
  have hl1 : Tendsto P (𝓝[<] (1:ℝ)) (𝓝 (∫ᶜ z in γ, ω z)) := by
    rw [curveIntegral_def]
    exact (hP 1 (by norm_num)).tendsto.mono_left
      (nhdsWithin_le_iff.mpr (Icc_mem_nhdsLT (by norm_num : (0:ℝ) < 1)))
  have hi (u : ℝ) (hu : u ∈ Icc (0:ℝ) 1) : IntervalIntegrable f volume 0 u := by
    apply hint.mono_set
    rw [uIcc_of_le hu.1,uIcc_of_le zero_le_one]
    exact fun _ hx => ⟨hx.1,hx.2.trans hu.2⟩
  have hlim := (hl1.comp tendsto_snd).sub (hl0.comp tendsto_fst)
  simp only [sub_zero] at hlim
  apply hlim.congr'
  have hu : ∀ᶠ u in 𝓝[>] (0:ℝ), u ∈ Icc (0:ℝ) 1 := Icc_mem_nhdsGT (by norm_num)
  have hv : ∀ᶠ v in 𝓝[<] (1:ℝ), v ∈ Icc (0:ℝ) 1 := Icc_mem_nhdsLT (by norm_num)
  filter_upwards [hu.prod_mk hv] with u hu
  exact intervalIntegral.integral_interval_sub_left (hi u.2 hu.2) (hi u.1 hu.1)

end NLS.ComplexAnalysis
