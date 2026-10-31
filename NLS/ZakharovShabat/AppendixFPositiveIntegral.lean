import NLS.ComplexAnalysis.AppendixFPositiveMajorant
import NLS.ComplexAnalysis.AppendixFMovingDominated
import NLS.ZakharovShabat.AppendixFRootPath

/-! # Applying the corrected Appendix F majorant to the interval integrals -/
noncomputable section
open Set Complex Filter Topology MeasureTheory
namespace NLS.ComplexAnalysis

/-- The corrected positive weight tends to one at every strictly positive parameter. -/
theorem appendixF_positive_majorant_tendsto_pointwise {ι : Type*} {l : Filter ι}
    (e : ι → ℝ) (he : Tendsto e l (𝓝 0)) (t : ℝ) (ht : 0 < t) :
    Tendsto (fun i => Real.sqrt (t+e i)/Real.sqrt |t-e i|) l (𝓝 1) := by
  have hn : Tendsto (fun i => Real.sqrt (t+e i)) l (𝓝 (Real.sqrt t)) := by
    simpa only [add_zero] using (tendsto_const_nhds.add he).sqrt
  have hd : Tendsto (fun i => Real.sqrt |t-e i|) l (𝓝 (Real.sqrt t)) := by
    have hd₀ : Tendsto (fun i => t-e i) l (𝓝 (t-0)) := tendsto_const_nhds.sub he
    simpa only [sub_zero, abs_of_pos ht] using hd₀.abs.sqrt
  convert hn.div hd (Real.sqrt_pos.mpr ht).ne' using 1
  · rfl
  · rw [div_self (Real.sqrt_pos.mpr ht).ne']

/-- Pointwise convergence dominated by the explicit corrected weight implies convergence
of the unit-interval integrals. Integrability and L1 convergence of the weight are derived. -/
theorem appendixF_tendsto_intervalIntegral_positive_majorant
    (F : ℕ → ℝ → ℂ) (f : ℝ → ℂ) (e : ℕ → ℝ)
    (he : Tendsto e atTop (𝓝 0)) (herange : ∀ n, 0 ≤ e n ∧ e n ≤ 1)
    (C : ℝ) (hC : 0 ≤ C)
    (hF : ∀ n, AEStronglyMeasurable (F n) (volume.restrict (Ioc (0:ℝ) 1)))
    (hbound : ∀ n, ∀ᵐ t ∂volume.restrict (Ioc (0:ℝ) 1),
      ‖F n t‖ ≤ C*(Real.sqrt (t+e n)/Real.sqrt |t-e n|))
    (hFlim : ∀ t ∈ Ioc (0:ℝ) 1, Tendsto (fun n => F n t) atTop (𝓝 (f t))) :
    Tendsto (fun n => ∫ t in (0:ℝ)..1, F n t) atTop (𝓝 (∫ t in (0:ℝ)..1, f t)) := by
  have hg n : Integrable (fun t : ℝ => Real.sqrt (t+e n)/Real.sqrt |t-e n|)
      (volume.restrict (Ioc (0:ℝ) 1)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
      (appendixF_positive_majorant_integrable (e n) (herange n).1 (herange n).2)
  have hp : ∀ᵐ t ∂volume.restrict (Ioc (0:ℝ) 1),
      Tendsto (fun n => Real.sqrt (t+e n)/Real.sqrt |t-e n|) atTop (𝓝 1) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact appendixF_positive_majorant_tendsto_pointwise e he t ht.1
  have hfp : ∀ᵐ t ∂volume.restrict (Ioc (0:ℝ) 1),
      Tendsto (fun n => F n t) atTop (𝓝 (f t)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hFlim t ht
  have hL1 := appendixF_positive_majorant_tendsto_L1 e he (Eventually.of_forall herange)
  simp only [intervalIntegral.integral_of_le zero_le_one] at hL1 ⊢
  exact appendixF_tendsto_integral_moving_majorant (volume.restrict (Ioc (0:ℝ) 1))
    F f (fun n t => Real.sqrt (t+e n)/Real.sqrt |t-e n|) C hC hF hg hbound hfp hp hL1

end NLS.ComplexAnalysis
namespace NLS.ZakharovShabat

/-- The actual normalized standard-root quotient satisfies the corrected positive bound
under the half-gap critical offset, for every nonzero complex terminal displacement. -/
theorem appendixF_standard_root_quotient_majorant (τ γ a z : ℂ) (hz : z ≠ 0)
    (ha : ‖a-τ‖ ≤ ‖γ‖/2) (t : ℝ) (ht : 0 < t) (hne : t ≠ ‖γ/(2*z)‖) :
    ‖(a-(τ+(t:ℂ)*z))/normalizedStandardRoot τ (γ^2) (τ+(t:ℂ)*z)‖ ≤
      Real.sqrt (t+‖γ/(2*z)‖)/Real.sqrt |t-‖γ/(2*z)‖| := by
  have hnum : ‖(τ-a)/z‖ ≤ ‖γ/(2*z)‖ := by
    rw [norm_div, norm_sub_rev]
    calc
      ‖a-τ‖/‖z‖ ≤ (‖γ‖/2)/‖z‖ := div_le_div_of_nonneg_right ha (norm_nonneg z)
      _ = ‖γ/(2*z)‖ := by rw [norm_div, norm_mul]; norm_num; ring
  have hs : (Complex.sqrt ((t:ℂ)^2-(γ/(2*z))^2))^2 = (t:ℂ)^2-(γ/(2*z))^2 := by
    have h := Complex.cpow_nat_inv_pow ((t:ℂ)^2-(γ/(2*z))^2) (Nat.succ_ne_zero 1)
    norm_num at h
    simpa only [Complex.sqrt, one_div] using h
  have hb := NLS.ComplexAnalysis.appendixF_quotient_le_positive_majorant t ht.le
    (γ/(2*z)) ((τ-a)/z) (Complex.sqrt ((t:ℂ)^2-(γ/(2*z))^2)) hnum hs hne
  rw [appendixF_normalized_root_on_spoke τ γ z hz t ht]
  have he : a-(τ+(t:ℂ)*z) = -z*((t:ℂ)+(τ-a)/z) := by field_simp; ring
  rw [he, mul_div_mul_left _ _ (neg_ne_zero.mpr hz)]
  exact hb

/-- The actual rescaled midpoint-path integrals converge when the gap collapses. The
half-gap critical bound and one common regular-factor bound supply the corrected majorant. -/
theorem appendixF_collapsing_spoke_integral_tendsto
    (τ γ a z : ℕ → ℂ) (z₀ : ℂ) (hz₀ : z₀ ≠ 0)
    (hγ : Tendsto γ atTop (𝓝 0)) (hz : Tendsto z atTop (𝓝 z₀))
    (hzn : ∀ n, z n ≠ 0) (ha : ∀ n, ‖a n-τ n‖ ≤ ‖γ n‖/2)
    (hrange : ∀ n, ‖γ n/(2*z n)‖ ≤ 1)
    (χ : ℕ → ℝ → ℂ) (χ₀ : ℝ → ℂ)
    (hχ : ∀ t ∈ Ioc (0:ℝ) 1, Tendsto (fun n => χ n t) atTop (𝓝 (χ₀ t)))
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ n, ∀ t ∈ Ioc (0:ℝ) 1, ‖z n‖*‖χ n t‖ ≤ C)
    (hmeas : ∀ n, AEStronglyMeasurable
      (fun t : ℝ => z n*((a n-(τ n+(t:ℂ)*z n)) /
        normalizedStandardRoot (τ n) ((γ n)^2) (τ n+(t:ℂ)*z n))*χ n t)
      (volume.restrict (Ioc (0:ℝ) 1))) :
    Tendsto (fun n => ∫ t in (0:ℝ)..1, z n*((a n-(τ n+(t:ℂ)*z n)) /
      normalizedStandardRoot (τ n) ((γ n)^2) (τ n+(t:ℂ)*z n))*χ n t)
      atTop (𝓝 (∫ t in (0:ℝ)..1, z₀*χ₀ t)) := by
  have hden : (2:ℂ)*z₀ ≠ 0 := mul_ne_zero (by norm_num) hz₀
  have he : Tendsto (fun n => ‖γ n/(2*z n)‖) atTop (𝓝 (0:ℝ)) := by
    simpa using (hγ.div (tendsto_const_nhds.mul hz) hden).norm
  have ha₀ : Tendsto (fun n => a n-τ n) atTop (𝓝 0) := by
    apply squeeze_zero_norm ha
    simpa only [norm_zero, zero_div] using hγ.norm.div_const 2
  apply NLS.ComplexAnalysis.appendixF_tendsto_intervalIntegral_positive_majorant
    _ _ (fun n => ‖γ n/(2*z n)‖) he (fun n => ⟨norm_nonneg _, hrange n⟩) C hC hmeas
  · intro n
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      (volume.restrict (Ioc (0:ℝ) 1)).ae_ne ‖γ n/(2*z n)‖] with t ht hne
    have hq := appendixF_standard_root_quotient_majorant
      (τ n) (γ n) (a n) (z n) (hzn n) (ha n) t ht.1 hne
    have hg : 0 ≤ Real.sqrt (t+‖γ n/(2*z n)‖)/Real.sqrt |t-‖γ n/(2*z n)‖| :=
      div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    rw [norm_mul, norm_mul]
    calc
      _ ≤ (‖z n‖*(Real.sqrt (t+‖γ n/(2*z n)‖)/Real.sqrt |t-‖γ n/(2*z n)‖|))*‖χ n t‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hq (norm_nonneg _)) (norm_nonneg _)
      _ = (‖z n‖*‖χ n t‖)*(Real.sqrt (t+‖γ n/(2*z n)‖)/Real.sqrt |t-‖γ n/(2*z n)‖|) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (hbound n t ht) hg
  · intro t ht
    have hq := appendixF_spoke_quotient_tendsto τ γ a z z₀ hz₀ hγ hz ha₀ t ht.1
    convert (hz.mul hq).mul (hχ t ht) using 1
    simp only [mul_one]

/-- The normalized gap is automatically small on a tail, so the actual integral limit
does not require an extra uniform bound on the first finitely many gaps. -/
theorem appendixF_collapsing_spoke_integral_tendsto_of_gap_zero
    (τ γ a z : ℕ → ℂ) (z₀ : ℂ) (hz₀ : z₀ ≠ 0)
    (hγ : Tendsto γ atTop (𝓝 0)) (hz : Tendsto z atTop (𝓝 z₀))
    (hzn : ∀ n, z n ≠ 0) (ha : ∀ n, ‖a n-τ n‖ ≤ ‖γ n‖/2)
    (χ : ℕ → ℝ → ℂ) (χ₀ : ℝ → ℂ)
    (hχ : ∀ t ∈ Ioc (0:ℝ) 1, Tendsto (fun n => χ n t) atTop (𝓝 (χ₀ t)))
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ n, ∀ t ∈ Ioc (0:ℝ) 1, ‖z n‖*‖χ n t‖ ≤ C)
    (hmeas : ∀ n, AEStronglyMeasurable
      (fun t : ℝ => z n*((a n-(τ n+(t:ℂ)*z n)) /
        normalizedStandardRoot (τ n) ((γ n)^2) (τ n+(t:ℂ)*z n))*χ n t)
      (volume.restrict (Ioc (0:ℝ) 1))) :
    Tendsto (fun n => ∫ t in (0:ℝ)..1, z n*((a n-(τ n+(t:ℂ)*z n)) /
      normalizedStandardRoot (τ n) ((γ n)^2) (τ n+(t:ℂ)*z n))*χ n t)
      atTop (𝓝 (∫ t in (0:ℝ)..1, z₀*χ₀ t)) := by
  have hden : (2:ℂ)*z₀ ≠ 0 := mul_ne_zero (by norm_num) hz₀
  have he : Tendsto (fun n => ‖γ n/(2*z n)‖) atTop (𝓝 (0:ℝ)) := by
    simpa using (hγ.div (tendsto_const_nhds.mul hz) hden).norm
  obtain ⟨N, hN⟩ := eventually_atTop.mp (he.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1)))
  apply (tendsto_add_atTop_iff_nat N).mp
  exact appendixF_collapsing_spoke_integral_tendsto
    (fun n => τ (n+N)) (fun n => γ (n+N)) (fun n => a (n+N)) (fun n => z (n+N)) z₀ hz₀
    (hγ.comp (tendsto_add_atTop_nat N)) (hz.comp (tendsto_add_atTop_nat N))
    (fun n => hzn (n+N)) (fun n => ha (n+N))
    (fun n => (hN (n+N) (Nat.le_add_left N n)).le)
    (fun n => χ (n+N)) χ₀ (fun t ht => (hχ t ht).comp (tendsto_add_atTop_nat N))
    C hC (fun n => hbound (n+N)) (fun n => hmeas (n+N))

end NLS.ZakharovShabat
