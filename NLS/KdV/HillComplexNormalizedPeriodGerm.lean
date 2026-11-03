import NLS.KdV.HillComplexPeriodLocalRootGerm

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal

namespace NLS.KdV

variable
    (hq : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

def hillAbelianNormalizedComplexPsi (n : ℕ) (t : Coeff 2 × Coeff 2) (E : ℂ) : ℂ :=
  hillAbelianHilbertPsi n (E,t.1)/hillAbelianComplexPeriod 0 hq hr n n t

theorem hillAbelianNormalizedComplexPsi_period_eq_ratio (n k : ℕ) (t : Coeff 2 × Coeff 2) :
    (2*(Real.pi : ℂ))⁻¹ * ∮ E in C((hillRealGapCenter 0 hq hr k : ℂ),
      hillRealGapHalfLength 0 hq hr k+hillRealGapCollar 0 hq hr k),
      hillAbelianNormalizedComplexPsi hq hr n t E/hillAbelianComplexRoot 0 hq hr (E,t.2) =
    hillAbelianComplexPeriod 0 hq hr n k t/hillAbelianComplexPeriod 0 hq hr n n t := by
  unfold hillAbelianNormalizedComplexPsi
  have he : (fun E => hillAbelianHilbertPsi n (E,t.1)/hillAbelianComplexPeriod 0 hq hr n n t/
      hillAbelianComplexRoot 0 hq hr (E,t.2)) =
      (fun E => (hillAbelianComplexPeriod 0 hq hr n n t)⁻¹*
        (hillAbelianHilbertPsi n (E,t.1)/hillAbelianComplexRoot 0 hq hr (E,t.2))) := by
    funext E
    ring
  rw [he,circleIntegral.integral_const_mul]
  unfold hillAbelianComplexPeriod
  ring

theorem exists_hillAbelianNormalizedComplexPsi_local_periods (n : ℕ) (hn : 1 ≤ n) :
    ∃ a : Coeff 2 → PositiveDeletedCoeff 2 (n : ℤ), AnalyticAt ℂ a 0 ∧ a 0 = 0 ∧
      ∀ᶠ p in 𝓝 (0 : Coeff 2), ∀ k : ℕ, 1 ≤ k →
        (∀ E ∈ sphere (hillRealGapCenter 0 hq hr k : ℂ)
          (hillRealGapHalfLength 0 hq hr k+hillRealGapCollar 0 hq hr k),
          (E,p) ∈ hillAbelianComplexRootDomain 0 hq hr) ∧
        ((2*(Real.pi : ℂ))⁻¹ * ∮ E in C((hillRealGapCenter 0 hq hr k : ℂ),
          hillRealGapHalfLength 0 hq hr k+hillRealGapCollar 0 hq hr k),
          hillAbelianNormalizedComplexPsi hq hr n ((a p : Coeff 2),p) E/
            hillAbelianComplexRoot 0 hq hr (E,p)) = if k = n then 1 else 0 := by
  obtain ⟨a,ha,ha0,hroots⟩ := exists_hillAbelianComplexPeriod_local_root_germ hq hr n hn
  obtain ⟨ε,D,hε,_,hc⟩ := exists_hillComplexPeriodControl hq hr
  refine ⟨a,ha,ha0,?_⟩
  filter_upwards [hroots,Metric.ball_mem_nhds (0 : Coeff 2) hε] with p hp hpball
  intro k hk
  have hpnorm : ‖p‖ ≤ ε := (show ‖p‖ < ε by simpa only [mem_ball,dist_zero_right] using hpball).le
  refine ⟨(hc p hpnorm).1 k hk,?_⟩
  rw [hillAbelianNormalizedComplexPsi_period_eq_ratio]
  by_cases hkn : k = n
  · subst k
    rw [if_pos rfl,div_self hp.2]
  · rw [if_neg hkn,hp.1 k hk hkn,zero_div]

theorem analyticAt_hillAbelianNormalizedComplexPsi_root_germ (n : ℕ) (hn : 1 ≤ n)
    (a : Coeff 2 → Coeff 2) (ha : AnalyticAt ℂ a 0) (ha0 : a 0 = 0) (E : ℂ) :
    AnalyticAt ℂ (fun t : ℂ × Coeff 2 => hillAbelianNormalizedComplexPsi hq hr n (a t.2,t.2) t.1)
      (E,0) := by
  have hJ : AnalyticAt ℂ (fun t : ℂ × Coeff 2 => (t.1,a t.2)) (E,0) :=
    analyticAt_fst.prod (ha.comp (f := fun t : ℂ × Coeff 2 => t.2) analyticAt_snd)
  have hN : AnalyticAt ℂ (fun t : ℂ × Coeff 2 => hillAbelianHilbertPsi n (t.1,a t.2)) (E,0) := by
    have hBase : AnalyticAt ℂ (hillAbelianHilbertPsi n) (E,a 0) :=
      analyticOnNhd_hillAbelianHilbertPsi n (E,a 0) (mem_univ _)
    convert! hBase.comp (f := fun t : ℂ × Coeff 2 => (t.1,a t.2)) hJ using 1
  have hD : AnalyticAt ℂ (fun t : ℂ × Coeff 2 => hillAbelianComplexPeriod 0 hq hr n n (a t.2,t.2)) (E,0) := by
    have hBase := analyticAt_hillAbelianComplexPeriod_root_germ hq hr n n hn a ha
    convert! hBase.comp (f := fun t : ℂ × Coeff 2 => t.2)
      (analyticAt_snd (𝕜 := ℂ) (p := (E,(0 : Coeff 2)))) using 1
  have hne : hillAbelianComplexPeriod 0 hq hr n n (a 0,0) ≠ 0 := by
    rw [ha0,hillAbelianComplexPeriod_zero_diagonal hq hr n hn]
    exact one_ne_zero
  exact hN.div hD hne

end NLS.KdV
