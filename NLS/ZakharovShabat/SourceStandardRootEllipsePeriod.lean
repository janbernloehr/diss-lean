import NLS.ZakharovShabat.SourceStandardRootEllipsePath
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.MeanValue

/-!
# Local weighted periods on shrinking ellipses

Cauchy's theorem on an annulus compares the pulled-back circle periods.
The numerator is required to be analytic only on the supplied neighborhood
of the gap. The limiting ellipse average is the ordinary cosine average.
-/

noncomputable section
open Set Metric Complex Filter MeasureTheory NLS.ComplexAnalysis
open scoped Topology
namespace NLS.ZakharovShabat

/-- The pullback circle integral is 2πi times the ellipse average. -/
theorem circleIntegral_joukowski_div (τ δ : ℂ) (r : ℝ) (hr : 0 < r) (f : ℂ → ℂ) :
    (∮ u in C((0:ℂ),r), f (standardRootJoukowski τ δ u)/u) =
      (2*(Real.pi:ℂ)*Complex.I)*(∫ t in (0:ℝ)..1, f (standardRootEllipseMap τ δ r t)) := by
  have hi : (∮ u in C((0:ℂ),r), f (standardRootJoukowski τ δ u)/u) =
      Complex.I*(∫ θ in (0:ℝ)..(2*Real.pi), f (standardRootJoukowski τ δ (circleMap 0 r θ))) := by
    rw [circleIntegral,← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro θ _
    have hn : circleMap 0 r θ ≠ 0 := by
      apply norm_ne_zero_iff.mp
      simpa only [norm_circleMap_zero,abs_of_pos hr] using hr.ne'
    simp only [deriv_circleMap,smul_eq_mul]
    field_simp [hn]
  have hc : (∫ θ in (0:ℝ)..(2*Real.pi), f (standardRootJoukowski τ δ (circleMap 0 r θ))) =
      (2*Real.pi) • (∫ t in (0:ℝ)..1, f (standardRootEllipseMap τ δ r t)) := by
    symm
    simpa only [mul_zero,mul_one,standardRootEllipseMap] using
      intervalIntegral.smul_integral_comp_mul_left
        (f := fun θ => f (standardRootJoukowski τ δ (circleMap 0 r θ))) (a := 0) (b := 1) (2*Real.pi)
  rw [hi,hc]
  simp only [Complex.real_smul,Complex.ofReal_mul,Complex.ofReal_ofNat]
  ring

/-- Holomorphy on the image annulus makes the ellipse averages independent of radius. -/
theorem standardRootEllipse_average_eq (τ δ : ℂ) (U : Set ℂ) (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f U) (R : ℝ)
    (hU : ∀ u : ℂ, 1 ≤ ‖u‖ → ‖u‖ ≤ R → standardRootJoukowski τ δ u ∈ U)
    (r s : ℝ) (hr : 1 < r) (hs : 1 < s) (hrR : r ≤ R) (hsR : s ≤ R) :
    (∫ t in (0:ℝ)..1, f (standardRootEllipseMap τ δ r t)) =
      ∫ t in (0:ℝ)..1, f (standardRootEllipseMap τ δ s t) := by
  have hordered (r s : ℝ) (hr : 1 < r) (hrs : r ≤ s) (hsR : s ≤ R) :
      (∫ t in (0:ℝ)..1, f (standardRootEllipseMap τ δ r t)) =
        ∫ t in (0:ℝ)..1, f (standardRootEllipseMap τ δ s t) := by
    have hG : AnalyticOnNhd ℂ (fun u => f (standardRootJoukowski τ δ u)/u)
        (closedBall (0:ℂ) s \ ball (0:ℂ) r) := by
      intro u hu
      have huR : ‖u‖ ≤ R := (mem_closedBall_zero_iff.mp hu.1).trans hsR
      have hu1 : 1 < ‖u‖ := hr.trans_le (not_lt.mp (by simpa only [mem_ball_zero_iff] using hu.2))
      have hu0 : u ≠ 0 := by intro he; norm_num [he] at hu1
      exact ((hf _ (hU u hu1.le huR)).comp (standardRootJoukowski_analyticAt τ δ u hu0)).div
        analyticAt_id hu0
    have he := Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable
      (by linarith : 0 < r) hrs (s := ∅) countable_empty hG.continuousOn (by
        intro u hu
        exact (hG u ⟨ball_subset_closedBall hu.1.1,
          fun h => hu.1.2 (ball_subset_closedBall h)⟩).differentiableAt)
    rw [circleIntegral_joukowski_div τ δ s (by linarith),circleIntegral_joukowski_div τ δ r (by linarith)] at he
    exact (mul_left_cancel₀ (by simp [Real.pi_ne_zero] : (2*(Real.pi:ℂ)*Complex.I) ≠ 0) he).symm
  rcases le_total r s with hrs | hsr
  · exact hordered r s hr hrs hsR
  · exact (hordered s r hs hsr hrR).symm

/-- Local analyticity on the image annulus suffices for convergence of the averages. -/
theorem standardRootEllipse_average_tendsto (τ δ : ℂ) (U : Set ℂ) (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f U) (R : ℝ) (hR : 1 < R)
    (hU : ∀ u : ℂ, 1 ≤ ‖u‖ → ‖u‖ ≤ R → standardRootJoukowski τ δ u ∈ U) :
    Tendsto (fun r : ℝ => ∫ t in (0:ℝ)..1, f (standardRootEllipseMap τ δ r t))
      (𝓝[>] (1:ℝ)) (𝓝 (∫ t in (0:ℝ)..1, f (standardRootEllipseMap τ δ 1 t))) := by
  have hF : ContinuousOn (fun x : ℝ × ℝ => f (standardRootEllipseMap τ δ x.1 x.2))
      (Icc (1:ℝ) R ×ˢ Icc (0:ℝ) 1) := by
    intro x hx
    have hx0 : 0 < x.1 := lt_of_lt_of_le zero_lt_one hx.1.1
    have hn : ‖circleMap 0 x.1 ((2*Real.pi)*x.2)‖ = x.1 := by
      rw [norm_circleMap_zero,abs_of_pos hx0]
    have hm := hU (circleMap 0 x.1 ((2*Real.pi)*x.2)) (by rw [hn]; exact hx.1.1) (by rw [hn]; exact hx.1.2)
    have hc : ContinuousAt f (standardRootEllipseMap τ δ x.1 x.2) := (hf _ hm).continuousAt
    exact (hc.comp (f := fun y : ℝ × ℝ => standardRootEllipseMap τ δ y.1 y.2)
      (standardRootEllipseMap_continuousAt τ δ x.1 x.2 hx0)).continuousWithinAt
  have hUniform := (isCompact_Icc.prod isCompact_Icc).uniformContinuousOn_of_continuous hF
  have hlimU := hUniform.tendstoUniformlyOn
    (F := fun r t : ℝ => f (standardRootEllipseMap τ δ r t))
    (show (1:ℝ) ∈ Icc 1 R from ⟨le_rfl,hR.le⟩)
  have hcont : ∀ᶠ r in 𝓝[Icc (1:ℝ) R] (1:ℝ),
      ContinuousOn (fun t => f (standardRootEllipseMap τ δ r t)) (uIcc (0:ℝ) 1) := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    rw [uIcc_of_le zero_le_one]
    have hg : ContinuousOn (fun t : ℝ => (r,t)) (Icc (0:ℝ) 1) := by fun_prop
    exact hF.comp (f := fun t : ℝ => (r,t)) hg (fun t ht => ⟨hr,ht⟩)
  have hlim := TendstoUniformlyOn.tendsto_intervalIntegral_of_continuousOn
    (μ := volume) hcont (by simpa only [uIcc_of_le zero_le_one] using hlimU)
  rw [nhdsWithin_Icc_eq_nhdsGE hR] at hlim
  exact hlim.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)

/-- Each sufficiently small ellipse average equals the limiting gap average. -/
theorem standardRootEllipse_average_eq_gap (τ δ : ℂ) (U : Set ℂ) (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f U) (R : ℝ) (hR : 1 < R)
    (hU : ∀ u : ℂ, 1 ≤ ‖u‖ → ‖u‖ ≤ R → standardRootJoukowski τ δ u ∈ U)
    (r : ℝ) (hr : 1 < r) (hrR : r ≤ R) :
    (∫ t in (0:ℝ)..1, f (standardRootEllipseMap τ δ r t)) =
      ∫ t in (0:ℝ)..1, f (τ+δ*(Real.cos ((2*Real.pi)*t):ℂ)) := by
  have hlim := standardRootEllipse_average_tendsto τ δ U f hf R hR hU
  have he : (fun s : ℝ => ∫ t in (0:ℝ)..1, f (standardRootEllipseMap τ δ s t)) =ᶠ[𝓝[>] (1:ℝ)]
      (fun _ => ∫ t in (0:ℝ)..1, f (standardRootEllipseMap τ δ r t)) := by
    filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hR)] with s hs hsR
    exact standardRootEllipse_average_eq τ δ U f hf R hU s r hs hr hsR.le hrR
  have hlimr := (tendsto_const_nhds : Tendsto
    (fun _ : ℝ => ∫ t in (0:ℝ)..1, f (standardRootEllipseMap τ δ r t))
    (𝓝[>] (1:ℝ)) (𝓝 _)).congr' he.symm
  have h := tendsto_nhds_unique hlimr hlim
  simpa only [standardRootEllipseMap_radius_one] using h

/-- The local contour formula for every sufficiently small ellipse in an arbitrary gap neighborhood. -/
theorem exists_standardRootEllipse_local_period (τ δ : ℂ) (hδ : δ ≠ 0)
    (U : Set ℂ) (hU : IsOpen U) (hgap : standardRootGapSegment τ δ ⊆ U)
    (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f U) :
    ∃ R : ℝ, 1 < R ∧ ∀ r : ℝ, ∀ hr : 1 < r, r ≤ R →
      (standardRootEllipseLoop τ δ r (by linarith)).Inside (U \ standardRootGapSegment τ δ) ∧
      (standardRootEllipseLoop τ δ r (by linarith)).integral
          (fun z => f z/normalizedStandardRoot τ ((2*δ)^2) z) =
        (-(2*(Real.pi:ℂ))*Complex.I)*(∫ t in (0:ℝ)..1, f (τ+δ*(Real.cos ((2*Real.pi)*t):ℂ))) := by
  obtain ⟨R,hR,hann⟩ := exists_standardRootJoukowski_annulus_subset τ δ U hU hgap
  refine ⟨R,hR,fun r hr hrR => ⟨?_,?_⟩⟩
  · apply standardRootEllipseLoop_inside
    intro t ht
    refine ⟨?_,standardRootEllipseMap_not_mem_gap τ δ r t hδ hr⟩
    apply hann
    · simpa only [norm_circleMap_zero,abs_of_pos (by linarith : 0 < r)] using hr.le
    · simpa only [norm_circleMap_zero,abs_of_pos (by linarith : 0 < r)] using hrR
  · rw [standardRootEllipseLoop_weighted_integral τ δ r hr hδ f,
      standardRootEllipse_average_eq_gap τ δ U f hf R hR hann r hr hrR]

end NLS.ZakharovShabat
