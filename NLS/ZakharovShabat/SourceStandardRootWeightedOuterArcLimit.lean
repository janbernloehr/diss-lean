import NLS.ZakharovShabat.SourceStandardRootWeightedStadium
import NLS.ZakharovShabat.SourceStandardRootEndpointCircleBound
import NLS.ZakharovShabat.SourceCriticalRootRatioOuterArcIntegral

/-!
# Vanishing weighted endpoint arcs of the standard-root stadium

Near either endpoint of an open real gap, the standard root has
square-root size. A numerator continuous at the endpoints is locally
bounded, so each outward semicircle integral is `O(√ρ)`.
-/

noncomputable section
open Set Metric Filter Topology Complex MeasureTheory intervalIntegral
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The angle-parametrized weighted inverse-root integral on an
outward endpoint semicircle. -/
def sourceStandardRoot_weighted_endpointArcIntegral
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n : ℤ) (g : ℂ → ℂ) (c : ℂ) (R : ℝ) : ℂ :=
  ∫ θ in (-(Real.pi/2))..(Real.pi/2),
    deriv (circleMap c R) θ *
      (g (circleMap c R θ) /
        sourceStandardRoot hp hp1 ψ n (circleMap c R θ))

/-- The angle integral is the curve integral of the bundled endpoint
semicircle path. -/
theorem sourceStandardRoot_weighted_endpointArc_curveIntegral_eq
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n : ℤ) (g : ℂ → ℂ) (c : ℂ) (R : ℝ) :
    (∫ᶜ z in sourceEndpointSemicirclePath c R,
      NLS.ComplexAnalysis.holomorphicOneForm
        (fun w => g w / sourceStandardRoot hp hp1 ψ n w) z) =
      sourceStandardRoot_weighted_endpointArcIntegral hp hp1 ψ n g c R := by
  exact curveIntegral_sourceEndpointSemicirclePath _ c R

/-- On one small outward endpoint semicircle, a bound for the
numerator gives a square-root bound for the arc integral. -/
theorem sourceStandardRoot_weighted_endpointArc_norm_le
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re)
    (g : ℂ → ℂ) (c : ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (hc : c = canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n ∨
      c = canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n)
    (R : ℝ) (hR : |R| = ρ)
    (hρsmall : ρ ≤
      ((canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re -
        (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
          (periodOnePotential_mem ψ) n).re)/2)
    (havoid : ∀ θ ∈ Icc (-(Real.pi/2)) (Real.pi/2),
      circleMap c R θ ∉ sourcePeriodicSegment hp hp1 ψ n)
    (M : ℝ) (hM : 0 ≤ M)
    (hg : ∀ θ ∈ Icc (-(Real.pi/2)) (Real.pi/2),
      ‖g (circleMap c R θ)‖ ≤ M) :
    ‖sourceStandardRoot_weighted_endpointArcIntegral hp hp1 ψ n g c R‖ ≤
      Real.pi * Real.sqrt ρ *
        (M / Real.sqrt
          (((canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
            (periodOnePotential_mem ψ) n).re -
            (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
              (periodOnePotential_mem ψ) n).re)/2)) := by
  let d := ((canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n).re -
      (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re)/2
  have hd : 0 < d := by
    change 0 < ((canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re -
      (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re)/2
    exact div_pos (sub_pos.mpr hopen) (by norm_num)
  have hweighted (θ : ℝ) (hθ : θ ∈ Icc (-(Real.pi/2)) (Real.pi/2)) :
      ‖(g (circleMap c R θ) /
          sourceStandardRoot hp hp1 ψ n (circleMap c R θ)) *
        (((Real.sqrt (d*ρ)):ℝ):ℂ)‖ ≤ M := by
    let z := circleMap c R θ
    let w := sourceStandardRoot hp hp1 ψ n z
    have hz : z ∉ sourcePeriodicSegment hp hp1 ψ n := havoid θ hθ
    have hwne : w ≠ 0 :=
      sourceStandardRoot_ne_zero_off_segment hp hp1 ψ n z hz
    have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hwne
    have hdist : ‖c-z‖ = ρ := by
      rw [norm_sub_rev,circleMap_sub_center,norm_circleMap_zero]
      exact hR
    have hroot : Real.sqrt (d*ρ) ≤ ‖w‖ := by
      rcases hc with hl | hr
      · subst c
        exact sourceStandardRoot_leftEndpoint_circle_norm_lower_bound
          hp hp1 ψ n hopen ρ hρ.le hρsmall z hz hdist
      · subst c
        exact sourceStandardRoot_rightEndpoint_circle_norm_lower_bound
          hp hp1 ψ n hopen ρ hρ.le hρsmall z hz hdist
    have hsqrt : 0 ≤ Real.sqrt (d*ρ) := Real.sqrt_nonneg _
    calc
      ‖(g z / w) * (((Real.sqrt (d*ρ)):ℝ):ℂ)‖ =
          ‖g z‖ * Real.sqrt (d*ρ) / ‖w‖ := by
            rw [norm_mul,norm_div,Complex.norm_real,Real.norm_eq_abs,
              abs_of_nonneg hsqrt]
            ring
      _ ≤ M := by
        apply (div_le_iff₀ hwpos).2
        calc
          ‖g z‖ * Real.sqrt (d*ρ) ≤ M * Real.sqrt (d*ρ) :=
            mul_le_mul_of_nonneg_right (hg θ hθ) hsqrt
          _ ≤ M * ‖w‖ := mul_le_mul_of_nonneg_left hroot hM
  exact endpointArcIntegral_norm_le_of_weighted_bound
    (fun z => g z / sourceStandardRoot hp hp1 ψ n z)
    c R ρ d M hρ hd hR hweighted

/-- Endpoint continuity supplies a common `O(√ρ)` bound on the two
outward arcs of a real open gap. -/
theorem exists_sourceStandardRoot_weighted_outerArc_sqrt_bound
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re)
    (g : ℂ → ℂ)
    (hgl : ContinuousAt g (canonicalPeriodicLeft hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ) n))
    (hgr : ContinuousAt g (canonicalPeriodicRight hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ) n)) :
    let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    ∃ ε C : ℝ, 0 < ε ∧ 0 < C ∧
      ∀ ρ ∈ Ioc 0 ε,
        ‖sourceStandardRoot_weighted_endpointArcIntegral
          hp hp1 ψ n g l (-ρ)‖ ≤ C * Real.sqrt ρ ∧
        ‖sourceStandardRoot_weighted_endpointArcIntegral
          hp hp1 ψ n g r ρ‖ ≤ C * Real.sqrt ρ := by
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let d := (r.re-l.re)/2
  have hd : 0 < d := by dsimp [d]; linarith
  obtain ⟨ε₀,hε₀,hdom⟩ :=
    exists_sourceCriticalRootRatio_outerArcs_mem_domain hp hp1 ψ hreal n
  obtain ⟨εl,hεl,hballl⟩ := Metric.mem_nhds_iff.mp
    (hgl (ball_mem_nhds (g l) (by norm_num : (0:ℝ) < 1)))
  obtain ⟨εr,hεr,hballr⟩ := Metric.mem_nhds_iff.mp
    (hgr (ball_mem_nhds (g r) (by norm_num : (0:ℝ) < 1)))
  let ε := min (ε₀/2) (min (εl/2) (min (εr/2) d))
  have hε : 0 < ε :=
    lt_min (by positivity) (lt_min (by positivity) (lt_min (by positivity) hd))
  let M := max ‖g l‖ ‖g r‖ + 1
  have hM : 0 < M := by dsimp [M]; positivity
  let C := Real.pi * (M / Real.sqrt d)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨ε,C,hε,hC,?_⟩
  intro ρ hρ
  have hρ₀ : ρ ∈ Ioc 0 ε₀ :=
    ⟨hρ.1,by
      have h := hρ.2.trans (min_le_left _ _)
      linarith⟩
  have hρl : ρ < εl := by
    have h := hρ.2.trans ((min_le_right _ _).trans (min_le_left _ _))
    linarith
  have hρr : ρ < εr := by
    have h := hρ.2.trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
    linarith
  have hρd : ρ ≤ d :=
    hρ.2.trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _)))
  have hleftbound (θ : ℝ)
      (hθ : θ ∈ Icc (-(Real.pi/2)) (Real.pi/2)) :
      ‖g (circleMap l (-ρ) θ)‖ ≤ M := by
    have hdist : dist (circleMap l (-ρ) θ) l = ρ := by
      rw [dist_eq_norm,circleMap_sub_center,norm_circleMap_zero]
      simp [abs_of_pos hρ.1]
    have hnear : circleMap l (-ρ) θ ∈ ball l εl := by
      exact mem_ball.mpr (by simpa only [hdist] using hρl)
    have hval : ‖g (circleMap l (-ρ) θ)-g l‖ < 1 := by
      simpa only [Set.mem_preimage,mem_ball,dist_eq_norm] using hballl hnear
    have hmax : ‖g l‖ ≤ max ‖g l‖ ‖g r‖ := le_max_left _ _
    exact (norm_le_norm_sub_add _ _).trans (by dsimp [M]; linarith)
  have hrightbound (θ : ℝ)
      (hθ : θ ∈ Icc (-(Real.pi/2)) (Real.pi/2)) :
      ‖g (circleMap r ρ θ)‖ ≤ M := by
    have hdist : dist (circleMap r ρ θ) r = ρ := by
      rw [dist_eq_norm,circleMap_sub_center,norm_circleMap_zero]
      exact abs_of_pos hρ.1
    have hnear : circleMap r ρ θ ∈ ball r εr := by
      exact mem_ball.mpr (by simpa only [hdist] using hρr)
    have hval : ‖g (circleMap r ρ θ)-g r‖ < 1 := by
      simpa only [Set.mem_preimage,mem_ball,dist_eq_norm] using hballr hnear
    have hmax : ‖g r‖ ≤ max ‖g l‖ ‖g r‖ := le_max_right _ _
    exact (norm_le_norm_sub_add _ _).trans (by dsimp [M]; linarith)
  have hl := sourceStandardRoot_weighted_endpointArc_norm_le
    hp hp1 ψ n hopen g l ρ hρ.1 (Or.inl rfl) (-ρ)
      (by simp [abs_of_pos hρ.1]) hρd
      (fun θ hθ => (hdom ρ hρ₀ θ hθ).1 n) M hM.le hleftbound
  have hr := sourceStandardRoot_weighted_endpointArc_norm_le
    hp hp1 ψ n hopen g r ρ hρ.1 (Or.inr rfl) ρ
      (abs_of_pos hρ.1) hρd
      (fun θ hθ => (hdom ρ hρ₀ θ hθ).2 n) M hM.le hrightbound
  constructor
  · calc
      _ ≤ Real.pi * Real.sqrt ρ * (M / Real.sqrt d) := hl
      _ = C * Real.sqrt ρ := by dsimp [C]; ring
  · calc
      _ ≤ Real.pi * Real.sqrt ρ * (M / Real.sqrt d) := hr
      _ = C * Real.sqrt ρ := by dsimp [C]; ring

/-- Both weighted outward endpoint semicircle integrals vanish as
the stadium shrinks onto the selected real gap. -/
theorem sourceStandardRoot_weighted_outerArcIntegrals_tendsto_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re)
    (g : ℂ → ℂ)
    (hgl : ContinuousAt g (canonicalPeriodicLeft hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ) n))
    (hgr : ContinuousAt g (canonicalPeriodicRight hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ) n)) :
    let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    Tendsto (fun ρ : ℝ =>
      sourceStandardRoot_weighted_endpointArcIntegral hp hp1 ψ n g l (-ρ))
      (𝓝[Set.Ioi 0] (0:ℝ)) (𝓝 0) ∧
    Tendsto (fun ρ : ℝ =>
      sourceStandardRoot_weighted_endpointArcIntegral hp hp1 ψ n g r ρ)
      (𝓝[Set.Ioi 0] (0:ℝ)) (𝓝 0) := by
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  obtain ⟨ε,C,hε,_,hbound⟩ :=
    exists_sourceStandardRoot_weighted_outerArc_sqrt_bound
      hp hp1 ψ hreal n hopen g hgl hgr
  have hsmall0 : ∀ᶠ ρ in 𝓝 (0:ℝ), ρ < ε := Iio_mem_nhds hε
  have hsmall : ∀ᶠ ρ in 𝓝[Set.Ioi 0] (0:ℝ), ρ < ε :=
    hsmall0.filter_mono nhdsWithin_le_nhds
  have hpos : ∀ᶠ ρ in 𝓝[Set.Ioi 0] (0:ℝ), 0 < ρ :=
    self_mem_nhdsWithin
  have hsqrt : Tendsto (fun ρ : ℝ => Real.sqrt ρ)
      (𝓝[Set.Ioi 0] (0:ℝ)) (𝓝 0) := by
    simpa using (Real.continuous_sqrt.tendsto (0:ℝ)).mono_left
      nhdsWithin_le_nhds
  have hmajor : Tendsto (fun ρ : ℝ => C * Real.sqrt ρ)
      (𝓝[Set.Ioi 0] (0:ℝ)) (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hsqrt
  constructor
  · have hnorm : Tendsto (fun ρ : ℝ =>
        ‖sourceStandardRoot_weighted_endpointArcIntegral
          hp hp1 ψ n g l (-ρ)‖)
        (𝓝[Set.Ioi 0] (0:ℝ)) (𝓝 0) := by
      apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) ?_ hmajor
      filter_upwards [hpos,hsmall] with ρ hρ hρε
      exact (hbound ρ ⟨hρ,hρε.le⟩).1
    exact tendsto_iff_norm_sub_tendsto_zero.mpr (by simpa [l] using hnorm)
  · have hnorm : Tendsto (fun ρ : ℝ =>
        ‖sourceStandardRoot_weighted_endpointArcIntegral
          hp hp1 ψ n g r ρ‖)
        (𝓝[Set.Ioi 0] (0:ℝ)) (𝓝 0) := by
      apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) ?_ hmajor
      filter_upwards [hpos,hsmall] with ρ hρ hρε
      exact (hbound ρ ⟨hρ,hρε.le⟩).2
    exact tendsto_iff_norm_sub_tendsto_zero.mpr (by simpa [r] using hnorm)

end NLS.ZakharovShabat
