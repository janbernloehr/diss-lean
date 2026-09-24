import NLS.ZakharovShabat.SourceCriticalRootRatioOuterArcs
import Mathlib.MeasureTheory.Integral.CircleIntegral

/-!
# Vanishing endpoint semicircle integrals

The quotient is at most of square-root order in the inverse radius on
both outward endpoint arcs. Multiplication by the circle-map derivative
contributes a factor of the radius, so both arc integrals are of order
of the square root of the radius and vanish as the contour collapses.
-/

noncomputable section
open Set Filter Topology Complex MeasureTheory intervalIntegral
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The angle-parametrized integral of the critical-root quotient over
an endpoint half-circle, with signed radius selecting its side. -/
def sourceCriticalRootRatio_endpointArcIntegral
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (c : ℂ) (R : ℝ) : ℂ :=
  ∫ θ in (-(Real.pi/2))..(Real.pi/2),
    deriv (circleMap c R) θ *
      (deriv (canonicalDiscriminant hp (periodOnePotential ψ))
          (circleMap c R θ) /
        sourceCanonicalRoot hp hp1 ψ (circleMap c R θ))

/-- Along any half-circle contained in the full root domain, the
critical-root quotient times the circle-map derivative is integrable. -/
theorem sourceCriticalRootRatio_endpointArc_intervalIntegrable
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (c : ℂ) (R : ℝ)
    (hdom : ∀ θ ∈ Icc (-(Real.pi/2)) (Real.pi/2),
      circleMap c R θ ∈ sourceCanonicalRootDomain hp hp1 ψ) :
    IntervalIntegrable
      (fun θ : ℝ => deriv (circleMap c R) θ *
        (deriv (canonicalDiscriminant hp (periodOnePotential ψ))
            (circleMap c R θ) /
          sourceCanonicalRoot hp hp1 ψ (circleMap c R θ)))
      volume (-(Real.pi/2)) (Real.pi/2) := by
  let q : ℂ → ℂ := fun z =>
    deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
      sourceCanonicalRoot hp hp1 ψ z
  have hq : ContinuousOn (fun θ : ℝ => q (circleMap c R θ))
      (Icc (-(Real.pi/2)) (Real.pi/2)) := by
    intro θ hθ
    exact ((sourceCriticalRootRatio_analyticOnNhd hp hp1 ψ _
      (hdom θ hθ)).continuousAt.comp
        (continuous_circleMap c R).continuousAt).continuousWithinAt
  have hderiv : Continuous (fun θ : ℝ => deriv (circleMap c R) θ) := by
    simp only [deriv_circleMap]
    fun_prop
  have hangle : -(Real.pi/2) ≤ Real.pi/2 := by
    linarith [Real.pi_pos]
  exact (hderiv.continuousOn.mul hq).intervalIntegrable_of_Icc hangle

/-- At a real-type source, both outward endpoint arc integrands are
integrable for every sufficiently small positive radius. -/
theorem exists_sourceCriticalRootRatio_outerArcs_intervalIntegrable
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ) :
    let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    ∃ ε : ℝ, 0 < ε ∧ ∀ ρ ∈ Ioc 0 ε,
      IntervalIntegrable
        (fun θ : ℝ => deriv (circleMap l (-ρ)) θ *
          (deriv (canonicalDiscriminant hp (periodOnePotential ψ))
              (circleMap l (-ρ) θ) /
            sourceCanonicalRoot hp hp1 ψ (circleMap l (-ρ) θ)))
        volume (-(Real.pi/2)) (Real.pi/2) ∧
      IntervalIntegrable
        (fun θ : ℝ => deriv (circleMap r ρ) θ *
          (deriv (canonicalDiscriminant hp (periodOnePotential ψ))
              (circleMap r ρ θ) /
            sourceCanonicalRoot hp hp1 ψ (circleMap r ρ θ)))
        volume (-(Real.pi/2)) (Real.pi/2) := by
  obtain ⟨ε,hε,hdom⟩ :=
    exists_sourceCriticalRootRatio_outerArcs_mem_domain hp hp1 ψ hreal n
  refine ⟨ε,hε,?_⟩
  intro ρ hρ
  exact ⟨sourceCriticalRootRatio_endpointArc_intervalIntegrable
      hp hp1 ψ _ (-ρ) (fun θ hθ => (hdom ρ hρ θ hθ).1),
    sourceCriticalRootRatio_endpointArc_intervalIntegrable
      hp hp1 ψ _ ρ (fun θ hθ => (hdom ρ hρ θ hθ).2)⟩

/-- A radius-weighted bound on a half-circle yields a square-root
bound for the angle-parametrized integral. -/
theorem endpointArcIntegral_norm_le_of_weighted_bound
    (f : ℂ → ℂ) (c : ℂ) (R ρ δ M : ℝ)
    (hρ : 0 < ρ) (hδ : 0 < δ) (hR : |R| = ρ)
    (hbound : ∀ θ ∈ Icc (-(Real.pi/2)) (Real.pi/2),
      ‖f (circleMap c R θ) * ((Real.sqrt (δ*ρ) : ℝ) : ℂ)‖ ≤ M) :
    ‖∫ θ in (-(Real.pi/2))..(Real.pi/2),
        deriv (circleMap c R) θ * f (circleMap c R θ)‖ ≤
      Real.pi * Real.sqrt ρ * (M / Real.sqrt δ) := by
  have hangle : -(Real.pi/2) ≤ Real.pi/2 := by
    linarith [Real.pi_pos]
  have hsqrtδ : 0 < Real.sqrt δ := Real.sqrt_pos.2 hδ
  have hsqrtρ : 0 ≤ Real.sqrt ρ := Real.sqrt_nonneg ρ
  have hpoint (θ : ℝ) (hθ : θ ∈ Icc (-(Real.pi/2)) (Real.pi/2)) :
      ‖deriv (circleMap c R) θ * f (circleMap c R θ)‖ ≤
        Real.sqrt ρ * (M / Real.sqrt δ) := by
    let q := f (circleMap c R θ)
    have hw : ‖q‖ * Real.sqrt (δ*ρ) ≤ M := by
      simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _)] using hbound θ hθ
    have hqsqrt : ‖q‖ * Real.sqrt ρ ≤ M / Real.sqrt δ := by
      apply (le_div_iff₀ hsqrtδ).2
      calc
        (‖q‖ * Real.sqrt ρ) * Real.sqrt δ =
            ‖q‖ * (Real.sqrt δ * Real.sqrt ρ) := by ring
        _ = ‖q‖ * Real.sqrt (δ*ρ) := by rw [Real.sqrt_mul hδ.le]
        _ ≤ M := hw
    have hderiv : ‖deriv (circleMap c R) θ‖ = ρ := by
      rw [deriv_circleMap, norm_mul, norm_circleMap_zero]
      simpa only [norm_I, mul_one] using hR
    calc
      ‖deriv (circleMap c R) θ * q‖ = ρ * ‖q‖ := by rw [norm_mul,hderiv]
      _ = Real.sqrt ρ * (‖q‖ * Real.sqrt ρ) := by
        calc
          ρ * ‖q‖ = (Real.sqrt ρ * Real.sqrt ρ) * ‖q‖ := by
            rw [Real.mul_self_sqrt hρ.le]
          _ = Real.sqrt ρ * (‖q‖ * Real.sqrt ρ) := by ring
      _ ≤ Real.sqrt ρ * (M / Real.sqrt δ) :=
        mul_le_mul_of_nonneg_left hqsqrt hsqrtρ
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := -(Real.pi/2)) (b := Real.pi/2)
    (f := fun θ => deriv (circleMap c R) θ * f (circleMap c R θ))
    (C := Real.sqrt ρ * (M / Real.sqrt δ)) (by
      intro θ hθ
      have hθ' : θ ∈ Ioc (-(Real.pi/2)) (Real.pi/2) := by
        simpa only [uIoc_of_le hangle] using hθ
      exact hpoint θ (Ioc_subset_Icc_self hθ'))
  have hlength : |Real.pi/2 - (-(Real.pi/2))| = Real.pi := by
    rw [abs_of_nonneg (by positivity)]
    ring
  calc
    ‖∫ θ in (-(Real.pi/2))..(Real.pi/2),
        deriv (circleMap c R) θ * f (circleMap c R θ)‖ ≤
      (Real.sqrt ρ * (M / Real.sqrt δ)) *
        |Real.pi/2 - (-(Real.pi/2))| := hint
    _ = Real.pi * Real.sqrt ρ * (M / Real.sqrt δ) := by
      rw [hlength]
      ring

/-- Both outward endpoint arcs have integrals bounded by one common
constant times the square root of their radius. -/
theorem exists_sourceCriticalRootRatio_outerArcIntegral_sqrt_bound
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re) :
    let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    ∃ ε C : ℝ, 0 < ε ∧ 0 < C ∧
      ∀ ρ ∈ Ioc 0 ε,
        ‖sourceCriticalRootRatio_endpointArcIntegral hp hp1 ψ l (-ρ)‖ ≤
          C * Real.sqrt ρ ∧
        ‖sourceCriticalRootRatio_endpointArcIntegral hp hp1 ψ r ρ‖ ≤
          C * Real.sqrt ρ := by
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let δ := (r.re-l.re)/2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  obtain ⟨ε,M,hε,hM,hbound⟩ :=
    exists_sourceCriticalRootRatio_outerArcs_weighted_bound
      hp hp1 ψ hreal n hopen
  let C := Real.pi * (M / Real.sqrt δ)
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨ε,C,hε,hC,?_⟩
  intro ρ hρ
  have hleft (θ : ℝ) (hθ : θ ∈ Icc (-(Real.pi/2)) (Real.pi/2)) :
      ‖(deriv (canonicalDiscriminant hp (periodOnePotential ψ))
          (circleMap l (-ρ) θ) /
        sourceCanonicalRoot hp hp1 ψ (circleMap l (-ρ) θ)) *
        ((Real.sqrt (δ*ρ) : ℝ) : ℂ)‖ ≤ M :=
    (hbound ρ hρ θ hθ).2.2.1
  have hright (θ : ℝ) (hθ : θ ∈ Icc (-(Real.pi/2)) (Real.pi/2)) :
      ‖(deriv (canonicalDiscriminant hp (periodOnePotential ψ))
          (circleMap r ρ θ) /
        sourceCanonicalRoot hp hp1 ψ (circleMap r ρ θ)) *
        ((Real.sqrt (δ*ρ) : ℝ) : ℂ)‖ ≤ M :=
    (hbound ρ hρ θ hθ).2.2.2
  have hl := endpointArcIntegral_norm_le_of_weighted_bound
    (fun z => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
      sourceCanonicalRoot hp hp1 ψ z) l (-ρ) ρ δ M hρ.1 hδ
      (by simp [abs_of_pos hρ.1]) hleft
  have hr := endpointArcIntegral_norm_le_of_weighted_bound
    (fun z => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
      sourceCanonicalRoot hp hp1 ψ z) r ρ ρ δ M hρ.1 hδ
      (abs_of_pos hρ.1) hright
  constructor
  · change ‖sourceCriticalRootRatio_endpointArcIntegral hp hp1 ψ l (-ρ)‖ ≤
      C * Real.sqrt ρ
    calc
      _ ≤ Real.pi * Real.sqrt ρ * (M / Real.sqrt δ) := hl
      _ = C * Real.sqrt ρ := by dsimp [C]; ring
  · change ‖sourceCriticalRootRatio_endpointArcIntegral hp hp1 ψ r ρ‖ ≤
      C * Real.sqrt ρ
    calc
      _ ≤ Real.pi * Real.sqrt ρ * (M / Real.sqrt δ) := hr
      _ = C * Real.sqrt ρ := by dsimp [C]; ring

/-- The two outer semicircle integrals vanish as the gap contour shrinks
onto its real branch cut. -/
theorem sourceCriticalRootRatio_outerArcIntegrals_tendsto_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re) :
    let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    Tendsto (fun ρ : ℝ =>
      sourceCriticalRootRatio_endpointArcIntegral hp hp1 ψ l (-ρ))
      (𝓝[Set.Ioi 0] (0:ℝ)) (𝓝 0) ∧
    Tendsto (fun ρ : ℝ =>
      sourceCriticalRootRatio_endpointArcIntegral hp hp1 ψ r ρ)
      (𝓝[Set.Ioi 0] (0:ℝ)) (𝓝 0) := by
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  obtain ⟨ε,C,hε,_,hbound⟩ :=
    exists_sourceCriticalRootRatio_outerArcIntegral_sqrt_bound
      hp hp1 ψ hreal n hopen
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
        ‖sourceCriticalRootRatio_endpointArcIntegral hp hp1 ψ l (-ρ)‖)
        (𝓝[Set.Ioi 0] (0:ℝ)) (𝓝 0) := by
      apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) ?_ hmajor
      filter_upwards [hpos,hsmall] with ρ hρ hρε
      exact (hbound ρ ⟨hρ,hρε.le⟩).1
    exact tendsto_iff_norm_sub_tendsto_zero.mpr (by simpa [l] using hnorm)
  · have hnorm : Tendsto (fun ρ : ℝ =>
        ‖sourceCriticalRootRatio_endpointArcIntegral hp hp1 ψ r ρ‖)
        (𝓝[Set.Ioi 0] (0:ℝ)) (𝓝 0) := by
      apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) ?_ hmajor
      filter_upwards [hpos,hsmall] with ρ hρ hρε
      exact (hbound ρ ⟨hρ,hρε.le⟩).2
    exact tendsto_iff_norm_sub_tendsto_zero.mpr (by simpa [r] using hnorm)

end NLS.ZakharovShabat
