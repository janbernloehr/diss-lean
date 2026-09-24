import NLS.ZakharovShabat.SourceActionStadiumCircle
import NLS.ZakharovShabat.SourceCriticalRootRatioOuterArcIntegral

/-!
# Vanishing endpoint arcs for the weighted action integrand

The extra affine factor in the recentered action remains bounded on
the two shrinking outward semicircles. The quotient's square-root arc
bound therefore still forces both weighted arc integrals to zero.
-/

noncomputable section
open Set Filter Topology Complex MeasureTheory intervalIntegral
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The angle-parametrized endpoint arc integral for the recentered
action integrand. -/
def sourceAction_endpointArcIntegral
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (q c : ℂ) (R : ℝ) : ℂ :=
  ∫ θ in (-(Real.pi/2))..(Real.pi/2),
    deriv (circleMap c R) θ *
      ((circleMap c R θ-q) *
        sourceCriticalRootRatioJoint hp hp1 (circleMap c R θ,ψ))

/-- The weighted angle integral is the curve integral of the bundled
endpoint semicircle path. -/
theorem sourceAction_endpointArc_curveIntegral_eq
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (q c : ℂ) (R : ℝ) :
    (∫ᶜ z in sourceEndpointSemicirclePath c R,
      NLS.ComplexAnalysis.holomorphicOneForm
        (fun w => (w-q) * sourceCriticalRootRatioJoint hp hp1 (w,ψ)) z) =
      sourceAction_endpointArcIntegral hp hp1 ψ q c R := by
  exact curveIntegral_sourceEndpointSemicirclePath _ c R

/-- On either endpoint arc, the recentering factor is bounded by its
value at the center plus the arc radius. -/
private theorem action_arc_weight_norm_le
    (q c : ℂ) (R ρ : ℝ) (hR : |R| = ρ) (θ : ℝ) :
    ‖circleMap c R θ-q‖ ≤ ‖c-q‖+ρ := by
  have hdist : ‖circleMap c R θ-c‖ = ρ := by
    rw [circleMap_sub_center,norm_circleMap_zero]
    exact hR
  calc
    ‖circleMap c R θ-q‖ =
        ‖(circleMap c R θ-c)+(c-q)‖ := by congr 1; ring
    _ ≤ ‖circleMap c R θ-c‖+‖c-q‖ := norm_add_le _ _
    _ = ‖c-q‖+ρ := by rw [hdist]; ring

/-- Both recentered action endpoint arcs have a common square-root
integral bound for all sufficiently small positive radii. -/
theorem exists_sourceAction_outerArcIntegral_sqrt_bound
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re)
    (q : ℂ) :
    let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    ∃ ε C : ℝ, 0 < ε ∧ 0 < C ∧
      ∀ ρ ∈ Ioc 0 ε,
        ‖sourceAction_endpointArcIntegral hp hp1 ψ q l (-ρ)‖ ≤
          C * Real.sqrt ρ ∧
        ‖sourceAction_endpointArcIntegral hp hp1 ψ q r ρ‖ ≤
          C * Real.sqrt ρ := by
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let d := (r.re-l.re)/2
  have hd : 0 < d := by dsimp [d]; linarith
  obtain ⟨ε,M,hε,hM,hbound⟩ :=
    exists_sourceCriticalRootRatio_outerArcs_weighted_bound
      hp hp1 ψ hreal n hopen
  let B := ‖l-q‖+‖r-q‖+ε+1
  have hB : 0 < B := by dsimp [B]; positivity
  let C := Real.pi * (B*M/Real.sqrt d)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨ε,C,hε,hC,?_⟩
  intro ρ hρ
  let Q : ℂ → ℂ := fun z =>
    sourceCriticalRootRatioJoint hp hp1 (z,ψ)
  have hleft (θ : ℝ) (hθ : θ ∈ Icc (-(Real.pi/2)) (Real.pi/2)) :
      ‖((circleMap l (-ρ) θ-q) * Q (circleMap l (-ρ) θ)) *
        ((Real.sqrt (d*ρ):ℝ):ℂ)‖ ≤ B*M := by
    let z := circleMap l (-ρ) θ
    have hq : ‖Q z * ((Real.sqrt (d*ρ):ℝ):ℂ)‖ ≤ M :=
      (hbound ρ hρ θ hθ).2.2.1
    have hwt : ‖z-q‖ ≤ B := by
      have h := action_arc_weight_norm_le q l (-ρ) ρ
        (by simp [abs_of_pos hρ.1]) θ
      change ‖circleMap l (-ρ) θ-q‖ ≤ B
      dsimp [B]
      linarith [norm_nonneg (r-q), hρ.2, hε]
    calc
      _ = ‖z-q‖ * ‖Q z * ((Real.sqrt (d*ρ):ℝ):ℂ)‖ := by
        change ‖((z-q)*Q z)*((Real.sqrt (d*ρ):ℝ):ℂ)‖ = _
        simp only [mul_assoc,norm_mul]
      _ ≤ B * ‖Q z * ((Real.sqrt (d*ρ):ℝ):ℂ)‖ :=
        mul_le_mul_of_nonneg_right hwt (norm_nonneg _)
      _ ≤ B*M := mul_le_mul_of_nonneg_left hq hB.le
  have hright (θ : ℝ) (hθ : θ ∈ Icc (-(Real.pi/2)) (Real.pi/2)) :
      ‖((circleMap r ρ θ-q) * Q (circleMap r ρ θ)) *
        ((Real.sqrt (d*ρ):ℝ):ℂ)‖ ≤ B*M := by
    let z := circleMap r ρ θ
    have hq : ‖Q z * ((Real.sqrt (d*ρ):ℝ):ℂ)‖ ≤ M :=
      (hbound ρ hρ θ hθ).2.2.2
    have hwt : ‖z-q‖ ≤ B := by
      have h := action_arc_weight_norm_le q r ρ ρ
        (abs_of_pos hρ.1) θ
      change ‖circleMap r ρ θ-q‖ ≤ B
      dsimp [B]
      linarith [norm_nonneg (l-q), hρ.2, hε]
    calc
      _ = ‖z-q‖ * ‖Q z * ((Real.sqrt (d*ρ):ℝ):ℂ)‖ := by
        change ‖((z-q)*Q z)*((Real.sqrt (d*ρ):ℝ):ℂ)‖ = _
        simp only [mul_assoc,norm_mul]
      _ ≤ B * ‖Q z * ((Real.sqrt (d*ρ):ℝ):ℂ)‖ :=
        mul_le_mul_of_nonneg_right hwt (norm_nonneg _)
      _ ≤ B*M := mul_le_mul_of_nonneg_left hq hB.le
  have hl := endpointArcIntegral_norm_le_of_weighted_bound
    (fun z => (z-q)*Q z) l (-ρ) ρ d (B*M) hρ.1 hd
      (by simp [abs_of_pos hρ.1]) hleft
  have hr := endpointArcIntegral_norm_le_of_weighted_bound
    (fun z => (z-q)*Q z) r ρ ρ d (B*M) hρ.1 hd
      (abs_of_pos hρ.1) hright
  constructor
  · change ‖sourceAction_endpointArcIntegral hp hp1 ψ q l (-ρ)‖ ≤
      C * Real.sqrt ρ
    calc
      _ ≤ Real.pi * Real.sqrt ρ * (B*M/Real.sqrt d) := hl
      _ = C * Real.sqrt ρ := by dsimp [C]; ring
  · change ‖sourceAction_endpointArcIntegral hp hp1 ψ q r ρ‖ ≤
      C * Real.sqrt ρ
    calc
      _ ≤ Real.pi * Real.sqrt ρ * (B*M/Real.sqrt d) := hr
      _ = C * Real.sqrt ρ := by dsimp [C]; ring

/-- The two weighted outward endpoint arc integrals vanish as the
stadium shrinks onto the real gap. -/
theorem sourceAction_outerArcIntegrals_tendsto_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re)
    (q : ℂ) :
    let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    Tendsto (fun ρ : ℝ =>
      sourceAction_endpointArcIntegral hp hp1 ψ q l (-ρ))
      (𝓝[Set.Ioi 0] (0:ℝ)) (𝓝 0) ∧
    Tendsto (fun ρ : ℝ =>
      sourceAction_endpointArcIntegral hp hp1 ψ q r ρ)
      (𝓝[Set.Ioi 0] (0:ℝ)) (𝓝 0) := by
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  obtain ⟨ε,C,hε,_,hbound⟩ :=
    exists_sourceAction_outerArcIntegral_sqrt_bound
      hp hp1 ψ hreal n hopen q
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
        ‖sourceAction_endpointArcIntegral hp hp1 ψ q l (-ρ)‖)
        (𝓝[Set.Ioi 0] (0:ℝ)) (𝓝 0) := by
      apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) ?_ hmajor
      filter_upwards [hpos,hsmall] with ρ hρ hρε
      exact (hbound ρ ⟨hρ,hρε.le⟩).1
    exact tendsto_iff_norm_sub_tendsto_zero.mpr (by simpa [l] using hnorm)
  · have hnorm : Tendsto (fun ρ : ℝ =>
        ‖sourceAction_endpointArcIntegral hp hp1 ψ q r ρ‖)
        (𝓝[Set.Ioi 0] (0:ℝ)) (𝓝 0) := by
      apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) ?_ hmajor
      filter_upwards [hpos,hsmall] with ρ hρ hρε
      exact (hbound ρ ⟨hρ,hρε.le⟩).2
    exact tendsto_iff_norm_sub_tendsto_zero.mpr (by simpa [r] using hnorm)

end NLS.ZakharovShabat
