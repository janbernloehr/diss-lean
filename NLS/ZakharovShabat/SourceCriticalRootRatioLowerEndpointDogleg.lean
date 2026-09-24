import NLS.ZakharovShabat.SourceCriticalRootRatioEndpointDoglegHeight

/-!
# Endpoint-to-endpoint paths below a real gap

The lower dogleg follows the same three-piece construction as the
upper dogleg, with negative crossing height. Its singular endpoint
segments remain curve-integrable, and its integral has a zero limit
as the crossing approaches the real axis from below.
-/

noncomputable section
open Set Filter Topology Complex
open scoped ENNReal unitInterval
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Positive `y` is the depth of this endpoint-to-endpoint path. -/
def sourceLowerGapDoglegPath
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (n : ℤ) (y : ℝ) :=
  sourceUpperGapDoglegPath hp hp1 ψ n (-y)

/-- The short lower doglegs are curve-integrable and split into
three oriented pieces. -/
theorem exists_sourceCriticalRootRatio_lowerDogleg_curveIntegrable_integral_eq
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
    ∃ ε : ℝ, 0 < ε ∧ ∀ y ∈ Ioo (0:ℝ) ε,
      CurveIntegrable
        (NLS.ComplexAnalysis.holomorphicOneForm
          (fun w => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) w /
            sourceCanonicalRoot hp hp1 ψ w))
        (sourceLowerGapDoglegPath hp hp1 ψ n y) ∧
      (∫ᶜ z in sourceLowerGapDoglegPath hp hp1 ψ n y,
        NLS.ComplexAnalysis.holomorphicOneForm
          (fun w => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) w /
            sourceCanonicalRoot hp hp1 ψ w) z) =
        (∫ᶜ z in Path.segment l (l+((-y:ℝ):ℂ)*Complex.I),
          NLS.ComplexAnalysis.holomorphicOneForm
            (fun w => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) w /
              sourceCanonicalRoot hp hp1 ψ w) z) +
        sourceCriticalRootRatio_horizontalIntegral hp hp1 ψ n (-y) -
        (∫ᶜ z in Path.segment r (r+((-y:ℝ):ℂ)*Complex.I),
          NLS.ComplexAnalysis.holomorphicOneForm
            (fun w => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) w /
              sourceCanonicalRoot hp hp1 ψ w) z) := by
  dsimp only
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let ω := NLS.ComplexAnalysis.holomorphicOneForm
    (fun w => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) w /
      sourceCanonicalRoot hp hp1 ψ w)
  obtain ⟨ε, hε, hvertical⟩ :=
    exists_sourceCriticalRootRatio_lowerEndpointSegment_curveIntegrable
      hp hp1 ψ hreal n hopen
  refine ⟨ε, hε, ?_⟩
  intro y hy
  have hleft : CurveIntegrable ω
      (Path.segment l (l+((-y:ℝ):ℂ)*Complex.I)) := by
    have h := hvertical (-1) (by simp) y hy
    rw [sourceCanonicalRootGapPoint_neg_one_eq_left hp hp1 ψ n] at h
    exact h
  have hright : CurveIntegrable ω
      (Path.segment r (r+((-y:ℝ):ℂ)*Complex.I)) := by
    have h := hvertical 1 (by simp) y hy
    rw [sourceCanonicalRootGapPoint_one_eq_right hp hp1 ψ n] at h
    exact h
  have hmid : CurveIntegrable ω
      (Path.segment (l+((-y:ℝ):ℂ)*Complex.I) (r+((-y:ℝ):ℂ)*Complex.I)) :=
    sourceCriticalRootRatio_horizontalSegment_curveIntegrable
      hp hp1 ψ hreal n (-y) (neg_ne_zero.2 (ne_of_gt hy.1))
  constructor
  · change CurveIntegrable ω
      (((Path.segment l (l+((-y:ℝ):ℂ)*Complex.I)).trans
        (Path.segment (l+((-y:ℝ):ℂ)*Complex.I)
          (r+((-y:ℝ):ℂ)*Complex.I))).trans
          (Path.segment r (r+((-y:ℝ):ℂ)*Complex.I)).symm)
    exact (hleft.trans hmid).trans hright.symm
  · change (∫ᶜ z in
      ((Path.segment l (l+((-y:ℝ):ℂ)*Complex.I)).trans
        (Path.segment (l+((-y:ℝ):ℂ)*Complex.I)
          (r+((-y:ℝ):ℂ)*Complex.I))).trans
          (Path.segment r (r+((-y:ℝ):ℂ)*Complex.I)).symm, ω z) = _
    rw [curveIntegral_trans (hleft.trans hmid) hright.symm,
      curveIntegral_trans hleft hmid, curveIntegral_symm,
      sourceCriticalRootRatio_horizontalSegment_curveIntegral_eq]
    ring

/-- The actual lower endpoint-to-endpoint dogleg integral tends to
zero as its depth shrinks. -/
theorem sourceCriticalRootRatio_lowerDogleg_curveIntegral_tendsto_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re) :
    Tendsto
      (fun y : ℝ => ∫ᶜ z in sourceLowerGapDoglegPath hp hp1 ψ n y,
        NLS.ComplexAnalysis.holomorphicOneForm
          (fun w => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) w /
            sourceCanonicalRoot hp hp1 ψ w) z)
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  obtain ⟨ε, hε, hdogleg⟩ :=
    exists_sourceCriticalRootRatio_lowerDogleg_curveIntegrable_integral_eq
      hp hp1 ψ hreal n hopen
  have hleft := sourceCriticalRootRatio_lowerEndpointSegment_curveIntegral_tendsto_zero
    hp hp1 ψ hreal n hopen (-1) (by simp)
  rw [sourceCanonicalRootGapPoint_neg_one_eq_left hp hp1 ψ n] at hleft
  have hright := sourceCriticalRootRatio_lowerEndpointSegment_curveIntegral_tendsto_zero
    hp hp1 ψ hreal n hopen 1 (by simp)
  rw [sourceCanonicalRootGapPoint_one_eq_right hp hp1 ψ n] at hright
  have hmid : Tendsto
      (fun y : ℝ => sourceCriticalRootRatio_horizontalIntegral hp hp1 ψ n (-y))
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
    simpa only [Function.comp_def, neg_zero] using (sourceCriticalRootRatio_horizontalIntegral_tendsto_zero_lower
      hp hp1 ψ hreal n hopen).comp tendsto_neg_nhdsGT_neg
  have hsum := (hleft.add hmid).sub hright
  have heq :
      (fun y : ℝ => ∫ᶜ z in sourceLowerGapDoglegPath hp hp1 ψ n y,
        NLS.ComplexAnalysis.holomorphicOneForm
          (fun w => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) w /
            sourceCanonicalRoot hp hp1 ψ w) z) =ᶠ[𝓝[>] (0:ℝ)]
      (fun y : ℝ =>
        (∫ᶜ z in Path.segment l (l+((-y:ℝ):ℂ)*Complex.I),
          NLS.ComplexAnalysis.holomorphicOneForm
            (fun w => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) w /
              sourceCanonicalRoot hp hp1 ψ w) z) +
        sourceCriticalRootRatio_horizontalIntegral hp hp1 ψ n (-y) -
        (∫ᶜ z in Path.segment r (r+((-y:ℝ):ℂ)*Complex.I),
          NLS.ComplexAnalysis.holomorphicOneForm
            (fun w => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) w /
              sourceCanonicalRoot hp hp1 ψ w) z)) := by
    filter_upwards [Ioo_mem_nhdsGT hε] with y hy
    exact (hdogleg y hy).2
  simpa using hsum.congr' heq.symm

end NLS.ZakharovShabat
