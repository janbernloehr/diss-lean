import NLS.ZakharovShabat.SourceCriticalRootRatioEndpointSegmentIntegral
import NLS.ZakharovShabat.SourceCriticalRootRatioStadiumIntegral
import NLS.ZakharovShabat.SourceCriticalRootRatioHorizontalLimit

/-!
# Endpoint-to-endpoint paths above a real gap

The dogleg starts at the left branch point, travels vertically into
the upper half-plane, crosses above the gap, and descends to the right
branch point. Its three parts are curve-integrable for small positive
heights, and its integral tends to zero as the height shrinks.
-/

noncomputable section
open Set Filter Topology Complex
open scoped ENNReal unitInterval
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The straight crossing between vertically shifted endpoints is
curve-integrable for every nonzero shift of a real-type gap. -/
theorem sourceCriticalRootRatio_horizontalSegment_curveIntegrable
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ) (y : ℝ) (hy : y ≠ 0) :
    let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    CurveIntegrable
      (NLS.ComplexAnalysis.holomorphicOneForm
        (fun w => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) w /
          sourceCanonicalRoot hp hp1 ψ w))
      (Path.segment (l+(y:ℂ)*Complex.I) (r+(y:ℂ)*Complex.I)) := by
  dsimp only
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  have hline (u : ℝ) :
      AffineMap.lineMap (l+(y:ℂ)*Complex.I) (r+(y:ℂ)*Complex.I) u =
        sourceCanonicalRootGapPoint hp hp1 ψ n (2*u-1)+(y:ℂ)*Complex.I := by
    rw [AffineMap.lineMap_apply_module']
    change u • ((r+(y:ℂ)*Complex.I)-(l+(y:ℂ)*Complex.I)) +
      (l+(y:ℂ)*Complex.I) =
      (l+r)/2 + (r-l)/2 * ((2*u-1:ℝ):ℂ) + (y:ℂ)*Complex.I
    simp only [Complex.real_smul]
    push_cast
    ring
  have hq := sourceCriticalRootRatio_vertical_continuous
    hp hp1 ψ hreal n y hy
  have hparam : Continuous (fun u : ℝ => (2*u-1:ℝ)) := by fun_prop
  have hcont : Continuous (fun u : ℝ =>
      (NLS.ComplexAnalysis.holomorphicOneForm
        (fun w => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) w /
          sourceCanonicalRoot hp hp1 ψ w)
        (AffineMap.lineMap (l+(y:ℂ)*Complex.I) (r+(y:ℂ)*Complex.I) u))
          ((r+(y:ℂ)*Complex.I)-(l+(y:ℂ)*Complex.I))) := by
    have hqparam := hq.comp hparam
    convert hqparam.mul (continuous_const : Continuous (fun _ : ℝ => r-l)) using 1
    ext u
    simp only [NLS.ComplexAnalysis.holomorphicOneForm_apply, hline]
    congr 1
    ring
  rw [curveIntegrable_segment]
  exact hcont.intervalIntegrable _ _

/-- A three-piece path from the actual left branch point to the right
one, crossing at positive height `y`. -/
def sourceUpperGapDoglegPath
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (n : ℤ) (y : ℝ) :
    let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    Path l r := by
  dsimp only
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  exact ((Path.segment l (l+(y:ℂ)*Complex.I)).trans
    (Path.segment (l+(y:ℂ)*Complex.I) (r+(y:ℂ)*Complex.I))).trans
      (Path.segment r (r+(y:ℂ)*Complex.I)).symm

/-- Every sufficiently short upper dogleg is curve-integrable, and
its integral is the sum of the two endpoint pieces and the shifted
horizontal crossing. -/
theorem exists_sourceCriticalRootRatio_upperDogleg_curveIntegrable_integral_eq
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
        (sourceUpperGapDoglegPath hp hp1 ψ n y) ∧
      (∫ᶜ z in sourceUpperGapDoglegPath hp hp1 ψ n y,
        NLS.ComplexAnalysis.holomorphicOneForm
          (fun w => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) w /
            sourceCanonicalRoot hp hp1 ψ w) z) =
        (∫ᶜ z in Path.segment l (l+(y:ℂ)*Complex.I),
          NLS.ComplexAnalysis.holomorphicOneForm
            (fun w => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) w /
              sourceCanonicalRoot hp hp1 ψ w) z) +
        sourceCriticalRootRatio_horizontalIntegral hp hp1 ψ n y -
        (∫ᶜ z in Path.segment r (r+(y:ℂ)*Complex.I),
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
    exists_sourceCriticalRootRatio_upperEndpointSegment_curveIntegrable
      hp hp1 ψ hreal n hopen
  refine ⟨ε, hε, ?_⟩
  intro y hy
  have hleft : CurveIntegrable ω (Path.segment l (l+(y:ℂ)*Complex.I)) := by
    have h := hvertical (-1) (by simp) y hy
    rw [sourceCanonicalRootGapPoint_neg_one_eq_left hp hp1 ψ n] at h
    exact h
  have hright : CurveIntegrable ω (Path.segment r (r+(y:ℂ)*Complex.I)) := by
    have h := hvertical 1 (by simp) y hy
    rw [sourceCanonicalRootGapPoint_one_eq_right hp hp1 ψ n] at h
    exact h
  have hmid : CurveIntegrable ω
      (Path.segment (l+(y:ℂ)*Complex.I) (r+(y:ℂ)*Complex.I)) :=
    sourceCriticalRootRatio_horizontalSegment_curveIntegrable
      hp hp1 ψ hreal n y (ne_of_gt hy.1)
  constructor
  · change CurveIntegrable ω
      (((Path.segment l (l+(y:ℂ)*Complex.I)).trans
        (Path.segment (l+(y:ℂ)*Complex.I) (r+(y:ℂ)*Complex.I))).trans
          (Path.segment r (r+(y:ℂ)*Complex.I)).symm)
    exact (hleft.trans hmid).trans hright.symm
  · change (∫ᶜ z in
      ((Path.segment l (l+(y:ℂ)*Complex.I)).trans
        (Path.segment (l+(y:ℂ)*Complex.I) (r+(y:ℂ)*Complex.I))).trans
          (Path.segment r (r+(y:ℂ)*Complex.I)).symm, ω z) = _
    rw [curveIntegral_trans (hleft.trans hmid) hright.symm,
      curveIntegral_trans hleft hmid, curveIntegral_symm,
      sourceCriticalRootRatio_horizontalSegment_curveIntegral_eq]
    ring

/-- The actual endpoint-to-endpoint dogleg integral tends to zero as
the upper crossing approaches the real gap. -/
theorem sourceCriticalRootRatio_upperDogleg_curveIntegral_tendsto_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re) :
    Tendsto
      (fun y : ℝ => ∫ᶜ z in sourceUpperGapDoglegPath hp hp1 ψ n y,
        NLS.ComplexAnalysis.holomorphicOneForm
          (fun w => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) w /
            sourceCanonicalRoot hp hp1 ψ w) z)
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  obtain ⟨ε, hε, hdogleg⟩ :=
    exists_sourceCriticalRootRatio_upperDogleg_curveIntegrable_integral_eq
      hp hp1 ψ hreal n hopen
  have hleft := sourceCriticalRootRatio_upperEndpointSegment_curveIntegral_tendsto_zero
    hp hp1 ψ hreal n hopen (-1) (by simp)
  rw [sourceCanonicalRootGapPoint_neg_one_eq_left hp hp1 ψ n] at hleft
  have hright := sourceCriticalRootRatio_upperEndpointSegment_curveIntegral_tendsto_zero
    hp hp1 ψ hreal n hopen 1 (by simp)
  rw [sourceCanonicalRootGapPoint_one_eq_right hp hp1 ψ n] at hright
  have hmid := sourceCriticalRootRatio_horizontalIntegral_tendsto_zero_upper
    hp hp1 ψ hreal n hopen
  have hsum := (hleft.add hmid).sub hright
  have heq :
      (fun y : ℝ => ∫ᶜ z in sourceUpperGapDoglegPath hp hp1 ψ n y,
        NLS.ComplexAnalysis.holomorphicOneForm
          (fun w => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) w /
            sourceCanonicalRoot hp hp1 ψ w) z) =ᶠ[𝓝[>] (0:ℝ)]
      (fun y : ℝ =>
        (∫ᶜ z in Path.segment l (l+(y:ℂ)*Complex.I),
          NLS.ComplexAnalysis.holomorphicOneForm
            (fun w => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) w /
              sourceCanonicalRoot hp hp1 ψ w) z) +
        sourceCriticalRootRatio_horizontalIntegral hp hp1 ψ n y -
        (∫ᶜ z in Path.segment r (r+(y:ℂ)*Complex.I),
          NLS.ComplexAnalysis.holomorphicOneForm
            (fun w => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) w /
              sourceCanonicalRoot hp hp1 ψ w) z)) := by
    filter_upwards [Ioo_mem_nhdsGT hε] with y hy
    exact (hdogleg y hy).2
  simpa using hsum.congr' heq.symm

end NLS.ZakharovShabat
