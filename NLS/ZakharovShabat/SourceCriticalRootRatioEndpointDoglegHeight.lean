import NLS.ComplexAnalysis.EndpointDoglegHeight
import NLS.ZakharovShabat.SourceCriticalRootRatioEndpointDogleg

/-!
# Exact upper dogleg integral at a real open gap

The critical-root quotient is analytic throughout each positive-height
rectangle between two doglegs. Cauchy's rectangle identity makes the
dogleg integral constant in height. Its previously proved zero limit
then forces exact vanishing.
-/

noncomputable section
open Set Filter Topology Complex MeasureTheory
open scoped ENNReal unitInterval
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- For small positive heights, the actual path integral is the
coordinate dogleg value. -/
theorem exists_sourceCriticalRootRatio_upperDogleg_curveIntegral_eq_value
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
      (∫ᶜ z in sourceUpperGapDoglegPath hp hp1 ψ n y,
        NLS.ComplexAnalysis.holomorphicOneForm
          (fun w => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) w /
            sourceCanonicalRoot hp hp1 ψ w) z) =
        NLS.ComplexAnalysis.upperDoglegValue
          (fun w => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) w /
            sourceCanonicalRoot hp hp1 ψ w) l.re r.re y := by
  dsimp only
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let f : ℂ → ℂ := fun w =>
    deriv (canonicalDiscriminant hp (periodOnePotential ψ)) w /
      sourceCanonicalRoot hp hp1 ψ w
  obtain ⟨hl,hr⟩ := canonicalPeriodicEndpoints_im_eq_zero_of_realType hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ)
    (isRealType_periodOnePotential ψ hreal) n
  have hlre : (l.re:ℂ) = l := by
    apply Complex.ext
    · simp
    · change 0 = l.im
      exact hl.symm
  have hrre : (r.re:ℂ) = r := by
    apply Complex.ext
    · simp
    · change 0 = r.im
      exact hr.symm
  obtain ⟨ε,hε,hcurve⟩ :=
    exists_sourceCriticalRootRatio_upperDogleg_curveIntegrable_integral_eq
      hp hp1 ψ hreal n hopen
  refine ⟨ε,hε,?_⟩
  intro y hy
  have hmid := sourceCriticalRootRatio_horizontalSegment_curveIntegral_eq
    hp hp1 ψ n y
  have hhor :
      (∫ᶜ z in Path.segment (l+(y:ℂ)*Complex.I) (r+(y:ℂ)*Complex.I),
        NLS.ComplexAnalysis.holomorphicOneForm f z) =
        ∫ x in l.re..r.re, f ((x:ℂ)+(y:ℂ)*Complex.I) := by
    have h := NLS.ComplexAnalysis.curveIntegral_horizontalSegment f l.re r.re y
    rw [hlre, hrre] at h
    exact h
  unfold NLS.ComplexAnalysis.upperDoglegValue
  rw [(hcurve y hy).2]
  rw [← hmid]
  rw [NLS.ComplexAnalysis.curveIntegral_verticalSegment,
      NLS.ComplexAnalysis.curveIntegral_verticalSegment]
  rw [hhor]
  rw [hlre, hrre]

/-- The upper dogleg integral is independent of its sufficiently
small positive crossing height. -/
theorem exists_sourceCriticalRootRatio_upperDogleg_curveIntegral_eq_of_heights
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ y ∈ Ioo (0:ℝ) ε, ∀ z ∈ Ioo (0:ℝ) ε,
      (∫ᶜ w in sourceUpperGapDoglegPath hp hp1 ψ n y,
        NLS.ComplexAnalysis.holomorphicOneForm
          (fun v => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) v /
            sourceCanonicalRoot hp hp1 ψ v) w) =
      (∫ᶜ w in sourceUpperGapDoglegPath hp hp1 ψ n z,
        NLS.ComplexAnalysis.holomorphicOneForm
          (fun v => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) v /
            sourceCanonicalRoot hp hp1 ψ v) w) := by
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let f : ℂ → ℂ := fun w =>
    deriv (canonicalDiscriminant hp (periodOnePotential ψ)) w /
      sourceCanonicalRoot hp hp1 ψ w
  obtain ⟨hl,hr⟩ := canonicalPeriodicEndpoints_im_eq_zero_of_realType hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ)
    (isRealType_periodOnePotential ψ hreal) n
  have hlre : (l.re:ℂ) = l := by
    apply Complex.ext
    · simp
    · change 0 = l.im
      exact hl.symm
  have hrre : (r.re:ℂ) = r := by
    apply Complex.ext
    · simp
    · change 0 = r.im
      exact hr.symm
  obtain ⟨ε₁,hε₁,hcoord⟩ :=
    exists_sourceCriticalRootRatio_upperDogleg_curveIntegral_eq_value
      hp hp1 ψ hreal n hopen
  obtain ⟨ε₂,hε₂,hendpoint⟩ :=
    exists_sourceCriticalRootRatio_upperEndpointConnector_integrable
      hp hp1 ψ hreal n hopen
  let ε := min ε₁ ε₂
  have hε : 0 < ε := lt_min hε₁ hε₂
  have hLeftInt : IntegrableOn
      (fun v : ℝ => f ((l.re:ℂ)+(v:ℂ)*Complex.I)) (Ioo 0 ε₂) := by
    have h := hendpoint (-1) (by simp)
    rw [sourceCanonicalRootGapPoint_neg_one_eq_left hp hp1 ψ n] at h
    rw [hlre]
    exact h
  have hRightInt : IntegrableOn
      (fun v : ℝ => f ((r.re:ℂ)+(v:ℂ)*Complex.I)) (Ioo 0 ε₂) := by
    have h := hendpoint 1 (by simp)
    rw [sourceCanonicalRootGapPoint_one_eq_right hp hp1 ψ n] at h
    rw [hrre]
    exact h
  have hleft (z : ℝ) (hz : z ∈ Ioo (0:ℝ) ε) :
      IntervalIntegrable
        (fun v : ℝ => f ((l.re:ℂ)+(v:ℂ)*Complex.I)) volume 0 z := by
    apply (intervalIntegrable_iff_integrableOn_Ioo_of_le hz.1.le).2
    exact hLeftInt.mono_set
      (Ioo_subset_Ioo le_rfl (hz.2.le.trans (min_le_right ε₁ ε₂)))
  have hright (z : ℝ) (hz : z ∈ Ioo (0:ℝ) ε) :
      IntervalIntegrable
        (fun v : ℝ => f ((r.re:ℂ)+(v:ℂ)*Complex.I)) volume 0 z := by
    apply (intervalIntegrable_iff_integrableOn_Ioo_of_le hz.1.le).2
    exact hRightInt.mono_set
      (Ioo_subset_Ioo le_rfl (hz.2.le.trans (min_le_right ε₁ ε₂)))
  have hrectangle (y z : ℝ) (hy : 0 < y) (hyz : y ≤ z) :
      DifferentiableOn ℂ f (uIcc l.re r.re ×ℂ uIcc y z) := by
    intro w hw
    have hwy : y ≤ w.im := by
      have hw' := hw.2
      rw [uIcc_of_le hyz] at hw'
      exact hw'.1
    have hz : w ∈ sourceCanonicalRootDomain hp hp1 ψ :=
      sourceCanonicalRootDomain_of_im_ne_zero hp hp1 ψ hreal w
        (ne_of_gt (hy.trans_le hwy))
    exact (sourceCriticalRootRatio_analyticOnNhd hp hp1 ψ w hz).differentiableAt.differentiableWithinAt
  refine ⟨ε,hε,?_⟩
  intro y hy z hz
  have hcoordY := hcoord y ⟨hy.1, hy.2.trans_le (min_le_left ε₁ ε₂)⟩
  have hcoordZ := hcoord z ⟨hz.1, hz.2.trans_le (min_le_left ε₁ ε₂)⟩
  rcases le_total y z with hyz | hzy
  · calc
      _ = NLS.ComplexAnalysis.upperDoglegValue f l.re r.re y := hcoordY
      _ = NLS.ComplexAnalysis.upperDoglegValue f l.re r.re z :=
        NLS.ComplexAnalysis.upperDoglegValue_eq_of_rectangle
          f l.re r.re y z hy.1.le hyz (hleft z hz) (hright z hz)
            (hrectangle y z hy.1 hyz)
      _ = _ := hcoordZ.symm
  · calc
      _ = NLS.ComplexAnalysis.upperDoglegValue f l.re r.re y := hcoordY
      _ = NLS.ComplexAnalysis.upperDoglegValue f l.re r.re z :=
        (NLS.ComplexAnalysis.upperDoglegValue_eq_of_rectangle
          f l.re r.re z y hz.1.le hzy (hleft y hy) (hright y hy)
            (hrectangle z y hz.1 hzy)).symm
      _ = _ := hcoordZ.symm

/-- Every sufficiently short upper endpoint-to-endpoint dogleg has
exactly zero critical-root quotient integral. -/
theorem exists_sourceCriticalRootRatio_upperDogleg_curveIntegral_eq_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ y ∈ Ioo (0:ℝ) ε,
      (∫ᶜ w in sourceUpperGapDoglegPath hp hp1 ψ n y,
        NLS.ComplexAnalysis.holomorphicOneForm
          (fun v => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) v /
            sourceCanonicalRoot hp hp1 ψ v) w) = 0 := by
  let F : ℝ → ℂ := fun y =>
    ∫ᶜ w in sourceUpperGapDoglegPath hp hp1 ψ n y,
      NLS.ComplexAnalysis.holomorphicOneForm
        (fun v => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) v /
          sourceCanonicalRoot hp hp1 ψ v) w
  obtain ⟨ε,hε,hconst⟩ :=
    exists_sourceCriticalRootRatio_upperDogleg_curveIntegral_eq_of_heights
      hp hp1 ψ hreal n hopen
  have hlim : Tendsto F (𝓝[>] (0:ℝ)) (𝓝 (0:ℂ)) :=
    sourceCriticalRootRatio_upperDogleg_curveIntegral_tendsto_zero
      hp hp1 ψ hreal n hopen
  refine ⟨ε,hε,?_⟩
  intro y hy
  have hEq : F =ᶠ[𝓝[>] (0:ℝ)] fun _ => F y := by
    filter_upwards [Ioo_mem_nhdsGT hε] with z hz
    exact hconst z hz y hy
  have hconstlim : Tendsto F (𝓝[>] (0:ℝ)) (𝓝 (F y)) :=
    tendsto_const_nhds.congr' hEq.symm
  exact tendsto_nhds_unique hconstlim hlim

/-- A single height range gives actual curve-integrable
endpoint-to-endpoint paths with exactly vanishing integrals. -/
theorem exists_sourceCriticalRootRatio_upperDogleg_integrable_and_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ y ∈ Ioo (0:ℝ) ε,
      CurveIntegrable
        (NLS.ComplexAnalysis.holomorphicOneForm
          (fun v => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) v /
            sourceCanonicalRoot hp hp1 ψ v))
        (sourceUpperGapDoglegPath hp hp1 ψ n y) ∧
      (∫ᶜ w in sourceUpperGapDoglegPath hp hp1 ψ n y,
        NLS.ComplexAnalysis.holomorphicOneForm
          (fun v => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) v /
            sourceCanonicalRoot hp hp1 ψ v) w) = 0 := by
  obtain ⟨ε₁,hε₁,hcurve⟩ :=
    exists_sourceCriticalRootRatio_upperDogleg_curveIntegrable_integral_eq
      hp hp1 ψ hreal n hopen
  obtain ⟨ε₂,hε₂,hzero⟩ :=
    exists_sourceCriticalRootRatio_upperDogleg_curveIntegral_eq_zero
      hp hp1 ψ hreal n hopen
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, ?_⟩
  intro y hy
  exact ⟨(hcurve y ⟨hy.1, hy.2.trans_le (min_le_left ε₁ ε₂)⟩).1,
    hzero y ⟨hy.1, hy.2.trans_le (min_le_right ε₁ ε₂)⟩⟩

end NLS.ZakharovShabat
