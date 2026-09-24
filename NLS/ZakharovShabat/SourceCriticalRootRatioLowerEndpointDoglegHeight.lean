import NLS.ZakharovShabat.SourceCriticalRootRatioLowerEndpointDogleg

/-!
# Exact lower dogleg integral at a real open gap

The same Cauchy rectangle identity applies below the real axis.
The lower endpoint estimates make the singular connector integrals
well-defined, and the shrinking-depth limit determines their common
height-independent value.
-/

noncomputable section
open Set Filter Topology Complex MeasureTheory
open scoped ENNReal unitInterval
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The lower dogleg curve integral agrees with the signed-height
coordinate expression. -/
theorem exists_sourceCriticalRootRatio_lowerDogleg_curveIntegral_eq_value
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
      (∫ᶜ z in sourceLowerGapDoglegPath hp hp1 ψ n y,
        NLS.ComplexAnalysis.holomorphicOneForm
          (fun w => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) w /
            sourceCanonicalRoot hp hp1 ψ w) z) =
        NLS.ComplexAnalysis.upperDoglegValue
          (fun w => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) w /
            sourceCanonicalRoot hp hp1 ψ w) l.re r.re (-y) := by
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
    exists_sourceCriticalRootRatio_lowerDogleg_curveIntegrable_integral_eq
      hp hp1 ψ hreal n hopen
  refine ⟨ε,hε,?_⟩
  intro y hy
  have hmid := sourceCriticalRootRatio_horizontalSegment_curveIntegral_eq
    hp hp1 ψ n (-y)
  have hhor :
      (∫ᶜ z in Path.segment (l+((-y:ℝ):ℂ)*Complex.I)
          (r+((-y:ℝ):ℂ)*Complex.I),
        NLS.ComplexAnalysis.holomorphicOneForm f z) =
        ∫ x in l.re..r.re, f ((x:ℂ)+((-y:ℝ):ℂ)*Complex.I) := by
    have h := NLS.ComplexAnalysis.curveIntegral_horizontalSegment f l.re r.re (-y)
    rw [hlre, hrre] at h
    exact h
  unfold NLS.ComplexAnalysis.upperDoglegValue
  rw [(hcurve y hy).2]
  rw [← hmid]
  rw [NLS.ComplexAnalysis.curveIntegral_verticalSegment,
      NLS.ComplexAnalysis.curveIntegral_verticalSegment]
  rw [hhor]
  rw [hlre, hrre]

/-- The lower dogleg integral is independent of its sufficiently
small positive depth. -/
theorem exists_sourceCriticalRootRatio_lowerDogleg_curveIntegral_eq_of_depths
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ y ∈ Ioo (0:ℝ) ε, ∀ z ∈ Ioo (0:ℝ) ε,
      (∫ᶜ w in sourceLowerGapDoglegPath hp hp1 ψ n y,
        NLS.ComplexAnalysis.holomorphicOneForm
          (fun v => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) v /
            sourceCanonicalRoot hp hp1 ψ v) w) =
      (∫ᶜ w in sourceLowerGapDoglegPath hp hp1 ψ n z,
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
    exists_sourceCriticalRootRatio_lowerDogleg_curveIntegral_eq_value
      hp hp1 ψ hreal n hopen
  obtain ⟨ε₂,hε₂,hendpoint⟩ :=
    exists_sourceCriticalRootRatio_lowerEndpointConnector_integrable
      hp hp1 ψ hreal n hopen
  let ε := min ε₁ ε₂
  have hε : 0 < ε := lt_min hε₁ hε₂
  have hLeftInt : IntegrableOn
      (fun v : ℝ => f ((l.re:ℂ)+((-v:ℝ):ℂ)*Complex.I)) (Ioo 0 ε₂) := by
    have h := hendpoint (-1) (by simp)
    rw [sourceCanonicalRootGapPoint_neg_one_eq_left hp hp1 ψ n] at h
    rw [hlre]
    exact h
  have hRightInt : IntegrableOn
      (fun v : ℝ => f ((r.re:ℂ)+((-v:ℝ):ℂ)*Complex.I)) (Ioo 0 ε₂) := by
    have h := hendpoint 1 (by simp)
    rw [sourceCanonicalRootGapPoint_one_eq_right hp hp1 ψ n] at h
    rw [hrre]
    exact h
  have hleft (z : ℝ) (hz : z ∈ Ioo (0:ℝ) ε) :
      IntervalIntegrable
        (fun v : ℝ => f ((l.re:ℂ)+(v:ℂ)*Complex.I)) volume 0 (-z) := by
    apply NLS.ComplexAnalysis.intervalIntegrable_signed_vertical_of_downward
    apply (intervalIntegrable_iff_integrableOn_Ioo_of_le hz.1.le).2
    exact hLeftInt.mono_set
      (Ioo_subset_Ioo le_rfl (hz.2.le.trans (min_le_right ε₁ ε₂)))
  have hright (z : ℝ) (hz : z ∈ Ioo (0:ℝ) ε) :
      IntervalIntegrable
        (fun v : ℝ => f ((r.re:ℂ)+(v:ℂ)*Complex.I)) volume 0 (-z) := by
    apply NLS.ComplexAnalysis.intervalIntegrable_signed_vertical_of_downward
    apply (intervalIntegrable_iff_integrableOn_Ioo_of_le hz.1.le).2
    exact hRightInt.mono_set
      (Ioo_subset_Ioo le_rfl (hz.2.le.trans (min_le_right ε₁ ε₂)))
  have hrectangle (y z : ℝ) (hy : 0 < y) (hz : 0 < z) :
      DifferentiableOn ℂ f (uIcc l.re r.re ×ℂ uIcc (-y) (-z)) := by
    intro w hw
    have hwim : w.im < 0 := by
      rcases le_total y z with hyz | hzy
      · have hw' := hw.2
        rw [uIcc_comm (-y) (-z), uIcc_of_le (neg_le_neg hyz)] at hw'
        exact lt_of_le_of_lt hw'.2 (neg_neg_of_pos hy)
      · have hw' := hw.2
        rw [uIcc_of_le (neg_le_neg hzy)] at hw'
        exact lt_of_le_of_lt hw'.2 (neg_neg_of_pos hz)
    have hdom : w ∈ sourceCanonicalRootDomain hp hp1 ψ :=
      sourceCanonicalRootDomain_of_im_ne_zero hp hp1 ψ hreal w (ne_of_lt hwim)
    exact (sourceCriticalRootRatio_analyticOnNhd hp hp1 ψ w hdom).differentiableAt.differentiableWithinAt
  refine ⟨ε,hε,?_⟩
  intro y hy z hz
  have hcoordY := hcoord y ⟨hy.1, hy.2.trans_le (min_le_left ε₁ ε₂)⟩
  have hcoordZ := hcoord z ⟨hz.1, hz.2.trans_le (min_le_left ε₁ ε₂)⟩
  calc
    _ = NLS.ComplexAnalysis.upperDoglegValue f l.re r.re (-y) := hcoordY
    _ = NLS.ComplexAnalysis.upperDoglegValue f l.re r.re (-z) :=
      NLS.ComplexAnalysis.upperDoglegValue_eq_of_rectangle_signed
        f l.re r.re (-y) (-z) (hleft y hy) (hleft z hz)
          (hright y hy) (hright z hz) (hrectangle y z hy.1 hz.1)
    _ = _ := hcoordZ.symm

/-- Every sufficiently shallow lower endpoint-to-endpoint dogleg
has exactly zero quotient integral. -/
theorem exists_sourceCriticalRootRatio_lowerDogleg_curveIntegral_eq_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ y ∈ Ioo (0:ℝ) ε,
      (∫ᶜ w in sourceLowerGapDoglegPath hp hp1 ψ n y,
        NLS.ComplexAnalysis.holomorphicOneForm
          (fun v => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) v /
            sourceCanonicalRoot hp hp1 ψ v) w) = 0 := by
  let F : ℝ → ℂ := fun y =>
    ∫ᶜ w in sourceLowerGapDoglegPath hp hp1 ψ n y,
      NLS.ComplexAnalysis.holomorphicOneForm
        (fun v => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) v /
          sourceCanonicalRoot hp hp1 ψ v) w
  obtain ⟨ε,hε,hconst⟩ :=
    exists_sourceCriticalRootRatio_lowerDogleg_curveIntegral_eq_of_depths
      hp hp1 ψ hreal n hopen
  have hlim : Tendsto F (𝓝[>] (0:ℝ)) (𝓝 (0:ℂ)) :=
    sourceCriticalRootRatio_lowerDogleg_curveIntegral_tendsto_zero
      hp hp1 ψ hreal n hopen
  refine ⟨ε,hε,?_⟩
  intro y hy
  have hEq : F =ᶠ[𝓝[>] (0:ℝ)] fun _ => F y := by
    filter_upwards [Ioo_mem_nhdsGT hε] with z hz
    exact hconst z hz y hy
  have hconstlim : Tendsto F (𝓝[>] (0:ℝ)) (𝓝 (F y)) :=
    tendsto_const_nhds.congr' hEq.symm
  exact tendsto_nhds_unique hconstlim hlim

/-- A common depth range gives genuine curve-integrable lower
doglegs with zero integral. -/
theorem exists_sourceCriticalRootRatio_lowerDogleg_integrable_and_zero
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
        (sourceLowerGapDoglegPath hp hp1 ψ n y) ∧
      (∫ᶜ w in sourceLowerGapDoglegPath hp hp1 ψ n y,
        NLS.ComplexAnalysis.holomorphicOneForm
          (fun v => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) v /
            sourceCanonicalRoot hp hp1 ψ v) w) = 0 := by
  obtain ⟨ε₁,hε₁,hcurve⟩ :=
    exists_sourceCriticalRootRatio_lowerDogleg_curveIntegrable_integral_eq
      hp hp1 ψ hreal n hopen
  obtain ⟨ε₂,hε₂,hzero⟩ :=
    exists_sourceCriticalRootRatio_lowerDogleg_curveIntegral_eq_zero
      hp hp1 ψ hreal n hopen
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, ?_⟩
  intro y hy
  exact ⟨(hcurve y ⟨hy.1, hy.2.trans_le (min_le_left ε₁ ε₂)⟩).1,
    hzero y ⟨hy.1, hy.2.trans_le (min_le_right ε₁ ε₂)⟩⟩

/-- One uniform short-height range works for both upper and lower
endpoint-to-endpoint paths. -/
theorem exists_sourceCriticalRootRatio_bothDoglegs_integrable_and_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ y ∈ Ioo (0:ℝ) ε,
      (CurveIntegrable
        (NLS.ComplexAnalysis.holomorphicOneForm
          (fun v => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) v /
            sourceCanonicalRoot hp hp1 ψ v))
        (sourceUpperGapDoglegPath hp hp1 ψ n y) ∧
      (∫ᶜ w in sourceUpperGapDoglegPath hp hp1 ψ n y,
        NLS.ComplexAnalysis.holomorphicOneForm
          (fun v => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) v /
            sourceCanonicalRoot hp hp1 ψ v) w) = 0) ∧
      (CurveIntegrable
        (NLS.ComplexAnalysis.holomorphicOneForm
          (fun v => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) v /
            sourceCanonicalRoot hp hp1 ψ v))
        (sourceLowerGapDoglegPath hp hp1 ψ n y) ∧
      (∫ᶜ w in sourceLowerGapDoglegPath hp hp1 ψ n y,
        NLS.ComplexAnalysis.holomorphicOneForm
          (fun v => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) v /
            sourceCanonicalRoot hp hp1 ψ v) w) = 0) := by
  obtain ⟨ε₁,hε₁,hupper⟩ :=
    exists_sourceCriticalRootRatio_upperDogleg_integrable_and_zero
      hp hp1 ψ hreal n hopen
  obtain ⟨ε₂,hε₂,hlower⟩ :=
    exists_sourceCriticalRootRatio_lowerDogleg_integrable_and_zero
      hp hp1 ψ hreal n hopen
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, ?_⟩
  intro y hy
  exact ⟨hupper y ⟨hy.1,hy.2.trans_le (min_le_left ε₁ ε₂)⟩,
    hlower y ⟨hy.1,hy.2.trans_le (min_le_right ε₁ ε₂)⟩⟩

end NLS.ZakharovShabat
