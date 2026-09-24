import NLS.ZakharovShabat.SourceCriticalRootRatioEndpointPuncturedBound
import NLS.ComplexAnalysis.SingularEndpointPathIntegrability

/-!
# Integrability along curved singular endpoint connectors

Near an open real-type periodic gap endpoint, the critical-root
quotient grows at most as the inverse square root of the radial
distance. A smooth connector that leaves the endpoint at a linear
rate therefore has an integrable pulled-back one-form.
-/

noncomputable section
open Set Metric Complex MeasureTheory
open scoped ENNReal unitInterval
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Both branch points admit a common punctured neighborhood in which
every smooth, linearly departing connector avoiding all gaps is
curve-integrable for the critical-root quotient. -/
theorem exists_sourceCriticalRootRatio_curvedEndpointConnector_curveIntegrable
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
    let ω := NLS.ComplexAnalysis.holomorphicOneForm
      (fun z => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
        sourceCanonicalRoot hp hp1 ψ z)
    ∃ ε : ℝ, 0 < ε ∧ ∀ c ∈ ({l,r} : Set ℂ),
      ∀ {b : ℂ} (γ : Path c b),
        ContDiffOn ℝ 1 γ.extend (Icc 0 1) →
        (∀ t ∈ Ioo (0:ℝ) 1,
          γ.extend t ∈ sourceCanonicalRootDomain hp hp1 ψ) →
        (∀ t ∈ Ioo (0:ℝ) 1,
          0 < ‖c-γ.extend t‖ ∧ ‖c-γ.extend t‖ ≤ ε) →
        (∃ k : ℝ, 0 < k ∧ ∀ t ∈ Ioo (0:ℝ) 1,
          k*t ≤ ‖c-γ.extend t‖) →
        CurveIntegrable ω γ := by
  dsimp only
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let f : ℂ → ℂ := fun z =>
    deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
      sourceCanonicalRoot hp hp1 ψ z
  let ω := NLS.ComplexAnalysis.holomorphicOneForm f
  obtain ⟨ε,M,hε,hM,hbound⟩ :=
    exists_sourceCriticalRootRatio_endpointPunctured_weighted_bound
      hp hp1 ψ hreal n hopen
  refine ⟨ε,hε,?_⟩
  intro c hc b γ hγ hdom hnear ⟨k,hk,hlinear⟩
  let d₀ : ℝ := (r.re-l.re)/2
  have hd₀ : 0 < d₀ := by
    dsimp [d₀]
    linarith
  let d : ℝ := d₀*k
  have hd : 0 < d := mul_pos hd₀ hk
  have hω : ContinuousOn ω (sourceCanonicalRootDomain hp hp1 ψ) := by
    intro z hz
    exact (((sourceCriticalRootRatio_analyticOnNhd hp hp1 ψ z hz).continuousAt).smul
      continuousAt_const).continuousWithinAt
  have hcont : ContinuousOn (curveIntegralFun ω γ) (Ioo (0:ℝ) 1) := by
    have hγcont : ContinuousOn γ.extend (Ioo (0:ℝ) 1) :=
      hγ.continuousOn.mono Ioo_subset_Icc_self
    have hωγ : ContinuousOn (fun t => ω (γ.extend t)) (Ioo (0:ℝ) 1) :=
      hω.comp hγcont (fun t ht => hdom t ht)
    have hderiv : ContinuousOn
        (fun t => derivWithin γ.extend (Icc 0 1) t) (Ioo (0:ℝ) 1) :=
      (hγ.continuousOn_derivWithin uniqueDiffOn_Icc_zero_one le_rfl).mono
        Ioo_subset_Icc_self
    have happly := hωγ.clm_apply hderiv
    apply happly.congr
    intro t ht
    exact curveIntegralFun_def ω γ t
  have hmeas : AEStronglyMeasurable (curveIntegralFun ω γ)
      (volume.restrict (Ioo (0:ℝ) 1)) :=
    hcont.aestronglyMeasurable measurableSet_Ioo
  have hDcont : ContinuousOn
      (derivWithin γ.extend (Icc (0:ℝ) 1)) (Icc (0:ℝ) 1) :=
    hγ.continuousOn_derivWithin uniqueDiffOn_Icc_zero_one le_rfl
  obtain ⟨D,hD⟩ :=
    (isCompact_Icc : IsCompact (Icc (0:ℝ) 1)).exists_bound_of_continuousOn
      hDcont
  apply NLS.ComplexAnalysis.curveIntegrable_of_norm_mul_sqrt_parameter_le
    ω γ hd hmeas
  intro t ht
  let z := γ.extend t
  let ρ := ‖c-z‖
  have hρ := hnear t ht
  have hweighted : ‖f z * ((Real.sqrt (d₀*ρ) : ℝ) : ℂ)‖ ≤ M :=
    hbound c hc z (hdom t ht) hρ.1 hρ.2
  have hscaled : d*t ≤ d₀*ρ := by
    dsimp [d]
    calc
      (d₀*k)*t = d₀*(k*t) := by ring
      _ ≤ d₀*ρ := mul_le_mul_of_nonneg_left (hlinear t ht) hd₀.le
  have hweight : Real.sqrt (d*t) ≤ Real.sqrt (d₀*ρ) :=
    Real.sqrt_le_sqrt hscaled
  have hfw : ‖f z‖ * Real.sqrt (d₀*ρ) ≤ M := by
    simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)] using hweighted
  have hsmall : ‖f z‖ * Real.sqrt (d*t) ≤ M :=
    (mul_le_mul_of_nonneg_left hweight (norm_nonneg _)).trans hfw
  have htIcc : t ∈ Icc (0:ℝ) 1 := Ioo_subset_Icc_self ht
  have hD' := hD t htIcc
  rw [curveIntegralFun_def, NLS.ComplexAnalysis.holomorphicOneForm_apply]
  change ‖f z * derivWithin γ.extend (Icc 0 1) t *
    ((Real.sqrt (d*t) : ℝ) : ℂ)‖ ≤ M*D
  calc
    _ = (‖f z‖ * Real.sqrt (d*t)) *
        ‖derivWithin γ.extend (Icc 0 1) t‖ := by
          simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (Real.sqrt_nonneg _)]
          ring
    _ ≤ M*D :=
      mul_le_mul hsmall hD' (norm_nonneg _) hM.le

end NLS.ZakharovShabat
