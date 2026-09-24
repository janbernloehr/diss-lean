import NLS.ZakharovShabat.SourceCriticalRootRatioCurvedEndpointConnector

/-!
# Quantitative integral bound for curved endpoint connectors

The inverse-square-root quotient bound controls not just
integrability but the norm of the actual connector integral. The
estimate records the path's speed and its linear radial departure
from the singular branch point.
-/

noncomputable section
open Set Metric Complex MeasureTheory Filter Topology
open scoped ENNReal unitInterval
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A common neighborhood and quotient constant give a quantitative
integral estimate for smooth curved connectors at either gap end. -/
theorem exists_sourceCriticalRootRatio_curvedConnector_integral_bound
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
    let d₀ := (r.re-l.re)/2
    let ω := NLS.ComplexAnalysis.holomorphicOneForm
      (fun z => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
        sourceCanonicalRoot hp hp1 ψ z)
    ∃ ε M : ℝ, 0 < ε ∧ 0 < M ∧
      ∀ c ∈ ({l,r} : Set ℂ), ∀ {b : ℂ} (γ : Path c b),
        ContDiffOn ℝ 1 γ.extend (Icc 0 1) →
        (∀ t ∈ Ioo (0:ℝ) 1,
          γ.extend t ∈ sourceCanonicalRootDomain hp hp1 ψ) →
        (∀ t ∈ Ioo (0:ℝ) 1,
          0 < ‖c-γ.extend t‖ ∧ ‖c-γ.extend t‖ ≤ ε) →
        ∀ k : ℝ, 0 < k →
          (∀ t ∈ Ioo (0:ℝ) 1, k*t ≤ ‖c-γ.extend t‖) →
          ∀ D : ℝ,
            (∀ t ∈ Ioo (0:ℝ) 1,
              ‖derivWithin γ.extend (Icc 0 1) t‖ ≤ D) →
            CurveIntegrable ω γ ∧
              ‖∫ᶜ z in γ, ω z‖ ≤
                (M*D / Real.sqrt (d₀*k))*2 := by
  dsimp only
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let d₀ : ℝ := (r.re-l.re)/2
  have hd₀ : 0 < d₀ := by
    dsimp [d₀]
    linarith
  let f : ℂ → ℂ := fun z =>
    deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
      sourceCanonicalRoot hp hp1 ψ z
  let ω := NLS.ComplexAnalysis.holomorphicOneForm f
  obtain ⟨ε₁,hε₁,hconnector⟩ :=
    exists_sourceCriticalRootRatio_curvedEndpointConnector_curveIntegrable
      hp hp1 ψ hreal n hopen
  obtain ⟨ε₂,M,hε₂,hM,hbound⟩ :=
    exists_sourceCriticalRootRatio_endpointPunctured_weighted_bound
      hp hp1 ψ hreal n hopen
  refine ⟨min ε₁ ε₂,M,lt_min hε₁ hε₂,hM,?_⟩
  intro c hc b γ hγ hdom hnear k hk hlinear D hD
  have hnear₁ (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) :
      0 < ‖c-γ.extend t‖ ∧ ‖c-γ.extend t‖ ≤ ε₁ :=
    ⟨(hnear t ht).1,(hnear t ht).2.trans (min_le_left ε₁ ε₂)⟩
  have hnear₂ (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) :
      0 < ‖c-γ.extend t‖ ∧ ‖c-γ.extend t‖ ≤ ε₂ :=
    ⟨(hnear t ht).1,(hnear t ht).2.trans (min_le_right ε₁ ε₂)⟩
  have hInt : CurveIntegrable ω γ :=
    hconnector c hc γ hγ hdom hnear₁ ⟨k,hk,hlinear⟩
  let d := d₀*k
  have hd : 0 < d := mul_pos hd₀ hk
  constructor
  · exact hInt
  · apply NLS.ComplexAnalysis.norm_curveIntegral_le_of_norm_mul_sqrt_parameter_le
      ω γ hd
    intro t ht
    let z := γ.extend t
    let ρ := ‖c-z‖
    have hρ := hnear₂ t ht
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
    rw [curveIntegralFun_def, NLS.ComplexAnalysis.holomorphicOneForm_apply]
    change ‖f z * derivWithin γ.extend (Icc 0 1) t *
      ((Real.sqrt (d*t) : ℝ) : ℂ)‖ ≤ M*D
    calc
      _ = (‖f z‖ * Real.sqrt (d*t)) *
          ‖derivWithin γ.extend (Icc 0 1) t‖ := by
            simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg (Real.sqrt_nonneg _)]
            ring
      _ ≤ M*D := mul_le_mul hsmall (hD t ht) (norm_nonneg _) hM.le

/-- A family of short curved connectors has vanishing integrals when
its radial departure and speed are both proportional to its size. -/
theorem exists_sourceCriticalRootRatio_curvedConnector_integral_tendsto_zero
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
      ∀ δ : ℝ, 0 < δ → ∀ β K : ℝ, 0 < β → 0 ≤ K →
      ∀ (b : ℝ → ℂ) (Γ : ∀ y : ℝ, Path c (b y)),
        (∀ y ∈ Ioo (0:ℝ) δ,
          ContDiffOn ℝ 1 (Γ y).extend (Icc 0 1) ∧
          (∀ t ∈ Ioo (0:ℝ) 1,
            (Γ y).extend t ∈ sourceCanonicalRootDomain hp hp1 ψ) ∧
          (∀ t ∈ Ioo (0:ℝ) 1,
            0 < ‖c-(Γ y).extend t‖ ∧ ‖c-(Γ y).extend t‖ ≤ ε) ∧
          (∀ t ∈ Ioo (0:ℝ) 1,
            (β*y)*t ≤ ‖c-(Γ y).extend t‖) ∧
          (∀ t ∈ Ioo (0:ℝ) 1,
            ‖derivWithin (Γ y).extend (Icc 0 1) t‖ ≤ K*y)) →
        Tendsto (fun y => ∫ᶜ z in Γ y, ω z)
          (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  dsimp only
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let d₀ : ℝ := (r.re-l.re)/2
  have hd₀ : 0 < d₀ := by
    dsimp [d₀]
    linarith
  let ω := NLS.ComplexAnalysis.holomorphicOneForm
    (fun z => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
      sourceCanonicalRoot hp hp1 ψ z)
  obtain ⟨ε,M,hε,hM,hbound⟩ :=
    exists_sourceCriticalRootRatio_curvedConnector_integral_bound
      hp hp1 ψ hreal n hopen
  refine ⟨ε,hε,?_⟩
  intro c hc δ hδ β K hβ hK b Γ hfamily
  let A := d₀*β
  have hA : 0 < A := mul_pos hd₀ hβ
  let C := (M*K / Real.sqrt A)*2
  have hsqrt : Tendsto (fun y : ℝ => Real.sqrt y)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    simpa using (Real.continuous_sqrt.tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds
  have hupper : Tendsto (fun y : ℝ => C*Real.sqrt y)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    simpa using (tendsto_const_nhds.mul hsqrt :
      Tendsto (fun y : ℝ => C*Real.sqrt y)
        (nhdsWithin 0 (Ioi 0)) (nhds (C*0)))
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun y => norm_nonneg
    (∫ᶜ z in Γ y, ω z))) ?_ hupper
  filter_upwards [Ioo_mem_nhdsGT hδ] with y hy
  obtain ⟨hγ,hdom,hnear,hlinear,hspeed⟩ := hfamily y hy
  have hquant := (hbound c hc (Γ y) hγ hdom hnear
    (β*y) (mul_pos hβ hy.1) hlinear (K*y) hspeed).2
  have hysqrt : 0 < Real.sqrt y := Real.sqrt_pos.2 hy.1
  have heq : (M*(K*y) / Real.sqrt (d₀*(β*y)))*2 = C*Real.sqrt y := by
    have hmul : d₀*(β*y) = A*y := by dsimp [A]; ring
    rw [hmul, Real.sqrt_mul hA.le]
    dsimp [C]
    field_simp
    nlinarith [Real.sq_sqrt hy.1.le]
  exact hquant.trans_eq heq

end NLS.ZakharovShabat
