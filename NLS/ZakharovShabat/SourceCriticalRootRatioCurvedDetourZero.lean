import NLS.ZakharovShabat.SourceCriticalRootRatioPrimitiveBoundary
import NLS.ZakharovShabat.SourceCriticalRootRatioCurvedDetourPrimitiveDefect

/-!
# Exact zero for immediately curved singular detours

The quotient primitive has one common boundary value at the two
endpoints of an open real-type gap within either half-plane. Every
short linearly departing curved connector approaches that value, so
the primitive defect formula makes the complete detour integral zero.
-/

noncomputable section
open Set Filter Topology Complex
open scoped ENNReal unitInterval
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

private theorem path_start_tendsto_within
    {a b : ℂ} (γ : Path a b) (s : Set ℂ)
    (hγs : ∀ t ∈ Ioo (0:ℝ) 1, γ.extend t ∈ s) :
    Tendsto γ.extend (𝓝[>] (0:ℝ)) (𝓝[s] a) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have hγ0 : ContinuousAt γ.extend (0:ℝ) := γ.continuous_extend.continuousAt
    have hγ0' : Tendsto γ.extend (𝓝[>] (0:ℝ)) (𝓝 (γ.extend 0)) :=
      hγ0.tendsto.mono_left nhdsWithin_le_nhds
    simpa only [Path.extend_zero] using hγ0'
  · filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ) < 1)] with t ht
    exact hγs t ht

/-- Every sufficiently short upper detour with immediately curved,
linearly departing connectors has exactly zero quotient integral. -/
theorem exists_sourceCriticalRootRatio_upperCurvedDetour_integral_eq_zero
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
    let D := sourceCanonicalRootDomain hp hp1 ψ
    let f : ℂ → ℂ := fun z =>
      deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
        sourceCanonicalRoot hp hp1 ψ z
    ∃ ε : ℝ, 0 < ε ∧ ∀ {a b : ℂ}
      (left : Path l a) (crossing : Path a b) (right : Path r b),
        IsCurvedEndpointConnector D ε left →
        IsCurvedEndpointConnector D ε right →
        (∀ t ∈ Ioo (0:ℝ) 1, 0 < (left.extend t).im) →
        (∀ t ∈ Ioo (0:ℝ) 1, 0 < (right.extend t).im) →
        ContDiffOn ℝ 1 crossing.extend (Icc 0 1) →
        (∀ u : I, 0 < (crossing u).im) →
        CurveIntegrable (NLS.ComplexAnalysis.holomorphicOneForm f)
          (sourceCurvedGapDetourPath left crossing right) ∧
        (∫ᶜ z in sourceCurvedGapDetourPath left crossing right,
          NLS.ComplexAnalysis.holomorphicOneForm f z) = 0 := by
  dsimp only
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let f : ℂ → ℂ := fun z =>
    deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
      sourceCanonicalRoot hp hp1 ψ z
  obtain ⟨F,hF⟩ := exists_sourceCriticalRootRatio_upperHalfPlane_primitive
    hp hp1 ψ hreal
  obtain ⟨A,hboundaryL,hboundaryR⟩ :=
    sourceCriticalRootRatio_upperPrimitive_common_boundary_limit
      hp hp1 ψ hreal n hopen F hF
  obtain ⟨ε,hε,hdefect⟩ :=
    exists_sourceCriticalRootRatio_upperCurvedDetour_primitive_defect
      hp hp1 ψ hreal n hopen
  refine ⟨ε,hε,?_⟩
  intro a b left crossing right hleft hright hleftU hrightU hcross hcrossU
  obtain ⟨Aleft,Aright,hAl,hAr,hcurve,hInt⟩ :=
    hdefect left crossing right hleft hright hleftU hrightU hcross hcrossU F hF
  have hleftlim : Tendsto (F ∘ left.extend)
      (𝓝[>] (0:ℝ)) (𝓝 A) :=
    hboundaryL.comp (path_start_tendsto_within left
      {z : ℂ | 0 < z.im} hleftU)
  have hrightlim : Tendsto (F ∘ right.extend)
      (𝓝[>] (0:ℝ)) (𝓝 A) :=
    hboundaryR.comp (path_start_tendsto_within right
      {z : ℂ | 0 < z.im} hrightU)
  have heqL : Aleft = A := tendsto_nhds_unique hAl hleftlim
  have heqR : Aright = A := tendsto_nhds_unique hAr hrightlim
  refine ⟨hcurve,?_⟩
  rw [hInt,heqL,heqR,sub_self]

/-- Every sufficiently short lower detour with immediately curved,
linearly departing connectors has exactly zero quotient integral. -/
theorem exists_sourceCriticalRootRatio_lowerCurvedDetour_integral_eq_zero
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
    let D := sourceCanonicalRootDomain hp hp1 ψ
    let f : ℂ → ℂ := fun z =>
      deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
        sourceCanonicalRoot hp hp1 ψ z
    ∃ ε : ℝ, 0 < ε ∧ ∀ {a b : ℂ}
      (left : Path l a) (crossing : Path a b) (right : Path r b),
        IsCurvedEndpointConnector D ε left →
        IsCurvedEndpointConnector D ε right →
        (∀ t ∈ Ioo (0:ℝ) 1, (left.extend t).im < 0) →
        (∀ t ∈ Ioo (0:ℝ) 1, (right.extend t).im < 0) →
        ContDiffOn ℝ 1 crossing.extend (Icc 0 1) →
        (∀ u : I, (crossing u).im < 0) →
        CurveIntegrable (NLS.ComplexAnalysis.holomorphicOneForm f)
          (sourceCurvedGapDetourPath left crossing right) ∧
        (∫ᶜ z in sourceCurvedGapDetourPath left crossing right,
          NLS.ComplexAnalysis.holomorphicOneForm f z) = 0 := by
  dsimp only
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let f : ℂ → ℂ := fun z =>
    deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
      sourceCanonicalRoot hp hp1 ψ z
  obtain ⟨F,hF⟩ := exists_sourceCriticalRootRatio_lowerHalfPlane_primitive
    hp hp1 ψ hreal
  obtain ⟨A,hboundaryL,hboundaryR⟩ :=
    sourceCriticalRootRatio_lowerPrimitive_common_boundary_limit
      hp hp1 ψ hreal n hopen F hF
  obtain ⟨ε,hε,hdefect⟩ :=
    exists_sourceCriticalRootRatio_lowerCurvedDetour_primitive_defect
      hp hp1 ψ hreal n hopen
  refine ⟨ε,hε,?_⟩
  intro a b left crossing right hleft hright hleftU hrightU hcross hcrossU
  obtain ⟨Aleft,Aright,hAl,hAr,hcurve,hInt⟩ :=
    hdefect left crossing right hleft hright hleftU hrightU hcross hcrossU F hF
  have hleftlim : Tendsto (F ∘ left.extend)
      (𝓝[>] (0:ℝ)) (𝓝 A) :=
    hboundaryL.comp (path_start_tendsto_within left
      {z : ℂ | z.im < 0} hleftU)
  have hrightlim : Tendsto (F ∘ right.extend)
      (𝓝[>] (0:ℝ)) (𝓝 A) :=
    hboundaryR.comp (path_start_tendsto_within right
      {z : ℂ | z.im < 0} hrightU)
  have heqL : Aleft = A := tendsto_nhds_unique hAl hleftlim
  have heqR : Aright = A := tendsto_nhds_unique hAr hrightlim
  refine ⟨hcurve,?_⟩
  rw [hInt,heqL,heqR,sub_self]

end NLS.ZakharovShabat
