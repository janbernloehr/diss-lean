import NLS.ZakharovShabat.SourceCriticalRootRatioCurvedEndpointDetour
import NLS.ZakharovShabat.SourceCriticalRootRatioCurvedConnectorIntegralBound
import NLS.ZakharovShabat.SourceCriticalRootRatioArbitraryHalfPlanePathLimit

/-!
# Shrinking limits for curved endpoint detours

Uniformly scaled curved connectors have integrals tending to zero.
The same holds for arbitrary smooth crossings in the upper half-plane,
so their actual branch-point-to-branch-point path has zero limit.
-/

noncomputable section
open Set Filter Topology Complex
open scoped ENNReal unitInterval
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A connector family has radial departure and speed proportional to
the positive size parameter. -/
def IsScaledCurvedEndpointConnector
    (D : Set ℂ) (ε β K y : ℝ) {c b : ℂ} (γ : Path c b) : Prop :=
  ContDiffOn ℝ 1 γ.extend (Icc 0 1) ∧
    (∀ t ∈ Ioo (0:ℝ) 1, γ.extend t ∈ D) ∧
    (∀ t ∈ Ioo (0:ℝ) 1,
      0 < ‖c-γ.extend t‖ ∧ ‖c-γ.extend t‖ ≤ ε) ∧
    (∀ t ∈ Ioo (0:ℝ) 1, (β*y)*t ≤ ‖c-γ.extend t‖) ∧
    (∀ t ∈ Ioo (0:ℝ) 1,
      ‖derivWithin γ.extend (Icc 0 1) t‖ ≤ K*y)

/-- Upper endpoint detours with uniformly scaled curved connectors
and arbitrary smooth upper crossings have integrals tending to zero. -/
theorem exists_sourceCriticalRootRatio_upperCurvedDetours_tendsto_zero
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
    let ω := NLS.ComplexAnalysis.holomorphicOneForm
      (fun z => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
        sourceCanonicalRoot hp hp1 ψ z)
    ∃ ε : ℝ, 0 < ε ∧
      ∀ δ : ℝ, 0 < δ →
      ∀ βL KL βR KR : ℝ, 0 < βL → 0 ≤ KL → 0 < βR → 0 ≤ KR →
      ∀ (left : (y : ℝ) → Path l (l+(y:ℂ)*Complex.I))
        (crossing : (y : ℝ) →
          Path (l+(y:ℂ)*Complex.I) (r+(y:ℂ)*Complex.I))
        (right : (y : ℝ) → Path r (r+(y:ℂ)*Complex.I)),
        (∀ y ∈ Ioo (0:ℝ) δ,
          IsScaledCurvedEndpointConnector D ε βL KL y (left y)) →
        (∀ y ∈ Ioo (0:ℝ) δ,
          IsScaledCurvedEndpointConnector D ε βR KR y (right y)) →
        (∀ y : ℝ, 0 < y →
          ContDiffOn ℝ 2 (crossing y).extend (Icc 0 1)) →
        (∀ y : ℝ, 0 < y → ∀ u : I, 0 < ((crossing y) u).im) →
        Tendsto
          (fun y : ℝ => ∫ᶜ z in sourceCurvedGapDetourPath
            (left y) (crossing y) (right y), ω z)
          (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  dsimp only
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let D := sourceCanonicalRootDomain hp hp1 ψ
  let ω := NLS.ComplexAnalysis.holomorphicOneForm
    (fun z => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
      sourceCanonicalRoot hp hp1 ψ z)
  obtain ⟨ε₁,hε₁,hshrink⟩ :=
    exists_sourceCriticalRootRatio_curvedConnector_integral_tendsto_zero
      hp hp1 ψ hreal n hopen
  obtain ⟨ε₂,hε₂,hdetour⟩ :=
    exists_sourceCriticalRootRatio_curvedGapDetour_integrable_integral_eq
      hp hp1 ψ hreal n hopen
  refine ⟨min ε₁ ε₂,lt_min hε₁ hε₂,?_⟩
  intro δ hδ βL KL βR KR hβL hKL hβR hKR left crossing right hleft hright
    hcross hupper
  have hleftData (y : ℝ) (hy : y ∈ Ioo (0:ℝ) δ) :
      ContDiffOn ℝ 1 (left y).extend (Icc 0 1) ∧
      (∀ t ∈ Ioo (0:ℝ) 1, (left y).extend t ∈ D) ∧
      (∀ t ∈ Ioo (0:ℝ) 1,
        0 < ‖l-(left y).extend t‖ ∧ ‖l-(left y).extend t‖ ≤ ε₁) ∧
      (∀ t ∈ Ioo (0:ℝ) 1, (βL*y)*t ≤ ‖l-(left y).extend t‖) ∧
      (∀ t ∈ Ioo (0:ℝ) 1,
        ‖derivWithin (left y).extend (Icc 0 1) t‖ ≤ KL*y) := by
    obtain ⟨hs,hd,hn,hr,hv⟩ := hleft y hy
    exact ⟨hs,hd,fun t ht => ⟨(hn t ht).1,
      (hn t ht).2.trans (min_le_left ε₁ ε₂)⟩,hr,hv⟩
  have hrightData (y : ℝ) (hy : y ∈ Ioo (0:ℝ) δ) :
      ContDiffOn ℝ 1 (right y).extend (Icc 0 1) ∧
      (∀ t ∈ Ioo (0:ℝ) 1, (right y).extend t ∈ D) ∧
      (∀ t ∈ Ioo (0:ℝ) 1,
        0 < ‖r-(right y).extend t‖ ∧ ‖r-(right y).extend t‖ ≤ ε₁) ∧
      (∀ t ∈ Ioo (0:ℝ) 1, (βR*y)*t ≤ ‖r-(right y).extend t‖) ∧
      (∀ t ∈ Ioo (0:ℝ) 1,
        ‖derivWithin (right y).extend (Icc 0 1) t‖ ≤ KR*y) := by
    obtain ⟨hs,hd,hn,hr,hv⟩ := hright y hy
    exact ⟨hs,hd,fun t ht => ⟨(hn t ht).1,
      (hn t ht).2.trans (min_le_left ε₁ ε₂)⟩,hr,hv⟩
  have hllimit : Tendsto (fun y => ∫ᶜ z in left y, ω z)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) :=
    hshrink l (by change l = l ∨ l = r; exact Or.inl rfl)
      δ hδ βL KL hβL hKL _ left hleftData
  have hrlimit : Tendsto (fun y => ∫ᶜ z in right y, ω z)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) :=
    hshrink r (by change r = l ∨ r = r; exact Or.inr rfl)
      δ hδ βR KR hβR hKR _ right hrightData
  have hmlimit : Tendsto (fun y => ∫ᶜ z in crossing y, ω z)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) :=
    sourceCriticalRootRatio_upperPaths_tendsto_zero
      hp hp1 ψ hreal n hopen crossing hcross hupper
  have heq :
      (fun y : ℝ => ∫ᶜ z in sourceCurvedGapDetourPath
        (left y) (crossing y) (right y), ω z) =ᶠ[nhdsWithin 0 (Ioi 0)]
      (fun y : ℝ => (∫ᶜ z in left y, ω z) +
        (∫ᶜ z in crossing y, ω z) - (∫ᶜ z in right y, ω z)) := by
    filter_upwards [Ioo_mem_nhdsGT hδ] with y hy
    have hleftConn : IsCurvedEndpointConnector D ε₂ (left y) := by
      obtain ⟨hs,hd,hn,hr,hv⟩ := hleft y hy
      refine ⟨hs,hd,?_,βL*y,mul_pos hβL hy.1,hr⟩
      exact fun t ht => ⟨(hn t ht).1,
        (hn t ht).2.trans (min_le_right ε₁ ε₂)⟩
    have hrightConn : IsCurvedEndpointConnector D ε₂ (right y) := by
      obtain ⟨hs,hd,hn,hr,hv⟩ := hright y hy
      refine ⟨hs,hd,?_,βR*y,mul_pos hβR hy.1,hr⟩
      exact fun t ht => ⟨(hn t ht).1,
        (hn t ht).2.trans (min_le_right ε₁ ε₂)⟩
    have hcrossdom : range (crossing y) ⊆ D := by
      rintro z ⟨u,rfl⟩
      exact sourceCanonicalRootDomain_of_im_ne_zero hp hp1 ψ hreal _
        (ne_of_gt (hupper y hy.1 u))
    exact (hdetour (left y) (crossing y) (right y)
      hleftConn hrightConn ((hcross y hy.1).of_le (by norm_num)) hcrossdom).2
  change Tendsto
    (fun y : ℝ => ∫ᶜ z in sourceCurvedGapDetourPath
      (left y) (crossing y) (right y), ω z)
    (nhdsWithin 0 (Ioi 0)) (nhds 0)
  simpa using (hllimit.add hmlimit |>.sub hrlimit).congr' heq.symm

/-- Lower endpoint detours with uniformly scaled curved connectors
and arbitrary smooth lower crossings have integrals tending to zero. -/
theorem exists_sourceCriticalRootRatio_lowerCurvedDetours_tendsto_zero
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
    let ω := NLS.ComplexAnalysis.holomorphicOneForm
      (fun z => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
        sourceCanonicalRoot hp hp1 ψ z)
    ∃ ε : ℝ, 0 < ε ∧
      ∀ δ : ℝ, 0 < δ →
      ∀ βL KL βR KR : ℝ, 0 < βL → 0 ≤ KL → 0 < βR → 0 ≤ KR →
      ∀ (left : (y : ℝ) → Path l (l+((-y:ℝ):ℂ)*Complex.I))
        (crossing : (y : ℝ) →
          Path (l+((-y:ℝ):ℂ)*Complex.I) (r+((-y:ℝ):ℂ)*Complex.I))
        (right : (y : ℝ) → Path r (r+((-y:ℝ):ℂ)*Complex.I)),
        (∀ y ∈ Ioo (0:ℝ) δ,
          IsScaledCurvedEndpointConnector D ε βL KL y (left y)) →
        (∀ y ∈ Ioo (0:ℝ) δ,
          IsScaledCurvedEndpointConnector D ε βR KR y (right y)) →
        (∀ y : ℝ, 0 < y →
          ContDiffOn ℝ 2 (crossing y).extend (Icc 0 1)) →
        (∀ y : ℝ, 0 < y → ∀ u : I, ((crossing y) u).im < 0) →
        Tendsto
          (fun y : ℝ => ∫ᶜ z in sourceCurvedGapDetourPath
            (left y) (crossing y) (right y), ω z)
          (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  dsimp only
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let D := sourceCanonicalRootDomain hp hp1 ψ
  let ω := NLS.ComplexAnalysis.holomorphicOneForm
    (fun z => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
      sourceCanonicalRoot hp hp1 ψ z)
  obtain ⟨ε₁,hε₁,hshrink⟩ :=
    exists_sourceCriticalRootRatio_curvedConnector_integral_tendsto_zero
      hp hp1 ψ hreal n hopen
  obtain ⟨ε₂,hε₂,hdetour⟩ :=
    exists_sourceCriticalRootRatio_curvedGapDetour_integrable_integral_eq
      hp hp1 ψ hreal n hopen
  refine ⟨min ε₁ ε₂,lt_min hε₁ hε₂,?_⟩
  intro δ hδ βL KL βR KR hβL hKL hβR hKR left crossing right hleft hright
    hcross hlower
  have hleftData (y : ℝ) (hy : y ∈ Ioo (0:ℝ) δ) :
      ContDiffOn ℝ 1 (left y).extend (Icc 0 1) ∧
      (∀ t ∈ Ioo (0:ℝ) 1, (left y).extend t ∈ D) ∧
      (∀ t ∈ Ioo (0:ℝ) 1,
        0 < ‖l-(left y).extend t‖ ∧ ‖l-(left y).extend t‖ ≤ ε₁) ∧
      (∀ t ∈ Ioo (0:ℝ) 1, (βL*y)*t ≤ ‖l-(left y).extend t‖) ∧
      (∀ t ∈ Ioo (0:ℝ) 1,
        ‖derivWithin (left y).extend (Icc 0 1) t‖ ≤ KL*y) := by
    obtain ⟨hs,hd,hn,hr,hv⟩ := hleft y hy
    exact ⟨hs,hd,fun t ht => ⟨(hn t ht).1,
      (hn t ht).2.trans (min_le_left ε₁ ε₂)⟩,hr,hv⟩
  have hrightData (y : ℝ) (hy : y ∈ Ioo (0:ℝ) δ) :
      ContDiffOn ℝ 1 (right y).extend (Icc 0 1) ∧
      (∀ t ∈ Ioo (0:ℝ) 1, (right y).extend t ∈ D) ∧
      (∀ t ∈ Ioo (0:ℝ) 1,
        0 < ‖r-(right y).extend t‖ ∧ ‖r-(right y).extend t‖ ≤ ε₁) ∧
      (∀ t ∈ Ioo (0:ℝ) 1, (βR*y)*t ≤ ‖r-(right y).extend t‖) ∧
      (∀ t ∈ Ioo (0:ℝ) 1,
        ‖derivWithin (right y).extend (Icc 0 1) t‖ ≤ KR*y) := by
    obtain ⟨hs,hd,hn,hr,hv⟩ := hright y hy
    exact ⟨hs,hd,fun t ht => ⟨(hn t ht).1,
      (hn t ht).2.trans (min_le_left ε₁ ε₂)⟩,hr,hv⟩
  have hllimit : Tendsto (fun y => ∫ᶜ z in left y, ω z)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) :=
    hshrink l (by change l = l ∨ l = r; exact Or.inl rfl)
      δ hδ βL KL hβL hKL _ left hleftData
  have hrlimit : Tendsto (fun y => ∫ᶜ z in right y, ω z)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) :=
    hshrink r (by change r = l ∨ r = r; exact Or.inr rfl)
      δ hδ βR KR hβR hKR _ right hrightData
  have hmlimit : Tendsto (fun y => ∫ᶜ z in crossing y, ω z)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    have hhor : Tendsto
        (fun y : ℝ => sourceCriticalRootRatio_horizontalIntegral hp hp1 ψ n (-y))
        (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
      simpa only [Function.comp_def, neg_zero] using
        (sourceCriticalRootRatio_horizontalIntegral_tendsto_zero_lower
          hp hp1 ψ hreal n hopen).comp tendsto_neg_nhdsGT_neg
    have hcrossEq :
        (fun y : ℝ => ∫ᶜ z in crossing y, ω z) =ᶠ[nhdsWithin 0 (Ioi 0)]
        (fun y : ℝ => sourceCriticalRootRatio_horizontalIntegral
          hp hp1 ψ n (-y)) := by
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact sourceCriticalRootRatio_lowerPathIntegral_eq_horizontal
        hp hp1 ψ hreal n (-y) (by simpa using hy) (crossing y)
        (hcross y hy) (hlower y hy)
    exact hhor.congr' hcrossEq.symm
  have heq :
      (fun y : ℝ => ∫ᶜ z in sourceCurvedGapDetourPath
        (left y) (crossing y) (right y), ω z) =ᶠ[nhdsWithin 0 (Ioi 0)]
      (fun y : ℝ => (∫ᶜ z in left y, ω z) +
        (∫ᶜ z in crossing y, ω z) - (∫ᶜ z in right y, ω z)) := by
    filter_upwards [Ioo_mem_nhdsGT hδ] with y hy
    have hleftConn : IsCurvedEndpointConnector D ε₂ (left y) := by
      obtain ⟨hs,hd,hn,hr,hv⟩ := hleft y hy
      refine ⟨hs,hd,?_,βL*y,mul_pos hβL hy.1,hr⟩
      exact fun t ht => ⟨(hn t ht).1,
        (hn t ht).2.trans (min_le_right ε₁ ε₂)⟩
    have hrightConn : IsCurvedEndpointConnector D ε₂ (right y) := by
      obtain ⟨hs,hd,hn,hr,hv⟩ := hright y hy
      refine ⟨hs,hd,?_,βR*y,mul_pos hβR hy.1,hr⟩
      exact fun t ht => ⟨(hn t ht).1,
        (hn t ht).2.trans (min_le_right ε₁ ε₂)⟩
    have hcrossdom : range (crossing y) ⊆ D := by
      rintro z ⟨u,rfl⟩
      exact sourceCanonicalRootDomain_of_im_ne_zero hp hp1 ψ hreal _
        (ne_of_lt (hlower y hy.1 u))
    exact (hdetour (left y) (crossing y) (right y)
      hleftConn hrightConn ((hcross y hy.1).of_le (by norm_num)) hcrossdom).2
  change Tendsto
    (fun y : ℝ => ∫ᶜ z in sourceCurvedGapDetourPath
      (left y) (crossing y) (right y), ω z)
    (nhdsWithin 0 (Ioi 0)) (nhds 0)
  simpa using (hllimit.add hmlimit |>.sub hrlimit).congr' heq.symm

end NLS.ZakharovShabat
