import NLS.ZakharovShabat.SourceCriticalRootRatioCurvedEndpointDetour
import NLS.ZakharovShabat.SourceCriticalRootRatioArbitraryHalfPlanePathLimit
import NLS.ZakharovShabat.SourceCriticalRootRatioLowerEndpointDoglegHeight

/-!
# Comparing curved endpoint detours with zero-integral doglegs

At a fixed height or depth, the regular crossing has the same integral
as a horizontal segment. The whole curved detour therefore differs
from the zero-integral dogleg only by its two connector integrals.
-/

noncomputable section
open Set Complex
open scoped ENNReal unitInterval
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A short upper detour with curved connectors differs from the zero
upper dogleg precisely by the left and right connector errors. -/
theorem exists_sourceCriticalRootRatio_upperCurvedDetour_integral_compare
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
    ∃ ε : ℝ, 0 < ε ∧ ∀ y ∈ Ioo (0:ℝ) ε,
      ∀ (left : Path l (l+(y:ℂ)*Complex.I))
        (crossing : Path (l+(y:ℂ)*Complex.I) (r+(y:ℂ)*Complex.I))
        (right : Path r (r+(y:ℂ)*Complex.I)),
        IsCurvedEndpointConnector D ε left →
        IsCurvedEndpointConnector D ε right →
        ContDiffOn ℝ 2 crossing.extend (Icc 0 1) →
        (∀ u : I, 0 < (crossing u).im) →
        CurveIntegrable ω (sourceCurvedGapDetourPath left crossing right) ∧
        (∫ᶜ z in sourceCurvedGapDetourPath left crossing right, ω z) =
          ((∫ᶜ z in left, ω z) -
            (∫ᶜ z in Path.segment l (l+(y:ℂ)*Complex.I), ω z)) -
          ((∫ᶜ z in right, ω z) -
            (∫ᶜ z in Path.segment r (r+(y:ℂ)*Complex.I), ω z)) := by
  dsimp only
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let D := sourceCanonicalRootDomain hp hp1 ψ
  let ω := NLS.ComplexAnalysis.holomorphicOneForm
    (fun z => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
      sourceCanonicalRoot hp hp1 ψ z)
  obtain ⟨ε₁,hε₁,hcurved⟩ :=
    exists_sourceCriticalRootRatio_curvedGapDetour_integrable_integral_eq
      hp hp1 ψ hreal n hopen
  obtain ⟨ε₂,hε₂,hstraight⟩ :=
    exists_sourceCriticalRootRatio_upperDogleg_curveIntegrable_integral_eq
      hp hp1 ψ hreal n hopen
  obtain ⟨ε₃,hε₃,hzero⟩ :=
    exists_sourceCriticalRootRatio_upperDogleg_curveIntegral_eq_zero
      hp hp1 ψ hreal n hopen
  refine ⟨min ε₁ (min ε₂ ε₃),lt_min hε₁ (lt_min hε₂ hε₃),?_⟩
  intro y hy left crossing right hleft hright hcross hupper
  have hy₂ : y ∈ Ioo (0:ℝ) ε₂ :=
    ⟨hy.1,hy.2.trans_le ((min_le_right ε₁ (min ε₂ ε₃)).trans
      (min_le_left ε₂ ε₃))⟩
  have hy₃ : y ∈ Ioo (0:ℝ) ε₃ :=
    ⟨hy.1,hy.2.trans_le ((min_le_right ε₁ (min ε₂ ε₃)).trans
      (min_le_right ε₂ ε₃))⟩
  have hleft₁ : IsCurvedEndpointConnector D ε₁ left := by
    obtain ⟨hs,hd,hn,k,hk,hr⟩ := hleft
    refine ⟨hs,hd,?_,k,hk,hr⟩
    exact fun t ht => ⟨(hn t ht).1,
      (hn t ht).2.trans (min_le_left ε₁ (min ε₂ ε₃))⟩
  have hright₁ : IsCurvedEndpointConnector D ε₁ right := by
    obtain ⟨hs,hd,hn,k,hk,hr⟩ := hright
    refine ⟨hs,hd,?_,k,hk,hr⟩
    exact fun t ht => ⟨(hn t ht).1,
      (hn t ht).2.trans (min_le_left ε₁ (min ε₂ ε₃))⟩
  have hcrossdom : range crossing ⊆ D := by
    rintro z ⟨u,rfl⟩
    exact sourceCanonicalRootDomain_of_im_ne_zero hp hp1 ψ hreal _
      (ne_of_gt (hupper u))
  have hcurvedEq := hcurved left crossing right hleft₁ hright₁
    (hcross.of_le (by norm_num)) hcrossdom
  have hstraightEq := (hstraight y hy₂).2
  have hzeroEq := hzero y hy₃
  have hcrossEq := sourceCriticalRootRatio_upperPathIntegral_eq_horizontal
    hp hp1 ψ hreal n y hy.1 crossing hcross hupper
  constructor
  · exact hcurvedEq.1
  · change (∫ᶜ z in sourceCurvedGapDetourPath left crossing right, ω z) = _
    rw [hcurvedEq.2, hcrossEq]
    have hcancel :
        (∫ᶜ z in Path.segment l (l+(y:ℂ)*Complex.I), ω z) +
        sourceCriticalRootRatio_horizontalIntegral hp hp1 ψ n y -
        (∫ᶜ z in Path.segment r (r+(y:ℂ)*Complex.I), ω z) = 0 := by
      rw [← hstraightEq]
      exact hzeroEq
    apply eq_of_sub_eq_zero
    linear_combination hcancel

/-- A short lower detour with curved connectors differs from the zero
lower dogleg precisely by the left and right connector errors. -/
theorem exists_sourceCriticalRootRatio_lowerCurvedDetour_integral_compare
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
    ∃ ε : ℝ, 0 < ε ∧ ∀ y ∈ Ioo (0:ℝ) ε,
      ∀ (left : Path l (l+((-y:ℝ):ℂ)*Complex.I))
        (crossing : Path (l+((-y:ℝ):ℂ)*Complex.I) (r+((-y:ℝ):ℂ)*Complex.I))
        (right : Path r (r+((-y:ℝ):ℂ)*Complex.I)),
        IsCurvedEndpointConnector D ε left →
        IsCurvedEndpointConnector D ε right →
        ContDiffOn ℝ 2 crossing.extend (Icc 0 1) →
        (∀ u : I, (crossing u).im < 0) →
        CurveIntegrable ω (sourceCurvedGapDetourPath left crossing right) ∧
        (∫ᶜ z in sourceCurvedGapDetourPath left crossing right, ω z) =
          ((∫ᶜ z in left, ω z) -
            (∫ᶜ z in Path.segment l (l+((-y:ℝ):ℂ)*Complex.I), ω z)) -
          ((∫ᶜ z in right, ω z) -
            (∫ᶜ z in Path.segment r (r+((-y:ℝ):ℂ)*Complex.I), ω z)) := by
  dsimp only
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let D := sourceCanonicalRootDomain hp hp1 ψ
  let ω := NLS.ComplexAnalysis.holomorphicOneForm
    (fun z => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
      sourceCanonicalRoot hp hp1 ψ z)
  obtain ⟨ε₁,hε₁,hcurved⟩ :=
    exists_sourceCriticalRootRatio_curvedGapDetour_integrable_integral_eq
      hp hp1 ψ hreal n hopen
  obtain ⟨ε₂,hε₂,hstraight⟩ :=
    exists_sourceCriticalRootRatio_lowerDogleg_curveIntegrable_integral_eq
      hp hp1 ψ hreal n hopen
  obtain ⟨ε₃,hε₃,hzero⟩ :=
    exists_sourceCriticalRootRatio_lowerDogleg_curveIntegral_eq_zero
      hp hp1 ψ hreal n hopen
  refine ⟨min ε₁ (min ε₂ ε₃),lt_min hε₁ (lt_min hε₂ hε₃),?_⟩
  intro y hy left crossing right hleft hright hcross hlower
  have hy₂ : y ∈ Ioo (0:ℝ) ε₂ :=
    ⟨hy.1,hy.2.trans_le ((min_le_right ε₁ (min ε₂ ε₃)).trans
      (min_le_left ε₂ ε₃))⟩
  have hy₃ : y ∈ Ioo (0:ℝ) ε₃ :=
    ⟨hy.1,hy.2.trans_le ((min_le_right ε₁ (min ε₂ ε₃)).trans
      (min_le_right ε₂ ε₃))⟩
  have hleft₁ : IsCurvedEndpointConnector D ε₁ left := by
    obtain ⟨hs,hd,hn,k,hk,hr⟩ := hleft
    refine ⟨hs,hd,?_,k,hk,hr⟩
    exact fun t ht => ⟨(hn t ht).1,
      (hn t ht).2.trans (min_le_left ε₁ (min ε₂ ε₃))⟩
  have hright₁ : IsCurvedEndpointConnector D ε₁ right := by
    obtain ⟨hs,hd,hn,k,hk,hr⟩ := hright
    refine ⟨hs,hd,?_,k,hk,hr⟩
    exact fun t ht => ⟨(hn t ht).1,
      (hn t ht).2.trans (min_le_left ε₁ (min ε₂ ε₃))⟩
  have hcrossdom : range crossing ⊆ D := by
    rintro z ⟨u,rfl⟩
    exact sourceCanonicalRootDomain_of_im_ne_zero hp hp1 ψ hreal _
      (ne_of_lt (hlower u))
  have hcurvedEq := hcurved left crossing right hleft₁ hright₁
    (hcross.of_le (by norm_num)) hcrossdom
  have hstraightEq := (hstraight y hy₂).2
  have hzeroEq := hzero y hy₃
  have hcrossEq := sourceCriticalRootRatio_lowerPathIntegral_eq_horizontal
    hp hp1 ψ hreal n (-y) (neg_lt_zero.mpr hy.1) crossing hcross hlower
  constructor
  · exact hcurvedEq.1
  · change (∫ᶜ z in sourceCurvedGapDetourPath left crossing right, ω z) = _
    rw [hcurvedEq.2, hcrossEq]
    have hcancel :
        (∫ᶜ z in Path.segment l (l+((-y:ℝ):ℂ)*Complex.I), ω z) +
        sourceCriticalRootRatio_horizontalIntegral hp hp1 ψ n (-y) -
        (∫ᶜ z in Path.segment r (r+((-y:ℝ):ℂ)*Complex.I), ω z) = 0 := by
      rw [← hstraightEq]
      exact hzeroEq
    apply eq_of_sub_eq_zero
    linear_combination hcancel

end NLS.ZakharovShabat
