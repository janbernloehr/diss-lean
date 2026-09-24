import NLS.ZakharovShabat.SourceCriticalRootRatioCurvedConnectorPrimitiveLimit
import NLS.ZakharovShabat.SourceCriticalRootRatioCurvedEndpointDetour

/-!
# Endpoint defect of a complete curved detour

For any curved endpoint-to-endpoint detour contained in one open
half-plane, primitive values telescope across the regular crossing.
Its integral is exactly the right connector's pathwise boundary value
minus the left connector's. This identifies the remaining boundary
comparison needed for exact vanishing.
-/

noncomputable section
open Set Filter Topology Complex
open scoped ENNReal unitInterval
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Every short curved upper detour has an integral equal to the
difference of the two pathwise endpoint limits of one primitive. -/
theorem exists_sourceCriticalRootRatio_upperCurvedDetour_primitive_defect
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
        ∀ F : ℂ → ℂ,
          (∀ z : ℂ, 0 < z.im → HasDerivAt F (f z) z) →
          ∃ Aleft Aright : ℂ,
            Tendsto (F ∘ left.extend) (𝓝[>] (0:ℝ)) (𝓝 Aleft) ∧
            Tendsto (F ∘ right.extend) (𝓝[>] (0:ℝ)) (𝓝 Aright) ∧
            CurveIntegrable (NLS.ComplexAnalysis.holomorphicOneForm f)
              (sourceCurvedGapDetourPath left crossing right) ∧
            (∫ᶜ z in sourceCurvedGapDetourPath left crossing right,
              NLS.ComplexAnalysis.holomorphicOneForm f z) = Aright - Aleft := by
  dsimp only
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let D := sourceCanonicalRootDomain hp hp1 ψ
  let f : ℂ → ℂ := fun z =>
    deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
      sourceCanonicalRoot hp hp1 ψ z
  let ω := NLS.ComplexAnalysis.holomorphicOneForm f
  obtain ⟨ε₁,hε₁,hconn⟩ :=
    exists_sourceCriticalRootRatio_upperCurvedConnector_primitive_limit
      hp hp1 ψ hreal n hopen
  obtain ⟨ε₂,hε₂,hdetour⟩ :=
    exists_sourceCriticalRootRatio_curvedGapDetour_integrable_integral_eq
      hp hp1 ψ hreal n hopen
  refine ⟨min ε₁ ε₂,lt_min hε₁ hε₂,?_⟩
  intro a b left crossing right hleft hright hleftU hrightU hcross hcrossU F hF
  have ha : 0 < a.im := by
    have := hcrossU 0
    simpa using this
  have hb : 0 < b.im := by
    have := hcrossU 1
    simpa using this
  have hleft₁ : IsCurvedEndpointConnector D ε₁ left := by
    obtain ⟨hs,hd,hn,k,hk,hr⟩ := hleft
    refine ⟨hs,hd,?_,k,hk,hr⟩
    exact fun t ht => ⟨(hn t ht).1,
      (hn t ht).2.trans (min_le_left ε₁ ε₂)⟩
  have hright₁ : IsCurvedEndpointConnector D ε₁ right := by
    obtain ⟨hs,hd,hn,k,hk,hr⟩ := hright
    refine ⟨hs,hd,?_,k,hk,hr⟩
    exact fun t ht => ⟨(hn t ht).1,
      (hn t ht).2.trans (min_le_left ε₁ ε₂)⟩
  have hleft₂ : IsCurvedEndpointConnector D ε₂ left := by
    obtain ⟨hs,hd,hn,k,hk,hr⟩ := hleft
    refine ⟨hs,hd,?_,k,hk,hr⟩
    exact fun t ht => ⟨(hn t ht).1,
      (hn t ht).2.trans (min_le_right ε₁ ε₂)⟩
  have hright₂ : IsCurvedEndpointConnector D ε₂ right := by
    obtain ⟨hs,hd,hn,k,hk,hr⟩ := hright
    refine ⟨hs,hd,?_,k,hk,hr⟩
    exact fun t ht => ⟨(hn t ht).1,
      (hn t ht).2.trans (min_le_right ε₁ ε₂)⟩
  obtain ⟨Aleft,hAl,_,hlval⟩ := hconn l (by
    change l = l ∨ l = r
    exact Or.inl rfl) left
    hleft₁.1 hleftU ha hleft₁.2.2.1 hleft₁.2.2.2 F hF
  obtain ⟨Aright,hAr,_,hrval⟩ := hconn r (by
    change r = l ∨ r = r
    exact Or.inr rfl) right
    hright₁.1 hrightU hb hright₁.2.2.1 hright₁.2.2.2 F hF
  have hcrossDom : range crossing ⊆ D := by
    rintro z ⟨u,rfl⟩
    exact sourceCanonicalRootDomain_of_im_ne_zero hp hp1 ψ hreal _
      (ne_of_gt (hcrossU u))
  have hdetourResult := hdetour left crossing right hleft₂ hright₂
    hcross hcrossDom
  have hdetourEq := hdetourResult.2
  have hcrossInt : CurveIntegrable ω crossing :=
    sourceCriticalRootRatio_curveIntegrable_of_smoothPath hp hp1 ψ
      crossing hcross hcrossDom
  have hcrossWithin (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      0 < (crossing.extend t).im := by
    rw [Path.extend_apply crossing ht]
    exact hcrossU ⟨t,ht⟩
  have hcrossVal : (∫ᶜ z in crossing, ω z) = F b - F a :=
    NLS.ComplexAnalysis.curveIntegral_eq_sub_of_primitive
      f F {z : ℂ | 0 < z.im} (fun z hz => hF z hz)
      crossing hcross hcrossWithin hcrossInt
  refine ⟨Aleft,Aright,hAl,hAr,hdetourResult.1,?_⟩
  rw [hdetourEq, hlval, hrval, hcrossVal]
  ring

/-- Every short curved lower detour has an integral equal to the
difference of the two pathwise endpoint limits of one primitive. -/
theorem exists_sourceCriticalRootRatio_lowerCurvedDetour_primitive_defect
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
        ∀ F : ℂ → ℂ,
          (∀ z : ℂ, z.im < 0 → HasDerivAt F (f z) z) →
          ∃ Aleft Aright : ℂ,
            Tendsto (F ∘ left.extend) (𝓝[>] (0:ℝ)) (𝓝 Aleft) ∧
            Tendsto (F ∘ right.extend) (𝓝[>] (0:ℝ)) (𝓝 Aright) ∧
            CurveIntegrable (NLS.ComplexAnalysis.holomorphicOneForm f)
              (sourceCurvedGapDetourPath left crossing right) ∧
            (∫ᶜ z in sourceCurvedGapDetourPath left crossing right,
              NLS.ComplexAnalysis.holomorphicOneForm f z) = Aright - Aleft := by
  dsimp only
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let D := sourceCanonicalRootDomain hp hp1 ψ
  let f : ℂ → ℂ := fun z =>
    deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
      sourceCanonicalRoot hp hp1 ψ z
  let ω := NLS.ComplexAnalysis.holomorphicOneForm f
  obtain ⟨ε₁,hε₁,hconn⟩ :=
    exists_sourceCriticalRootRatio_lowerCurvedConnector_primitive_limit
      hp hp1 ψ hreal n hopen
  obtain ⟨ε₂,hε₂,hdetour⟩ :=
    exists_sourceCriticalRootRatio_curvedGapDetour_integrable_integral_eq
      hp hp1 ψ hreal n hopen
  refine ⟨min ε₁ ε₂,lt_min hε₁ hε₂,?_⟩
  intro a b left crossing right hleft hright hleftU hrightU hcross hcrossU F hF
  have ha : a.im < 0 := by
    have := hcrossU 0
    simpa using this
  have hb : b.im < 0 := by
    have := hcrossU 1
    simpa using this
  have hleft₁ : IsCurvedEndpointConnector D ε₁ left := by
    obtain ⟨hs,hd,hn,k,hk,hr⟩ := hleft
    refine ⟨hs,hd,?_,k,hk,hr⟩
    exact fun t ht => ⟨(hn t ht).1,
      (hn t ht).2.trans (min_le_left ε₁ ε₂)⟩
  have hright₁ : IsCurvedEndpointConnector D ε₁ right := by
    obtain ⟨hs,hd,hn,k,hk,hr⟩ := hright
    refine ⟨hs,hd,?_,k,hk,hr⟩
    exact fun t ht => ⟨(hn t ht).1,
      (hn t ht).2.trans (min_le_left ε₁ ε₂)⟩
  have hleft₂ : IsCurvedEndpointConnector D ε₂ left := by
    obtain ⟨hs,hd,hn,k,hk,hr⟩ := hleft
    refine ⟨hs,hd,?_,k,hk,hr⟩
    exact fun t ht => ⟨(hn t ht).1,
      (hn t ht).2.trans (min_le_right ε₁ ε₂)⟩
  have hright₂ : IsCurvedEndpointConnector D ε₂ right := by
    obtain ⟨hs,hd,hn,k,hk,hr⟩ := hright
    refine ⟨hs,hd,?_,k,hk,hr⟩
    exact fun t ht => ⟨(hn t ht).1,
      (hn t ht).2.trans (min_le_right ε₁ ε₂)⟩
  obtain ⟨Aleft,hAl,_,hlval⟩ := hconn l (by
    change l = l ∨ l = r
    exact Or.inl rfl) left
    hleft₁.1 hleftU ha hleft₁.2.2.1 hleft₁.2.2.2 F hF
  obtain ⟨Aright,hAr,_,hrval⟩ := hconn r (by
    change r = l ∨ r = r
    exact Or.inr rfl) right
    hright₁.1 hrightU hb hright₁.2.2.1 hright₁.2.2.2 F hF
  have hcrossDom : range crossing ⊆ D := by
    rintro z ⟨u,rfl⟩
    exact sourceCanonicalRootDomain_of_im_ne_zero hp hp1 ψ hreal _
      (ne_of_lt (hcrossU u))
  have hdetourResult := hdetour left crossing right hleft₂ hright₂
    hcross hcrossDom
  have hdetourEq := hdetourResult.2
  have hcrossInt : CurveIntegrable ω crossing :=
    sourceCriticalRootRatio_curveIntegrable_of_smoothPath hp hp1 ψ
      crossing hcross hcrossDom
  have hcrossWithin (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      (crossing.extend t).im < 0 := by
    rw [Path.extend_apply crossing ht]
    exact hcrossU ⟨t,ht⟩
  have hcrossVal : (∫ᶜ z in crossing, ω z) = F b - F a :=
    NLS.ComplexAnalysis.curveIntegral_eq_sub_of_primitive
      f F {z : ℂ | z.im < 0} (fun z hz => hF z hz)
      crossing hcross hcrossWithin hcrossInt
  refine ⟨Aleft,Aright,hAl,hAr,hdetourResult.1,?_⟩
  rw [hdetourEq, hlval, hrval, hcrossVal]
  ring

end NLS.ZakharovShabat
