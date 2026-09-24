import NLS.ZakharovShabat.SourceCriticalRootRatioCurvedEndpointConnector
import NLS.ZakharovShabat.SourceCriticalRootRatioStadiumIntegral

/-!
# Integrable endpoint-to-endpoint paths with curved connectors

Two linearly departing, gap-avoiding curved connectors can be joined by
any smooth gap-avoiding crossing. The resulting actual path between
singular branch points is curve-integrable, and its integral splits
into the signed integrals of the three pieces.
-/

noncomputable section
open Set Complex
open scoped ENNReal unitInterval
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A smooth connector that leaves its starting point at a linear
rate while remaining in a punctured gap-avoiding neighborhood. -/
def IsCurvedEndpointConnector
    (D : Set ℂ) (ε : ℝ) {c b : ℂ} (γ : Path c b) : Prop :=
  ContDiffOn ℝ 1 γ.extend (Icc 0 1) ∧
    (∀ t ∈ Ioo (0:ℝ) 1, γ.extend t ∈ D) ∧
    (∀ t ∈ Ioo (0:ℝ) 1,
      0 < ‖c-γ.extend t‖ ∧ ‖c-γ.extend t‖ ≤ ε) ∧
    (∃ k : ℝ, 0 < k ∧ ∀ t ∈ Ioo (0:ℝ) 1,
      k*t ≤ ‖c-γ.extend t‖)

/-- Start at the left singular endpoint, traverse a regular crossing,
then follow the right connector backwards to the other endpoint. -/
def sourceCurvedGapDetourPath
    {l r a b : ℂ} (left : Path l a) (crossing : Path a b)
    (right : Path r b) : Path l r :=
  (left.trans crossing).trans right.symm

/-- Short curved connectors at both ends of an open real-type gap
produce genuine integrable endpoint-to-endpoint paths. The crossing
may be any smooth path in the root domain. -/
theorem exists_sourceCriticalRootRatio_curvedGapDetour_integrable_integral_eq
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
    ∃ ε : ℝ, 0 < ε ∧ ∀ {a b : ℂ}
      (left : Path l a) (crossing : Path a b) (right : Path r b),
        IsCurvedEndpointConnector D ε left →
        IsCurvedEndpointConnector D ε right →
        ContDiffOn ℝ 1 crossing.extend (Icc 0 1) →
        range crossing ⊆ D →
        CurveIntegrable ω (sourceCurvedGapDetourPath left crossing right) ∧
          (∫ᶜ z in sourceCurvedGapDetourPath left crossing right, ω z) =
            (∫ᶜ z in left, ω z) +
            (∫ᶜ z in crossing, ω z) -
            (∫ᶜ z in right, ω z) := by
  dsimp only
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let D := sourceCanonicalRootDomain hp hp1 ψ
  let ω := NLS.ComplexAnalysis.holomorphicOneForm
    (fun z => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
      sourceCanonicalRoot hp hp1 ψ z)
  obtain ⟨ε,hε,hconnector⟩ :=
    exists_sourceCriticalRootRatio_curvedEndpointConnector_curveIntegrable
      hp hp1 ψ hreal n hopen
  refine ⟨ε,hε,?_⟩
  intro a b left crossing right hleft hright hcross hcrossdom
  have hl : CurveIntegrable ω left :=
    hconnector l (by
      change l = l ∨ l = r
      exact Or.inl rfl) left hleft.1 hleft.2.1 hleft.2.2.1 hleft.2.2.2
  have hr : CurveIntegrable ω right :=
    hconnector r (by
      change r = l ∨ r = r
      exact Or.inr rfl) right hright.1 hright.2.1 hright.2.2.1 hright.2.2.2
  have hm : CurveIntegrable ω crossing :=
    sourceCriticalRootRatio_curveIntegrable_of_smoothPath
      hp hp1 ψ crossing hcross hcrossdom
  constructor
  · exact (hl.trans hm).trans hr.symm
  · change (∫ᶜ z in (left.trans crossing).trans right.symm, ω z) = _
    rw [curveIntegral_trans (hl.trans hm) hr.symm,
      curveIntegral_trans hl hm, curveIntegral_symm]
    ring

end NLS.ZakharovShabat
