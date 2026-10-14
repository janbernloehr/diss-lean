import NLS.ZakharovShabat.SourceSection11OriginalEstimates
import NLS.ZakharovShabat.SourcePsiSquaredGapComplexRootAtlas
import NLS.ZakharovShabat.SourcePsiOriginalPeriods

/-!
# Theorem 12.1 on one common source neighborhood

One squared-gap root atlas supplies all deleted indices, analytic root
maps, exact periods and locally uniform ℓᵖ offsets at every complex
source. It is constructed inside the retained Section 11 domain.
-/

noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The original canonical-root domain already supports every psi integrand. -/
theorem SourceSection11OriginalEstimates.psiIntegrand_joint
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceSection11OriginalEstimates hp hp1 W) (n : ℤ) :
    IsOpen (sourcePsiContourJointDomain hp hp1 W) ∧
      AnalyticOnNhd ℂ (sourcePsiContourIntegrandJoint hp hp1 n) (sourcePsiContourJointDomain hp hp1 W) := by
  have hroot := H.previous.previous.criticalOffsets.previous.previous.joint
  exact ⟨hroot.1.preimage (continuous_fst.prodMk (continuous_snd.comp continuous_snd)),
    sourcePsiContourIntegrandJoint_analyticOnNhd hp hp1 n W hroot.2⟩

/-- The simultaneous psi family, retaining the original source domain and all preceding results. -/
structure SourceTheorem12_1Data (hp : p ≠ ⊤) (hp1 : 1 < p)
    (W₀ W : Set (CoeffPair p)) (s : (n : ℤ) → CoeffPair p → DeletedCoeff p n) : Prop where
  previous : SourceSection11OriginalEstimates hp hp1 W₀
  subset : W ⊆ W₀
  analytic : ∀ n : ℤ, AnalyticOnNhd ℂ (s n) W
  real_agreement : ∀ n : ℤ, ∀ φ : realTypeSourceLocus p, s n φ.val = sourcePsiGapRoot hp hp1 n φ
  locally_uniform_offsets : ∀ φ ∈ W,
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧ V ⊆ W ∧
      ∃ C : ℝ, 0 < C ∧ ∀ ψ ∈ V, ∀ n : ℤ, ∃ a : Coeff p, a n = 0 ∧
        (∀ m : ℤ, m ≠ n → displacedRoots (s n ψ : Coeff p) m =
          sourceStandardRootMidpoint hp hp1 ψ m+(sourcePeriodicGapDisplacement hp hp1 ψ m)^2*a m) ∧ ‖a‖ ≤ C
  period : ∀ ψ ∈ W, ∀ n m : ℤ, ∀ D : SourceCriticalRootPeriodCircle hp hp1 ψ m,
    sourcePsiContour hp hp1 n (s n ψ : Coeff p) ψ (D.center:ℂ) D.radius = if m = n then 1 else 0

/-- Theorem 12.1 is constructed within any existing original open source domain. -/
theorem SourceSection11OriginalEstimates.psiFunctions
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ : Set (CoeffPair p)}
    (H : SourceSection11OriginalEstimates hp hp1 W₀) (hW : IsOpen W₀)
    (hR : realTypeSourceLocus p ⊆ W₀) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ IsSimplyConnected W ∧ realTypeSourceLocus p ⊆ W ∧
      ∃ s : (n : ℤ) → CoeffPair p → DeletedCoeff p n, SourceTheorem12_1Data hp hp1 W₀ W s := by
  obtain ⟨A⟩ := nonempty_sourcePsiSquaredGapComplexRootAtlas hp hp1 W₀ hW hR
  let B := A.toSourcePsiComplexRootAtlas
  exact ⟨B.domain,B.isOpen_domain,B.isSimplyConnected_domain,B.realType_subset_domain,B.branch,
    H,A.toSourcePsiIsolatingComplexRootAtlas.domain_subset,B.analytic,B.eq_sourcePsiGapRoot_of_real,
    A.locally_uniform_squared_gap_offsets,
    fun ψ hψ n m D => A.toSourcePsiIsolatingComplexRootAtlas.periodCircle_orthogonality
      W₀ (Subset.refl _) H.psiIntegrand_joint ψ hψ n m D⟩

namespace SourceTheorem12_1Data
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- General winding form of (2.21), for every original isolating family. -/
theorem circuit_winding (H : SourceTheorem12_1Data hp hp1 W₀ W s)
    {V : Set (CoeffPair p)} {D : ℤ → Set ℂ} {c : ℝ}
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (hψV : ψ ∈ V) (n m : ℤ)
    (Γ : PiecewiseC1Loop) (hΓ : Γ.Inside (D m \ sourcePeriodicSegment hp hp1 ψ m)) :
    sourcePsiCircuit hp hp1 n (s n ψ : Coeff p) ψ Γ =
      (if m = n then 1 else 0)*Γ.windingIntegral
        (canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m) := by
  obtain ⟨a,r,hr,he⟩ := hD.discs m
  let P := hD.periodCircle ψ hψV m a r hr he
  rw [P.psiCircuit_eq_mul_winding n _ Γ (by
    change Γ.Inside (ball (a:ℂ) r \ sourcePeriodicSegment hp hp1 ψ m)
    rwa [← he]),H.period ψ hψ n m P]

/-- Equation (2.21) with the literal factor 1/(2π), integrand and original circuit. -/
theorem circuit (H : SourceTheorem12_1Data hp hp1 W₀ W s)
    {V : Set (CoeffPair p)} {D : ℤ → Set ℂ} {c : ℝ}
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (hψV : ψ ∈ V) (n m : ℤ)
    (Γ : PiecewiseC1Loop) (hΓ : Γ.Inside (D m \ sourcePeriodicSegment hp hp1 ψ m))
    (hw : Γ.windingIntegral
      (canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m) = 1) :
    (2*Real.pi:ℂ)⁻¹*Γ.integral
      (fun z => sourcePsiCandidate n (z,(s n ψ : Coeff p))/sourceCanonicalRoot hp hp1 ψ z) =
        if m = n then 1 else 0 := by
  change sourcePsiCircuit hp hp1 n (s n ψ : Coeff p) ψ Γ = _
  rw [H.circuit_winding hD ψ hψ hψV n m Γ hΓ,hw,mul_one]

end SourceTheorem12_1Data

/-- One original domain and one common psi neighborhood for every finite p>1. -/
theorem sourceTheorem12_1 (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W₀ : Set (CoeffPair p), IsOpen W₀ ∧ IsConnected W₀ ∧ realTypeSourceLocus p ⊆ W₀ ∧
      ∃ W : Set (CoeffPair p), IsOpen W ∧ IsSimplyConnected W ∧ realTypeSourceLocus p ⊆ W ∧
        ∃ s : (n : ℤ) → CoeffPair p → DeletedCoeff p n, SourceTheorem12_1Data hp hp1 W₀ W s := by
  obtain ⟨W₀,ho,hc,hr,H⟩ := sourceSection11OriginalEstimates hp hp1
  exact ⟨W₀,ho,hc,hr,H.psiFunctions ho hr⟩

end NLS.ZakharovShabat
