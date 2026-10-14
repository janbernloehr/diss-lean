import NLS.ZakharovShabat.SourceActionChiContour

/-!
# Equation (2.18) on the unchanged common source domain

Retain Lemma 11.1 and package the literal deleted product's joint
analyticity on the moving-gap domain and on every original fixed disk
domain. The union in the latter is indexed by m, correcting the printed
U_n under a union over m≠n; see SOURCE_ERRATA.md.
-/

noncomputable section
open Set Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Equation (2.18), retaining the full preceding action package and domain. -/
structure SourceEquation2_18Data (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p)) : Prop where
  previous : SourceLemma11_1Data hp hp1 W
  joint : ∀ n : ℤ,
    AnalyticOnNhd ℂ (fun t : ℂ × CoeffPair p => sourceActionChi hp hp1 n t.2 t.1)
      (sourceStandardRootOmittedJointDomain hp hp1 W n)
  fixed : ∀ {V : Set (CoeffPair p)}, V ⊆ W → ∀ {D : ℤ → Set ℂ} {c : ℝ},
    SourceIsolatingNeighborhoods hp hp1 V D c → ∀ n : ℤ,
    AnalyticOnNhd ℂ (fun t : ℂ × CoeffPair p => sourceActionChi hp hp1 n t.2 t.1)
      ((⋃ m : ℤ, ⋃ (_ : m ≠ n), closure (D m))ᶜ ×ˢ V)
  disk : ∀ {V : Set (CoeffPair p)}, V ⊆ W → ∀ {D : ℤ → Set ℂ} {c : ℝ},
    SourceIsolatingNeighborhoods hp hp1 V D c → ∀ n : ℤ,
    AnalyticOnNhd ℂ (fun t : ℂ × CoeffPair p => sourceActionChi hp hp1 n t.2 t.1) (D n ×ˢ V)

/-- Upgrade an existing open W without replacing it or any of its original disks. -/
theorem SourceLemma11_1Data.actionChi
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceLemma11_1Data hp hp1 W) (hW : IsOpen W) : SourceEquation2_18Data hp hp1 W := by
  have h6 : SourceCorollary10_6Data hp hp1 W :=
    H.previous.previous.previous.previous.previous.previous.previous.previous.previous.previous
  refine ⟨H,h6.chi_joint hW,?_,?_⟩
  · intro V hVW D c hD n
    exact h6.chi_fixed hW hVW hD n
  · intro V hVW D c hD n
    exact h6.chi_disk hW hVW hD n

/-- Exact normalization of the actual quotient, with no selected-factor division. -/
theorem SourceEquation2_18Data.factorization
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (_H : SourceEquation2_18Data hp hp1 W) (ψ : CoeffPair p) (n : ℤ) (z : ℂ)
    (hz : z ∈ sourceCanonicalRootDomain hp hp1 ψ) :
    deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z / sourceCanonicalRoot hp hp1 ψ z =
      -Complex.I*((canonicalCriticalPoints hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n-z)/sourceStandardRoot hp hp1 ψ n z)*
          sourceActionChi hp hp1 n ψ z :=
  sourceCriticalRootRatio_eq_selectedFactor_mul_chi hp hp1 ψ n z hz

/-- The exact recentered formula on every admissible original circuit. -/
theorem SourceEquation2_18Data.circuit
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    (H : SourceEquation2_18Data hp hp1 W)
    {D : ℤ → Set ℂ} {c : ℝ} (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (ψ : CoeffPair p) (hψW : ψ ∈ W) (hψV : ψ ∈ V) (n : ℤ)
    (Γ : PiecewiseC1Loop) (hΓ : Γ.Inside (D n \ sourcePeriodicSegment hp hp1 ψ n))
    (hw : Γ.windingIntegral
      (canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n) = 1) :
    sourceIndexedAction hp hp1 n ψ = Complex.I/(Real.pi : ℂ)*Γ.integral (fun z =>
      (canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n-z)^2 /
        sourceStandardRoot hp hp1 ψ n z*sourceActionChi hp hp1 n ψ z) :=
  H.previous.action_eq_chi_circuit hD ψ hψW hψV n Γ hΓ hw

/-- The literal deleted product and recentered actions for every finite p>1. -/
theorem sourceEquation2_18 (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ IsConnected W ∧ realTypeSourceLocus p ⊆ W ∧
      SourceEquation2_18Data hp hp1 W := by
  obtain ⟨W,ho,hc,hr,H⟩ := sourceLemma11_1 hp hp1
  exact ⟨W,ho,hc,hr,H.actionChi ho⟩

end NLS.ZakharovShabat
