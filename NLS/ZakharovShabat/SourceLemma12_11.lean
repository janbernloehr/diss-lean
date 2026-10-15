import NLS.ZakharovShabat.SourcePsiOriginalNormalization
import NLS.ZakharovShabat.SourcePsiOriginalOuterProduct

/-!
# Lemma 12.11 on exactly the domain and family of Lemma 12.10

Every original diagonal period is 2π on the unchanged common complex W.
The package retains all of Lemma 12.10, including its original real roots,
source domain, and local disk placement, and the large-circle proof identity.
-/

noncomputable section
open Set Complex Filter Topology Metric NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

structure SourceLemma12_11Data (hp : p ≠ ⊤) (hp1 : 1 < p)
    (W₀ W : Set (CoeffPair p)) (s : (n : ℤ) → CoeffPair p → DeletedCoeff p n) : Prop where
  previous : SourceLemma12_10Data hp hp1 W₀ W s
  circle : ∀ ψ ∈ W, ∀ n : ℤ, ∀ P : SourceCriticalRootPeriodCircle hp hp1 ψ n,
    (∮ z in C((P.center:ℂ),P.radius),
      sourcePsiContourIntegrandJoint hp hp1 n (z,((s n ψ:Coeff p),ψ))) = (2*Real.pi:ℂ)
  circuit : ∀ {V : Set (CoeffPair p)} {D : ℤ → Set ℂ} {c : ℝ},
    SourceIsolatingNeighborhoods hp hp1 V D c → ∀ ψ ∈ W, ψ ∈ V → ∀ n : ℤ,
      ∀ Γ : PiecewiseC1Loop, Γ.Inside (D n \ sourcePeriodicSegment hp hp1 ψ n) →
        Γ.windingIntegral (sourceStandardRootMidpoint hp hp1 ψ n) = 1 →
          Γ.integral (fun z => sourcePsiCandidate n (z,(s n ψ:Coeff p))/sourceCanonicalRoot hp hp1 ψ z) =
            (2*Real.pi:ℂ)
  outer_eq : ∀ ψ ∈ W, ∀ n : ℤ, ∀ P : SourceCriticalRootPeriodCircle hp hp1 ψ n,
    ∀ᶠ k : ℕ in atTop,
      (∮ z in C(0,centralCircleRadius k),
        sourcePsiContourIntegrandJoint hp hp1 n (z,((s n ψ:Coeff p),ψ))) =
      (∮ z in C((P.center:ℂ),P.radius),
        sourcePsiContourIntegrandJoint hp hp1 n (z,((s n ψ:Coeff p),ψ)))

/-- Extend the retained result with exact periods without altering either domain or any root map. -/
theorem SourceLemma12_10Data.lemma12_11
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W : Set (CoeffPair p)}
    {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
    (H : SourceLemma12_10Data hp hp1 W₀ W s) (hW₀ : IsOpen W₀) :
    SourceLemma12_11Data hp hp1 W₀ W s :=
  ⟨H,H.original_diagonal_raw_circle hW₀,
    fun hD => H.original_diagonal_raw_circuit hW₀ hD,H.eventually_original_raw_outer_eq hW₀⟩

/-- The diagonal source normalization for every finite exponent greater than one. -/
theorem sourceLemma12_11 (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W₀ : Set (CoeffPair p), IsOpen W₀ ∧ IsConnected W₀ ∧ realTypeSourceLocus p ⊆ W₀ ∧
      ∃ W : Set (CoeffPair p), IsOpen W ∧ IsSimplyConnected W ∧ realTypeSourceLocus p ⊆ W ∧
        ∃ s : (n : ℤ) → CoeffPair p → DeletedCoeff p n, SourceLemma12_11Data hp hp1 W₀ W s := by
  obtain ⟨W₀,ho,hc,hr,W,hW,hs,hrW,s,H⟩ := sourceLemma12_10 hp hp1
  exact ⟨W₀,ho,hc,hr,W,hW,hs,hrW,s,H.lemma12_11 ho⟩

end NLS.ZakharovShabat
