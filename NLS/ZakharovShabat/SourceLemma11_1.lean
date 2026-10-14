import NLS.ZakharovShabat.SourceIndexedActionGradient

/-!
# Lemma 11.1 on the unchanged common source domain

The contour-independent indexed actions are analytic on W. Their exact
Fréchet gradients are the negative normalized discriminant-variation
integrals on every admissible counterclockwise piecewise C¹ circuit.
Every complex collapsed gap has zero action; on the real locus the
actions are real and nonnegative, with the stated zero-gap equivalence.
-/

noncomputable section
open Set Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The complete assertions of Lemma 11.1, retaining equation (2.16) and W. -/
structure SourceLemma11_1Data (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p)) : Prop where
  previous : SourceEquation2_16Data hp hp1 W
  gradient : ∀ {V : Set (CoeffPair p)}, IsOpen V →
    ∀ {D : ℤ → Set ℂ} {c : ℝ}, SourceIsolatingNeighborhoods hp hp1 V D c →
    ∀ ψ ∈ W, ψ ∈ V → ∀ n : ℤ, ∀ Γ : PiecewiseC1Loop,
    Γ.Inside (D n \ sourcePeriodicSegment hp hp1 ψ n) →
    Γ.windingIntegral
      (canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n) = 1 →
    ∀ v : CoeffPair p, (fderiv ℂ (sourceIndexedAction hp hp1 n) ψ) v =
      -(Real.pi : ℂ)⁻¹*Γ.integral (fun z =>
        (fderiv ℂ (fun χ : CoeffPair p => canonicalDiscriminant hp (periodOnePotential χ) z) ψ) v /
          sourceCanonicalRoot hp hp1 ψ z)
  collapsed : ∀ ψ ∈ W, ∀ n : ℤ,
    canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n = 0 →
      sourceIndexedAction hp hp1 n ψ = 0
  real_properties : ∀ φ : CoeffPair p, IsRealType (CoeffPair.toMax p φ) → ∀ n : ℤ,
    0 ≤ (sourceIndexedAction hp hp1 n φ).re ∧ (sourceIndexedAction hp hp1 n φ).im = 0 ∧
      (sourceIndexedAction hp hp1 n φ = 0 ↔
        canonicalPeriodicGap hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n = 0)

/-- The action-gradient theorem strengthens the existing package without shrinking W. -/
theorem SourceEquation2_16Data.actionGradients
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceEquation2_16Data hp hp1 W) : SourceLemma11_1Data hp hp1 W := by
  refine ⟨H,H.circuit_gradient,H.indexedAction_zero_of_gap_zero,?_⟩
  intro φ hφ n
  simpa only [sourcePeriodicGapDisplacement_apply] using!
    sourceIndexedAction_nonneg_and_eq_zero_iff_gap_zero hp hp1 n φ hφ

/-- An open real gap gives strictly positive action. -/
theorem SourceLemma11_1Data.action_pos_of_real_gap_ne_zero
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceLemma11_1Data hp hp1 W) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ)
    (hg : canonicalPeriodicGap hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n ≠ 0) :
    0 < (sourceIndexedAction hp hp1 n φ).re := by
  obtain ⟨hpos,him,hzero⟩ := H.real_properties φ hφ n
  apply lt_of_le_of_ne hpos
  intro he
  have ha : sourceIndexedAction hp hp1 n φ = 0 := Complex.ext he.symm him
  exact hg (hzero.mp ha)

/-- Lemma 11.1 for every finite p>1 on the unchanged open connected
neighborhood of the entire real-type source locus. -/
theorem sourceLemma11_1 (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ IsConnected W ∧ realTypeSourceLocus p ⊆ W ∧
      SourceLemma11_1Data hp hp1 W := by
  obtain ⟨W,ho,hc,hr,H⟩ := sourceEquation2_16 hp hp1
  exact ⟨W,ho,hc,hr,H.actionGradients⟩

end NLS.ZakharovShabat
