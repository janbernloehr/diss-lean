import NLS.ComplexAnalysis.LocalAnalyticSquareRoot
import NLS.ZakharovShabat.SourceSymmetricContour

/-! # Analytic half-gaps at arbitrary complex source points

The analytic squared gap determines local analytic endpoint branches
at every open complex gap. Their unordered pair and segment coincide
with the canonical endpoints even when those labels exchange places.
-/

noncomputable section
open Set Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- An analytic half-gap has exactly the actual unordered endpoints. -/
theorem sourcePeriodicEndpoint_pair_eq_of_halfGap_sq
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (m : ℤ) (d : ℂ)
    (hsq : d ^ 2 = (canonicalPeriodicGap hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ) m / 2) ^ 2) :
    let τ := canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m
    ({τ - d, τ + d} : Set ℂ) =
      {canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m,
        canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m} := by
  dsimp only
  have hl : canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m -
      canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m / 2 =
      canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m := by
    dsimp only [canonicalPeriodicMidpoint,canonicalPeriodicGap]; ring
  have hr : canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m +
      canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m / 2 =
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m := by
    dsimp only [canonicalPeriodicMidpoint,canonicalPeriodicGap]; ring
  rcases eq_or_eq_neg_of_sq_eq_sq d _ hsq with hd | hd
  · rw [hd,hl,hr]
  · rw [hd,sub_neg_eq_add,← sub_eq_add_neg,hr,hl,pair_comm]

/-- The cut does not depend on the local sign of the analytic half-gap. -/
theorem sourcePeriodicSegment_eq_of_halfGap_sq
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (m : ℤ) (d : ℂ)
    (hsq : d ^ 2 = (canonicalPeriodicGap hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ) m / 2) ^ 2) :
    let τ := canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m
    segment ℝ (τ - d) (τ + d) = sourcePeriodicSegment hp hp1 ψ m := by
  dsimp only
  have hl : canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m -
      canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m / 2 =
      canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m := by
    dsimp only [canonicalPeriodicMidpoint,canonicalPeriodicGap]; ring
  have hr : canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m +
      canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m / 2 =
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m := by
    dsimp only [canonicalPeriodicMidpoint,canonicalPeriodicGap]; ring
  rcases eq_or_eq_neg_of_sq_eq_sq d _ hsq with hd | hd
  · rw [hd,hl,hr]; rfl
  · rw [hd,sub_neg_eq_add,← sub_eq_add_neg,hr,hl,segment_symm]; rfl

/-- A local half-gap is constructed from the actual analytic squared
gap at any complex source. Its base sign agrees with the canonical label. -/
theorem exists_local_sourceAnalyticHalfGap
    (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p)) (hW : IsOpen W)
    (φ : CoeffPair p) (hφ : φ ∈ W) (m : ℤ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) m ≠ 0)
    (hsq : AnalyticAt ℂ (fun ψ : CoeffPair p =>
      (canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m) ^ 2) φ) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧ V ⊆ W ∧
      ∃ δ : CoeffPair p → ℂ, AnalyticOnNhd ℂ δ V ∧
        δ φ = canonicalPeriodicGap hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) m / 2 ∧
        ∀ ψ ∈ V, δ ψ ≠ 0 ∧ δ ψ ^ 2 =
          (canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m / 2) ^ 2 := by
  let f : CoeffPair p → ℂ := fun ψ =>
    (canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m / 2) ^ 2
  let w := canonicalPeriodicGap hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) m / 2
  have hf : AnalyticAt ℂ f φ := by
    have heq : f = fun ψ =>
        (canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m) ^ 2 / 4 := by
      funext ψ; dsimp only [f]; ring
    rw [heq]
    exact hsq.div_const
  obtain ⟨O,hO,hφO,δ,hδ,hbase,hroots⟩ := exists_local_analytic_squareRoot f φ w hf
    (div_ne_zero hgap (by norm_num)) rfl
  exact ⟨O ∩ W,hO.inter hW,⟨hφO,hφ⟩,inter_subset_right,δ,
    hδ.mono inter_subset_left,hbase,fun ψ hψ => hroots ψ hψ.1⟩

end NLS.ZakharovShabat
