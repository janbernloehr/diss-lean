import NLS.ZakharovShabat.SourceLemma11_1

/-!
# The analytic collapsed-gap loci in Section 11

The set Z_n is the zero set of the actual squared canonical gap on the
unchanged domain W. Its defining function is analytic there, its relative
zero set is closed, and the indexed action vanishes on it.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The dissertation's Z_n, using the literal squared canonical gap. -/
def sourceActionGapZeroLocus (hp : p ≠ ⊤) (hp1 : 1 < p)
    (W : Set (CoeffPair p)) (n : ℤ) : Set (CoeffPair p) :=
  {ψ | ψ ∈ W ∧
    (canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)^2 = 0}

@[simp] theorem mem_sourceActionGapZeroLocus_iff (hp : p ≠ ⊤) (hp1 : 1 < p)
    (W : Set (CoeffPair p)) (n : ℤ) (ψ : CoeffPair p) :
    ψ ∈ sourceActionGapZeroLocus hp hp1 W n ↔ ψ ∈ W ∧
      canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n = 0 := by
  simp [sourceActionGapZeroLocus]

/-- The defining function is analytic on the same W, not a new real-base domain. -/
theorem SourceLemma11_1Data.squared_gap_analytic
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceLemma11_1Data hp hp1 W) (n : ℤ) :
    AnalyticOnNhd ℂ (fun ψ : CoeffPair p =>
      (canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)^2) W := by
  have Hq : SourceEquation2_15Data hp hp1 W :=
    H.previous.previous.previous.previous.previous.previous
  exact Hq.previous.previous.previous.previous.roots.roots.symmetric.squared_gap n

/-- A single analytic equation defines Z_n throughout W. -/
theorem sourceActionGapZeroLocus_eq_preimage (hp : p ≠ ⊤) (hp1 : 1 < p)
    (W : Set (CoeffPair p)) (n : ℤ) :
    sourceActionGapZeroLocus hp hp1 W n = W ∩
      (fun ψ : CoeffPair p =>
        (canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)^2) ⁻¹' {0} := rfl

/-- The analytic zero locus is closed relative to W. -/
theorem SourceLemma11_1Data.gapZeroLocus_isClosed
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceLemma11_1Data hp hp1 W) (n : ℤ) :
    IsClosed {ψ : W | ψ.1 ∈ sourceActionGapZeroLocus hp hp1 W n} := by
  have hc := continuousOn_iff_continuous_domRestrict.mp (H.squared_gap_analytic n).continuousOn
  have hz := isClosed_eq hc (continuous_const (y := (0 : ℂ)))
  simpa [sourceActionGapZeroLocus, Set.domRestrict] using! hz

/-- The complex action vanishes on every point of Z_n. -/
theorem SourceLemma11_1Data.action_zero_on_gapZeroLocus
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceLemma11_1Data hp hp1 W) (n : ℤ) :
    EqOn (sourceIndexedAction hp hp1 n) (fun _ => 0) (sourceActionGapZeroLocus hp hp1 W n) := by
  intro ψ hψ
  obtain ⟨hW,hg⟩ := (mem_sourceActionGapZeroLocus_iff hp hp1 W n ψ).mp hψ
  exact H.collapsed ψ hW n hg

end NLS.ZakharovShabat
