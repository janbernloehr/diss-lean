import NLS.ZakharovShabat.SourceHolomorphicRealGerm
import NLS.SequenceSpaces.PairExponentEmbedding

/-!
# Real-centered ball cores of complex source neighborhoods

Shrinking an open neighborhood of the real locus to its real-centered
balls preserves that locus. Real projection commutes with exponent
inclusion and contracts distance from real centers, allowing analytic
continuation across complex overlaps of exponent domains.
-/

noncomputable section
open Set Metric Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- The real-type projection commutes with coefficient exponent inclusion. -/
theorem sourceRealPart_exponent (hpq : p ≤ q) (ψ : CoeffPair p) :
    CoeffPair.exponentInclusion hpq (sourceRealPart ψ) =
      sourceRealPart (CoeffPair.exponentInclusion hpq ψ) := by
  have hc : CoeffPair.exponentInclusion hpq (sourceConjugation ψ) =
      sourceConjugation (CoeffPair.exponentInclusion hpq ψ) := by
    apply (CoeffPair.toMax q).injective
    apply Prod.ext <;> ext n <;> simp
  simp only [sourceRealPart,map_smul,map_add,hc]

/-- The union of all real-centered balls contained in a source domain. -/
def sourceRealBallCore (U : Set (CoeffPair p)) : Set (CoeffPair p) :=
  ⋃ φ : realTypeSourceLocus p, ⋃ r : ℝ, ⋃ (_ : ball φ.val r ⊆ U), ball φ.val r

/-- A union of real-centered balls is open. -/
theorem sourceRealBallCore_open (U : Set (CoeffPair p)) : IsOpen (sourceRealBallCore U) :=
  isOpen_iUnion fun _ => isOpen_iUnion fun _ => isOpen_iUnion fun _ => isOpen_ball

/-- The ball core lies in the original source domain. -/
theorem sourceRealBallCore_subset (U : Set (CoeffPair p)) : sourceRealBallCore U ⊆ U := by
  intro ψ hψ
  obtain ⟨φ,hφ⟩ := mem_iUnion.mp hψ
  obtain ⟨r,hr⟩ := mem_iUnion.mp hφ
  obtain ⟨hball,hψ⟩ := mem_iUnion.mp hr
  exact hball hψ

/-- Passing to the core preserves the whole real locus of an open neighborhood. -/
theorem sourceRealBallCore_real_subset (U : Set (CoeffPair p)) (hU : IsOpen U)
    (hr : realTypeSourceLocus p ⊆ U) : realTypeSourceLocus p ⊆ sourceRealBallCore U := by
  intro φ hφ
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds (hr hφ))
  exact mem_iUnion.mpr ⟨⟨φ,hφ⟩,mem_iUnion.mpr ⟨r,mem_iUnion.mpr ⟨hball,mem_ball_self hr⟩⟩⟩

/-- A domain made of real-centered balls is unchanged by taking its core. -/
theorem sourceRealBallCore_idem (U : Set (CoeffPair p)) :
    sourceRealBallCore (sourceRealBallCore U) = sourceRealBallCore U := by
  apply Subset.antisymm (sourceRealBallCore_subset _)
  intro ψ hψ
  obtain ⟨φ,hφ⟩ := mem_iUnion.mp hψ
  obtain ⟨r,hr⟩ := mem_iUnion.mp hφ
  obtain ⟨hball,hψ⟩ := mem_iUnion.mp hr
  have hb : ball φ.val r ⊆ sourceRealBallCore U := fun _ hx =>
    mem_iUnion.mpr ⟨φ,mem_iUnion.mpr ⟨r,mem_iUnion.mpr ⟨hball,hx⟩⟩⟩
  exact mem_iUnion.mpr ⟨φ,mem_iUnion.mpr ⟨r,mem_iUnion.mpr ⟨hb,hψ⟩⟩⟩

end NLS.ZakharovShabat
