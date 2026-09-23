import NLS.ZakharovShabat.SourceAllIndexDisjointIsolation
import Mathlib.Analysis.Convex.PathConnected

/-!
# Connected real-type source locus

The real-type Fourier relation is closed under addition and real scalar
multiplication. Its source coefficient locus is convex and connected.
-/

noncomputable section
open Set Complex
open scoped ENNReal ComplexConjugate
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The real-type source coefficient locus. -/
def realTypeSourceLocus (p : ℝ≥0∞) [Fact (1 ≤ p)] : Set (CoeffPair p) :=
  {φ | IsRealType (CoeffPair.toMax p φ)}

omit [Fact (1 ≤ p)] in
/-- Real-type coefficient pairs are closed under addition. -/
theorem IsRealType.add {φ ψ : PairSpace p}
    (hφ : IsRealType φ) (hψ : IsRealType ψ) : IsRealType (φ + ψ) := by
  intro n
  change φ.2 n + ψ.2 n = conj (φ.1 (-n) + ψ.1 (-n))
  rw [map_add, ← hφ n, ← hψ n]

/-- The real-type source locus is convex over the real scalars. -/
theorem convex_realTypeSourceLocus : Convex ℝ (realTypeSourceLocus p) := by
  intro φ hφ ψ hψ a b ha hb hab
  change IsRealType (CoeffPair.toMax p (a • φ + b • ψ))
  change IsRealType (CoeffPair.toMax p ((a : ℂ) • φ + (b : ℂ) • ψ))
  simpa only [map_add, map_smul] using
    ((hφ.ofReal_smul a).add (hψ.ofReal_smul b))

/-- The real-type source locus is connected. -/
theorem isConnected_realTypeSourceLocus : IsConnected (realTypeSourceLocus p) := by
  apply (convex_realTypeSourceLocus (p := p)).isConnected
  exact ⟨0, by simp [realTypeSourceLocus]⟩

end NLS.ZakharovShabat
