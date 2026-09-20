import NLS.ZakharovShabat.PeriodicEndpointLabeling

/-!
# Sorting each periodic endpoint pair

Lexicographic comparison orders the two slots. Swapping slots preserves
all spectral data, and each new displacement is bounded by the sum of
the original displacement norms, so both remain in lp.
-/

noncomputable section
open NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.ZakharovShabat

/-- The first endpoint in lexicographic order. -/
def orderedEndpointLeft (x y : ℂ) : ℂ := if complexLexLE x y then x else y

/-- The second endpoint in lexicographic order. -/
def orderedEndpointRight (x y : ℂ) : ℂ := if complexLexLE x y then y else x

/-- The sorted pair retains its entire multiset, including coincident endpoints. -/
theorem orderedEndpointPair_multiset (x y : ℂ) :
    ({orderedEndpointLeft x y,orderedEndpointRight x y} : Multiset ℂ) = {x,y} := by
  unfold orderedEndpointLeft orderedEndpointRight
  split_ifs
  · rfl
  · exact Multiset.pair_comm _ _

/-- The first sorted slot never exceeds the second in lexicographic order. -/
theorem orderedEndpointPair_le (x y : ℂ) : complexLexLE (orderedEndpointLeft x y) (orderedEndpointRight x y) := by
  unfold orderedEndpointLeft orderedEndpointRight
  split_ifs with h
  · exact h
  · exact (le_total (complexLexKey x) (complexLexKey y)).resolve_left h

/-- Sorting both slots preserves the lp displacement class at every exponent. -/
theorem memℓp_orderedEndpoint_displacements {p : ℝ≥0∞} (ξ η c : ℤ → ℂ)
    (hξ : Memℓp (fun n => ξ n-c n) p) (hη : Memℓp (fun n => η n-c n) p) :
    Memℓp (fun n => orderedEndpointLeft (ξ n) (η n)-c n) p ∧
      Memℓp (fun n => orderedEndpointRight (ξ n) (η n)-c n) p := by
  have hb := hξ.norm.add hη.norm
  constructor
  · apply hb.mono
    intro n
    unfold orderedEndpointLeft
    split_ifs
    · exact le_add_of_nonneg_right (norm_nonneg _)
    · exact le_add_of_nonneg_left (norm_nonneg _)
  · apply hb.mono
    intro n
    unfold orderedEndpointRight
    split_ifs
    · exact le_add_of_nonneg_left (norm_nonneg _)
    · exact le_add_of_nonneg_right (norm_nonneg _)

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A sorted distant pair has the same actual spectral data as the original pair. -/
theorem PeriodicEndpointPair.ordered {hp : p ≠ ⊤} {φ : PairSpace p} {n : ℤ} {x y : ℂ}
    (h : PeriodicEndpointPair hp φ n x y) :
    PeriodicEndpointPair hp φ n (orderedEndpointLeft x y) (orderedEndpointRight x y) := by
  unfold orderedEndpointLeft orderedEndpointRight
  split_ifs
  · exact h
  · exact h.swap

/-- Sorting every pair preserves a complete endpoint labeling. -/
theorem PeriodicEndpointLabeling.ordered_pairs {hp : p ≠ ⊤} {φ : PairSpace p} {N : ℕ} {ξ η : ℤ → ℂ}
    (h : PeriodicEndpointLabeling hp φ N ξ η) :
    PeriodicEndpointLabeling hp φ N (fun n => orderedEndpointLeft (ξ n) (η n))
      (fun n => orderedEndpointRight (ξ n) (η n)) := by
  have hlp := memℓp_orderedEndpoint_displacements ξ η (fun n => (Real.pi : ℂ)*n)
    h.left_displacement h.right_displacement
  refine ⟨h.counting,⟨?_⟩,fun n hn => (h.distant n hn).ordered,hlp.1,hlp.2⟩
  simpa only [orderedEndpointPair_multiset] using h.central.roots

end NLS.ZakharovShabat
