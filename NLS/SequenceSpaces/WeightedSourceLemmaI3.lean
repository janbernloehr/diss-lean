import NLS.SequenceSpaces.SourceLemmaI3
import NLS.SequenceSpaces.Weighted

/-! # I.3 on weighted coefficient spaces, with raw pointwise bounds -/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.WeightedCoeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The symmetric complementary projection in the original weighted norm. -/
def sourceI3Tail (w : Weight) (N : ℕ) (a : WeightedCoeff w p) : WeightedCoeff w p :=
  a-truncate w p (Finset.Icc (-(N : ℤ)) N) a

/-- Weighting preserves the exact symmetric tail. -/
theorem weightEquiv_sourceI3Tail (w : Weight) (N : ℕ) (a : WeightedCoeff w p) :
    weightEquiv w p (sourceI3Tail w N a) = Coeff.sourceI3Tail N (weightEquiv w p a) := by
  simp only [sourceI3Tail,map_sub,truncate,LinearEquiv.apply_symm_apply,Coeff.sourceI3Tail_eq]

/-- No norm comparison constant is lost when transporting the tail criterion. -/
theorem norm_sourceI3Tail (w : Weight) (N : ℕ) (a : WeightedCoeff w p) :
    ‖sourceI3Tail w N a‖ = ‖Coeff.sourceI3Tail N (weightEquiv w p a)‖ := by
  rw [norm_eq,weightEquiv_sourceI3Tail]

/-- The full criterion holds for every positive weight, using the raw source coefficients. -/
theorem sourceLemmaI3 (hp : p ≠ ⊤) (w : Weight) (B : Set (WeightedCoeff w p)) :
    TotallyBounded B ↔
      (∀ n : ℤ, ∃ C : ℝ, ∀ a ∈ B, ‖a.val n‖ ≤ C) ∧
      (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, 1 ≤ N ∧ ∀ a ∈ B, ‖sourceI3Tail w N a‖ ≤ ε) := by
  have he : TotallyBounded ((weightEquiv w p) '' B) ↔ TotallyBounded B :=
    totallyBounded_image_iff (weightIsometry w p).isometry.isUniformInducing
  constructor
  · intro hB
    obtain ⟨_,ht⟩ := (Coeff.sourceLemmaI3 hp ((weightEquiv w p) '' B)).mp (he.mpr hB)
    constructor
    · obtain ⟨C,hC⟩ := hB.isBounded.exists_norm_le
      intro n
      exact ⟨C/w n,fun a ha => (norm_apply_le w p a n).trans
        (div_le_div_of_nonneg_right (hC a ha) (w.positive n).le)⟩
    · intro ε hε
      obtain ⟨N,hN,hbound⟩ := ht ε hε
      refine ⟨N,hN,fun a ha => ?_⟩
      rw [norm_sourceI3Tail]
      exact hbound _ ⟨a,ha,rfl⟩
  · rintro ⟨hb,ht⟩
    apply he.mp
    apply (Coeff.sourceLemmaI3 hp ((weightEquiv w p) '' B)).mpr
    constructor
    · intro n
      obtain ⟨C,hC⟩ := hb n
      refine ⟨w n*C,?_⟩
      rintro b ⟨a,ha,rfl⟩
      simp only [weightEquiv_apply,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (w.positive n)]
      exact mul_le_mul_of_nonneg_left (hC a ha) (w.positive n).le
    · intro ε hε
      obtain ⟨N,hN,hbound⟩ := ht ε hε
      refine ⟨N,hN,?_⟩
      rintro b ⟨a,ha,rfl⟩
      rw [← norm_sourceI3Tail]
      exact hbound a ha

/-- The weighted criterion applies to compact sets by adding closedness alone. -/
theorem sourceLemmaI3_compact (hp : p ≠ ⊤) (w : Weight) (B : Set (WeightedCoeff w p)) :
    IsCompact B ↔ IsClosed B ∧
      (∀ n : ℤ, ∃ C : ℝ, ∀ a ∈ B, ‖a.val n‖ ≤ C) ∧
      (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, 1 ≤ N ∧ ∀ a ∈ B, ‖sourceI3Tail w N a‖ ≤ ε) := by
  constructor
  · intro hB
    exact ⟨hB.isClosed,(sourceLemmaI3 hp w B).mp hB.totallyBounded⟩
  · rintro ⟨hc,hb,ht⟩
    exact ((sourceLemmaI3 hp w B).mpr ⟨hb,ht⟩).isCompact_of_isClosed hc

end NLS.WeightedCoeff
