import NLS.ZakharovShabat.SourceSignedBlockCompact
import NLS.ZakharovShabat.NormalizedWeightedSourceTopology
import NLS.ZakharovShabat.SourceCompactSignedEntries

/-! # Compactness of weighted lifts of signed blocks

Decoding an even spectral weight cancels the same weight in both source
modes and the corresponding target mode. The four entries of the weighted
lift therefore equal the original tail entries. Their decay proves
compactness in the weighted topology via exact two-mode rows.
-/

noncomputable section
open Set Metric Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A bounded weighted lift of a compact signed-block operator is compact in the weighted norm. -/
theorem isCompactOperator_of_weighted_signed_block_lift
    (hp : p ≠ ⊤) (w : SpectralWeight)
    (T L : CoeffPair p →L[ℂ] (Coeff p × Coeff p)) (hL : IsCompactOperator L) (K : ℕ)
    (hrow : ∀ n : ℤ, K ≤ n.natAbs → ∀ a : CoeffPair p,
      (L a).1 n = a.fst (-n)*(L (CoeffPair.inlCLM (lp.single p (-n) 1))).1 n+
        a.snd n*(L (CoeffPair.inrCLM (lp.single p n 1))).1 n ∧
      (L a).2 n = a.fst (-n)*(L (CoeffPair.inlCLM (lp.single p (-n) 1))).2 n+
        a.snd n*(L (CoeffPair.inrCLM (lp.single p n 1))).2 n)
    (hcomp : ∀ a : CoeffPair p, ∀ n : ℤ,
      (T a).1 n/(w (2*n) : ℂ) = (L (normalizedWeightedSource w a)).1 n ∧
      (T a).2 n/(w (2*n) : ℂ) = (L (normalizedWeightedSource w a)).2 n) :
    IsCompactOperator T := by
  have hTrow (n : ℤ) (hn : K ≤ n.natAbs) (a : CoeffPair p) :
      (T a).1 n = a.fst (-n)*(L (CoeffPair.inlCLM (lp.single p (-n) 1))).1 n+
        a.snd n*(L (CoeffPair.inrCLM (lp.single p n 1))).1 n ∧
      (T a).2 n = a.fst (-n)*(L (CoeffPair.inlCLM (lp.single p (-n) 1))).2 n+
        a.snd n*(L (CoeffPair.inrCLM (lp.single p n 1))).2 n := by
    constructor
    · apply (div_left_inj' (w.toWeight.complex_ne_zero (2*n))).mp
      rw [(hcomp a n).1,(hrow n hn (normalizedWeightedSource w a)).1]
      simp only [normalizedWeightedSource_fst,normalizedWeightedSource_snd,mul_neg,SpectralWeight.apply_neg]
      ring
    · apply (div_left_inj' (w.toWeight.complex_ne_zero (2*n))).mp
      rw [(hcomp a n).2,(hrow n hn (normalizedWeightedSource w a)).2]
      simp only [normalizedWeightedSource_fst,normalizedWeightedSource_snd,mul_neg,SpectralWeight.apply_neg]
      ring
  have hTl (n : ℤ) (hn : K ≤ n.natAbs) :
      (T (CoeffPair.inlCLM (lp.single p (-n) 1))).1 n = (L (CoeffPair.inlCLM (lp.single p (-n) 1))).1 n ∧
      (T (CoeffPair.inlCLM (lp.single p (-n) 1))).2 n = (L (CoeffPair.inlCLM (lp.single p (-n) 1))).2 n := by
    simpa using hTrow n hn (CoeffPair.inlCLM (lp.single p (-n) 1))
  have hTr (n : ℤ) (hn : K ≤ n.natAbs) :
      (T (CoeffPair.inrCLM (lp.single p n 1))).1 n = (L (CoeffPair.inrCLM (lp.single p n 1))).1 n ∧
      (T (CoeffPair.inrCLM (lp.single p n 1))).2 n = (L (CoeffPair.inrCLM (lp.single p n 1))).2 n := by
    simpa using hTrow n hn (CoeffPair.inrCLM (lp.single p n 1))
  apply isCompactOperator_of_tail_signed_blocks T K
  · intro n hn a
    rw [(hTl n hn).1,(hTl n hn).2,(hTr n hn).1,(hTr n hn).2]
    exact hTrow n hn a
  · intro ε hε
    obtain ⟨K',hK'⟩ := exists_compactOperator_signed_block_entries_small hp L hL ε hε
    refine ⟨max K K',fun n hn => ?_⟩
    rw [(hTl n (by omega)).1,(hTl n (by omega)).2,(hTr n (by omega)).1,(hTr n (by omega)).2]
    exact hK' n (by omega)
end NLS.ZakharovShabat
