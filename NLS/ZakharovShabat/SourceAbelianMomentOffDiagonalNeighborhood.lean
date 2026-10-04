import NLS.ZakharovShabat.SourceAbelianMomentCubicCoefficients

/-! # Off-diagonal Lemma 20.3 on an almost-real neighborhood

A connected open neighborhood of the real source locus supports the
actual cubic-gap factorization, locally uniformly at every complex
source and uniformly in the deleted index. Every local source ball is
chosen before the refined sequence exponent.
-/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
variable {W V : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- Refined coefficient rows for off-diagonal second moments on one
connected complex neighborhood, with local bounds at every source. -/
theorem SourceAbelianMomentAtlas.exists_almostReal_offDiagonal_secondMoment_coefficients
    (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 V s)
    (hV : IsOpen V) (hrealV : realTypeSourceLocus p ⊆ V) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ IsConnected U ∧ realTypeSourceLocus p ⊆ U ∧
      U ⊆ A.domain ∩ V ∧ ∀ φ ∈ U, ∃ ρ : ℝ, 0 < ρ ∧ ball φ ρ ⊆ U ∧
        ∀ r : ℝ≥0∞, r ≠ ⊤ → 1 < r → ENNReal.ofReal (p.toReal/2) ≤ r →
          ∃ M : ℝ, 0 ≤ M ∧ ∀ ψ ∈ ball φ ρ, ∀ n : ℤ, ∃ a : Coeff r,
            (∀ k, a k = sourceSecondMomentCubicCoefficient A n ψ k) ∧
            a n = 0 ∧ ‖a‖ ≤ M ∧ ∀ k : ℤ, k ≠ n →
              A.moment n k 2 ψ = (sourcePeriodicGapDisplacement hp hp1 ψ k)^3/((n-k:ℤ):ℂ)*a k := by
  obtain ⟨D,_⟩ := A.exists_errorDomain hs.toSourcePsiNormalizedComplexExtension hV hrealV
  have hlocal (φ : realTypeSourceSubmodule p) :=
    D.exists_local_offDiagonal_secondMoment_coefficients hs φ (hrealV φ.property)
  choose T hT hφT hTD hrows using hlocal
  let S : Set (CoeffPair p) := ⋃ φ : realTypeSourceSubmodule p, T φ
  have hS : IsOpen S := isOpen_iUnion hT
  have hrealS : realTypeSourceLocus p ⊆ S :=
    fun ψ hψ => mem_iUnion.mpr ⟨⟨ψ,hψ⟩,hφT ⟨ψ,hψ⟩⟩
  let U := connectedComponentIn S (0 : CoeffPair p)
  have hzero : (0 : CoeffPair p) ∈ realTypeSourceLocus p := by simp [realTypeSourceLocus]
  have hUS : U ⊆ S := connectedComponentIn_subset S 0
  have hU : IsOpen U := hS.connectedComponentIn
  refine ⟨U,hU,isConnected_connectedComponentIn_iff.mpr (hrealS hzero),
    isConnected_realTypeSourceLocus.isPreconnected.subset_connectedComponentIn hzero hrealS,?_,?_⟩
  · intro ψ hψ
    obtain ⟨φ,hφ⟩ := mem_iUnion.mp (hUS hψ)
    exact ⟨D.source_subset (hTD φ hφ).1,(hTD φ hφ).2⟩
  · intro χ hχ
    obtain ⟨φ,hφ⟩ := mem_iUnion.mp (hUS hχ)
    obtain ⟨ρ,hρ,hball⟩ := Metric.mem_nhds_iff.mp ((hU.inter (hT φ)).mem_nhds ⟨hχ,hφ⟩)
    refine ⟨ρ,hρ,fun ψ hψ => (hball hψ).1,?_⟩
    intro r hr hr1 hpr
    obtain ⟨M,hM,hb⟩ := hrows φ r hr hr1 hpr
    exact ⟨M,hM,fun ψ hψ n => hb ψ (hball hψ).2 n⟩

end NLS.ZakharovShabat
