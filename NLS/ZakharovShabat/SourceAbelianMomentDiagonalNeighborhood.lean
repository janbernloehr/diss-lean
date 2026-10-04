import NLS.ZakharovShabat.SourceAbelianMomentDiagonalCoefficients

/-! # Diagonal Lemma 20.3 on an almost-real neighborhood

A connected open neighborhood of the real source locus supports the
actual quadratic-gap factorization, locally uniformly at every complex
source. Every local source ball is
chosen before the refined sequence exponent.
-/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
variable {W V : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- One refined coefficient sequence for diagonal second moments on one
connected complex neighborhood, with local bounds at every source. -/
theorem SourceAbelianMomentAtlas.exists_almostReal_diagonal_secondMoment_coefficients
    (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 V s)
    (hV : IsOpen V) (hrealV : realTypeSourceLocus p ⊆ V) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ IsConnected U ∧ realTypeSourceLocus p ⊆ U ∧
      U ⊆ A.domain ∩ V ∧ ∀ φ ∈ U, ∃ ρ : ℝ, 0 < ρ ∧ ball φ ρ ⊆ U ∧
        ∀ r : ℝ≥0∞, r ≠ ⊤ → 1 < r → ENNReal.ofReal (p.toReal/2) ≤ r →
          ∃ M : ℝ, 0 ≤ M ∧ ∀ ψ ∈ ball φ ρ, ∃ a : Coeff r,
            (∀ k, a k = sourceSecondMomentDiagonalCoefficient A ψ k) ∧
            ‖a‖ ≤ M ∧ ∀ k : ℤ,
              A.moment k k 2 ψ = (sourcePeriodicGapDisplacement hp hp1 ψ k)^2/4*((Real.pi:ℂ)+a k) := by
  obtain ⟨D,_⟩ := A.exists_errorDomain hs.toSourcePsiNormalizedComplexExtension hV hrealV
  have hlocal (φ : realTypeSourceSubmodule p) :=
    D.exists_local_diagonal_secondMoment_coefficients hs φ (hrealV φ.property)
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
    exact ⟨M,hM,fun ψ hψ => hb ψ (hball hψ).2⟩

end NLS.ZakharovShabat
