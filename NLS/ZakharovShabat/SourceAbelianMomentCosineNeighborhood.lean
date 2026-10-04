import NLS.ZakharovShabat.SourceAbelianMomentUniformCosine
import NLS.ZakharovShabat.SourceGapCosineMeanBound

/-! # A common almost-real domain for the cosine moment estimates

All indices and positive even orders share one open connected source
domain containing the entire real locus. The same domain also supports
the normalized second-moment supremum bound on each actual complex gap.
-/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceAbelianMomentAtlas
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
variable {W V : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- All positive even moments have their exact gap-cosine formulas on
one connected neighborhood of the whole real source locus. -/
theorem exists_almostReal_all_even_moments_eq_cosineMean
    (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiNormalizedComplexExtension hp hp1 V s) (hV : IsOpen V)
    (hrealV : realTypeSourceLocus p ⊆ V) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ IsConnected U ∧ realTypeSourceLocus p ⊆ U ∧
      U ⊆ A.domain ∩ V ∧ ∀ ψ ∈ U, ∀ (n k : ℤ) (m : ℕ),
        A.moment n k (2*(m+1)) ψ = -(2*Complex.I) *
          sourceGapCosineMean hp hp1 k (fun t : ℂ × CoeffPair p =>
            sourceAbelianMomentEvenNumerator hp hp1 W n k (m+1) (s n t.2 : Coeff p) t.2 t.1) ψ := by
  have hlocal (φ : realTypeSourceSubmodule p) :=
    A.exists_ball_all_even_moments_eq_cosineMean hs hV φ (hrealV φ.property)
  choose r hr hsub heq using hlocal
  let S : Set (CoeffPair p) := ⋃ φ : realTypeSourceSubmodule p, ball φ.val (r φ)
  have hS : IsOpen S := isOpen_iUnion (fun _ => isOpen_ball)
  have hrealS : realTypeSourceLocus p ⊆ S := fun ψ hψ =>
    mem_iUnion.mpr ⟨⟨ψ,hψ⟩,mem_ball_self (hr ⟨ψ,hψ⟩)⟩
  have hzero : (0 : CoeffPair p) ∈ realTypeSourceLocus p := by simp [realTypeSourceLocus]
  let U := connectedComponentIn S (0 : CoeffPair p)
  have hUS : U ⊆ S := connectedComponentIn_subset S 0
  have hrealU : realTypeSourceLocus p ⊆ U :=
    isConnected_realTypeSourceLocus.isPreconnected.subset_connectedComponentIn hzero hrealS
  refine ⟨U,hS.connectedComponentIn,isConnected_connectedComponentIn_iff.mpr (hrealS hzero),hrealU,?_,?_⟩
  · intro ψ hψ
    obtain ⟨φ,hφ⟩ := mem_iUnion.mp (hUS hψ)
    exact hsub φ hφ
  · intro ψ hψ n k m
    obtain ⟨φ,hφ⟩ := mem_iUnion.mp (hUS hψ)
    exact heq φ n k m ψ hφ

/-- The same source neighborhood supports every second-moment formula
and the product bound for arbitrary square and psi-factor majorants.
No source neighborhood is chosen after the indices or the bounds. -/
theorem exists_almostReal_second_moment_gap_bounds
    (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiNormalizedComplexExtension hp hp1 V s) (hV : IsOpen V)
    (hrealV : realTypeSourceLocus p ⊆ V) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ IsConnected U ∧ realTypeSourceLocus p ⊆ U ∧
      U ⊆ A.domain ∩ V ∧ ∀ ψ ∈ U, ∀ n k : ℤ,
        (A.moment n k 2 ψ = -(2*Complex.I) *
          sourceGapCosineMean hp hp1 k (fun t : ℂ × CoeffPair p =>
            sourceAbelianMomentEvenNumerator hp hp1 W n k 1 (s n t.2 : Coeff p) t.2 t.1) ψ) ∧
        ∀ M B : ℝ, 0 ≤ M → 0 ≤ B →
          (∀ z ∈ sourcePeriodicSegment hp hp1 ψ k, ‖sourceFullAbelianSquare hp hp1 W k (z,ψ)‖ ≤ M) →
          (∀ z ∈ sourcePeriodicSegment hp hp1 ψ k,
            ‖sourceMomentRegularNumerator hp hp1 n k (s n ψ : Coeff p) ψ z‖ ≤ B) →
          ‖(2*Real.pi:ℂ)⁻¹ * A.moment n k 2 ψ‖ ≤ M*B := by
  obtain ⟨U,hU,hconn,hreal,hsub,heq⟩ := A.exists_almostReal_all_even_moments_eq_cosineMean hs hV hrealV
  refine ⟨U,hU,hconn,hreal,hsub,?_⟩
  intro ψ hψ n k
  refine ⟨heq ψ hψ n k 0,?_⟩
  intro M B hM _ hS hP
  rw [heq ψ hψ n k 0]
  apply norm_normalized_sourceGapCosineMean_le
  intro z hz
  simpa only [sourceAbelianMomentEvenNumerator,Nat.zero_add,pow_one,norm_mul] using
    mul_le_mul (hS z hz) (hP z hz) (norm_nonneg _) hM

end NLS.ZakharovShabat.SourceAbelianMomentAtlas
