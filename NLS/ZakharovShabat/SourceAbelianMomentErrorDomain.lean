import NLS.ZakharovShabat.SourceAbelianMomentGapRegularity
import NLS.ZakharovShabat.SourceGapCosineError

/-! # A common domain for quantitative second-moment errors

Exact cosine formulas, continuity of every numerator, and separation of
all selected gaps hold on one connected neighborhood of the real locus.
This packages the inputs for subtracting polynomial leading terms.
-/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
variable {W : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

structure SourceAbelianMomentErrorDomain (A : SourceAbelianMomentAtlas hp hp1 W s) where
  domain : Set (CoeffPair p)
  isOpen_domain : IsOpen domain
  isConnected_domain : IsConnected domain
  real_subset : realTypeSourceLocus p ⊆ domain
  source_subset : domain ⊆ A.domain
  segment_omitted : ∀ ψ ∈ domain, ∀ k : ℤ,
    sourcePeriodicSegment hp hp1 ψ k ⊆ sourceStandardRootOmittedDomain hp hp1 ψ k
  numerator_continuous : ∀ ψ ∈ domain, ∀ n k : ℤ,
    ContinuousOn (sourceAbelianMomentEvenNumerator hp hp1 W n k 1 (s n ψ : Coeff p) ψ)
      (sourcePeriodicSegment hp hp1 ψ k)
  cosine_formula : ∀ ψ ∈ domain, ∀ n k : ℤ,
    A.moment n k 2 ψ = -(2*Complex.I) *
      sourceGapCosineMean hp hp1 k (fun t : ℂ × CoeffPair p =>
        sourceAbelianMomentEvenNumerator hp hp1 W n k 1 (s n t.2 : Coeff p) t.2 t.1) ψ

/-- All error estimates may use one actual source domain, chosen before
indices, model numerators, and error bounds. -/
theorem SourceAbelianMomentAtlas.exists_errorDomain
    (A : SourceAbelianMomentAtlas hp hp1 W s) {V : Set (CoeffPair p)}
    (hs : SourcePsiNormalizedComplexExtension hp hp1 V s) (hV : IsOpen V)
    (hrealV : realTypeSourceLocus p ⊆ V) :
    ∃ D : SourceAbelianMomentErrorDomain A, D.domain ⊆ V := by
  obtain ⟨U,hU,_,hrealU,hUV,hcos⟩ := A.exists_almostReal_all_even_moments_eq_cosineMean hs hV hrealV
  obtain ⟨R,hR,hrealR,_,hreg⟩ := A.exists_almostReal_evenNumerator_analytic
  let S := U ∩ R
  let T := connectedComponentIn S (0 : CoeffPair p)
  have hzero : (0 : CoeffPair p) ∈ realTypeSourceLocus p := by simp [realTypeSourceLocus]
  have hrealS : realTypeSourceLocus p ⊆ S := fun ψ hψ => ⟨hrealU hψ,hrealR hψ⟩
  have hTS : T ⊆ S := connectedComponentIn_subset S 0
  refine ⟨{
    domain := T
    isOpen_domain := (hU.inter hR).connectedComponentIn
    isConnected_domain := isConnected_connectedComponentIn_iff.mpr (hrealS hzero)
    real_subset := isConnected_realTypeSourceLocus.isPreconnected.subset_connectedComponentIn hzero hrealS
    source_subset := fun ψ hψ => (hUV (hTS hψ).1).1
    segment_omitted := fun ψ hψ => (hreg ψ (hTS hψ).2).1
    numerator_continuous := fun ψ hψ n k =>
      ((hreg ψ (hTS hψ).2).2 n k 1 (s n ψ : Coeff p)).continuousOn.mono ((hreg ψ (hTS hψ).2).1 k)
    cosine_formula := fun ψ hψ n k => hcos ψ (hTS hψ).1 n k 0
  },fun ψ hψ => (hUV (hTS hψ).1).2⟩

namespace SourceAbelianMomentErrorDomain
variable {A : SourceAbelianMomentAtlas hp hp1 W s}

/-- Subtract any continuous regular model before estimating the integral.
The normalization has operator norm one on the gap supremum norm. -/
theorem norm_model_error_le
    (D : SourceAbelianMomentErrorDomain A) (ψ : CoeffPair p) (hψ : ψ ∈ D.domain)
    (n k : ℤ) (c : ℂ) (g : ℂ × CoeffPair p → ℂ)
    (hg : ContinuousOn (fun z => g (z,ψ)) (sourcePeriodicSegment hp hp1 ψ k))
    (B : ℝ) (hB : ∀ z ∈ sourcePeriodicSegment hp hp1 ψ k,
      ‖c*sourceAbelianMomentEvenNumerator hp hp1 W n k 1 (s n ψ : Coeff p) ψ z-g (z,ψ)‖ ≤ B) :
    ‖(2*Real.pi:ℂ)⁻¹ * (c*A.moment n k 2 ψ -
      (-(2*Complex.I)*sourceGapCosineMean hp hp1 k g ψ))‖ ≤ B := by
  let f : ℂ × CoeffPair p → ℂ := fun t =>
    sourceAbelianMomentEvenNumerator hp hp1 W n k 1 (s n t.2 : Coeff p) t.2 t.1
  have hc : ContinuousOn (fun z => c*f (z,ψ)) (sourcePeriodicSegment hp hp1 ψ k) :=
    continuousOn_const.mul (D.numerator_continuous ψ hψ n k)
  have hb := norm_sourceGapCosineMean_sub_le hp hp1 k ψ (fun t => c*f t) g hc hg B hB
  have he : sourceGapCosineMean hp hp1 k (fun t => c*f t) ψ = c*sourceGapCosineMean hp hp1 k f ψ := by
    unfold sourceGapCosineMean parametricCosineMean
    exact intervalIntegral.integral_const_mul _ _
  rw [he] at hb
  rw [D.cosine_formula ψ hψ n k]
  convert hb using 1
  congr 1
  dsimp only [f]
  ring

/-- The midpoint of any other gap cannot lie on the selected gap. -/
theorem midpoint_sub_ne_zero
    (D : SourceAbelianMomentErrorDomain A) (ψ : CoeffPair p) (hψ : ψ ∈ D.domain)
    (n k : ℤ) (hkn : k ≠ n) (z : ℂ) (hz : z ∈ sourcePeriodicSegment hp hp1 ψ k) :
    sourceStandardRootMidpoint hp hp1 ψ n-z ≠ 0 := by
  intro he
  have hm := sourcePeriodicMidpoint_mem_segment hp hp1 ψ n
  change sourceStandardRootMidpoint hp hp1 ψ n ∈ sourcePeriodicSegment hp hp1 ψ n at hm
  rw [sub_eq_zero.mp he] at hm
  exact D.segment_omitted ψ hψ k hz n hkn.symm hm

end SourceAbelianMomentErrorDomain
end NLS.ZakharovShabat
