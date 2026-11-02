import NLS.ZakharovShabat.SourceAbelianMomentOnePlus
import NLS.ZakharovShabat.SourceAngularOriginalDomain

/-! # A constructed domain for the sharp off-diagonal moment estimate

The original psi roots of Lemmas 12.11–12.12 supply the atlas and the
critical-root comparison. The domain precedes every target exponent.
This is the off-diagonal part of article Lemma 5.3 for finite p > 2.
-/
noncomputable section
set_option autoImplicit false
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
variable {W W₀ V : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- The actual cubic coefficient is locally bounded in every finite q > 1
on one open connected neighborhood of the entire real source space. -/
theorem SourceAbelianMomentAtlas.exists_offDiagonal_onePlus
    (A : SourceAbelianMomentAtlas hp hp1 W s)
    (H : SourceLemma12_11Data hp hp1 W₀ V s)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 V s) (hp2 : 2 < p)
    (hV : IsOpen V) (hrealV : realTypeSourceLocus p ⊆ V) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ IsConnected U ∧ realTypeSourceLocus p ⊆ U ∧
      U ⊆ A.domain ∩ V ∧ ∀ ψ ∈ U, ∃ T : Set (CoeffPair p),
        IsOpen T ∧ ψ ∈ T ∧ T ⊆ U ∧
        ∀ q : ℝ≥0∞, q ≠ ⊤ → 1 < q → ∃ M : ℝ, 0 ≤ M ∧
          ∀ χ ∈ T, ∀ n : ℤ, ∃ a : Coeff q,
            (∀ k, a k = sourceSecondMomentCubicCoefficient A n χ k) ∧ a n = 0 ∧ ‖a‖ ≤ M ∧
            ∀ k : ℤ, k ≠ n → A.moment n k 2 χ =
              (sourcePeriodicGapDisplacement hp hp1 χ k)^3/((n-k:ℤ):ℂ)*a k := by
  classical
  obtain ⟨D,_⟩ := A.exists_errorDomain hs.toSourcePsiNormalizedComplexExtension hV hrealV
  have hlocal (φ : realTypeSourceSubmodule p) :=
    D.exists_local_offDiagonal_onePlus_coefficients H hs hp2 φ (hrealV φ.property)
  choose T hT hφT hTD hrows using hlocal
  let S := ⋃ φ : realTypeSourceSubmodule p, T φ
  have hrealS : realTypeSourceLocus p ⊆ S := by
    intro ψ hψ
    exact mem_iUnion.mpr ⟨⟨ψ,hψ⟩,hφT ⟨ψ,hψ⟩⟩
  have hzero : (0 : CoeffPair p) ∈ realTypeSourceLocus p := by simp [realTypeSourceLocus]
  let U := connectedComponentIn S (0 : CoeffPair p)
  have hUS : U ⊆ S := connectedComponentIn_subset S 0
  have hU : IsOpen U := (isOpen_iUnion hT).connectedComponentIn
  refine ⟨U,hU,isConnected_connectedComponentIn_iff.mpr (hrealS hzero),
    isConnected_realTypeSourceLocus.isPreconnected.subset_connectedComponentIn hzero hrealS,?_,?_⟩
  · intro ψ hψ
    obtain ⟨φ,hφ⟩ := mem_iUnion.mp (hUS hψ)
    exact ⟨D.source_subset (hTD φ hφ).1,(hTD φ hφ).2⟩
  · intro ψ hψ
    obtain ⟨φ,hφ⟩ := mem_iUnion.mp (hUS hψ)
    refine ⟨T φ ∩ U,(hT φ).inter hU,⟨hφ,hψ⟩,inter_subset_right,?_⟩
    intro q hq hq1
    obtain ⟨M,hM,hbound⟩ := hrows φ q hq hq1
    exact ⟨M,hM,fun χ hχ n => hbound χ hχ.1 n⟩

/-- Construct both the original root family and its sharp actual moment atlas.
There is no independently assumed compatibility or spectral premise. -/
theorem exists_sourceAbelianMoment_onePlusAtlas (hp : p ≠ ⊤) (hp2 : 2 < p) :
    ∃ W V : Set (CoeffPair p), IsOpen V ∧ realTypeSourceLocus p ⊆ V ∧
      ∃ s : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
        SourcePsiSquaredGapComplexExtension hp (lt_trans (by norm_num : (1:ℝ≥0∞)<2) hp2) V s ∧
        ∃ A : SourceAbelianMomentAtlas hp (lt_trans (by norm_num : (1:ℝ≥0∞)<2) hp2) W s,
        ∃ U : Set (CoeffPair p), IsOpen U ∧ IsConnected U ∧ realTypeSourceLocus p ⊆ U ∧
          U ⊆ A.domain ∩ V ∧ ∀ ψ ∈ U, ∃ T : Set (CoeffPair p),
            IsOpen T ∧ ψ ∈ T ∧ T ⊆ U ∧
            ∀ q : ℝ≥0∞, q ≠ ⊤ → 1 < q → ∃ M : ℝ, 0 ≤ M ∧
              ∀ χ ∈ T, ∀ n : ℤ, ∃ a : Coeff q,
                (∀ k, a k = sourceSecondMomentCubicCoefficient A n χ k) ∧ a n = 0 ∧ ‖a‖ ≤ M ∧
                ∀ k : ℤ, k ≠ n → A.moment n k 2 χ =
                  (sourcePeriodicGapDisplacement hp (lt_trans (by norm_num : (1:ℝ≥0∞)<2) hp2) χ k)^3/
                    ((n-k:ℤ):ℂ)*a k := by
  classical
  let hp1 : 1 < p := lt_trans (by norm_num : (1:ℝ≥0∞)<2) hp2
  obtain ⟨W₀,_,_,_,V,hV,_,hrealV,s,H⟩ := sourceLemma12_12 hp hp1
  have hs := H.angular_extension
  obtain ⟨W,_,_,hlocal⟩ := hs.toSourcePsiNormalizedComplexExtension.exists_moment_localCharts hV hrealV
  choose L hL using hlocal
  let A : SourceAbelianMomentAtlas hp hp1 W s := ⟨L⟩
  obtain ⟨U,hU,hUc,hreal,hUV,hrows⟩ := A.exists_offDiagonal_onePlus H.previous hs hp2 hV hrealV
  exact ⟨W,V,hV,hrealV,s,hs,A,U,hU,hUc,hreal,hUV,hrows⟩

end NLS.ZakharovShabat
