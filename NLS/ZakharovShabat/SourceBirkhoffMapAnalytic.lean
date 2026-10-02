import NLS.ZakharovShabat.SourceBirkhoffSequenceLocal

/-! # The complex analytic Birkhoff sequence map on a common domain

A union of constructed source neighborhoods contains the entire real
locus and supports the actual `ℓᵖ × ℓᵖ` map. Its scalar coordinates,
local norm bounds, action radii, and real closed-gap zeros are retained.
The real-valuedness of the remaining coordinates is a separate assertion.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The complex analytic and quantitative part of Theorem 15.2, with
exact scalar evaluations ruling out any sequence-constructor fallback. -/
structure SourceBirkhoffMapComplexData (hp : p ≠ ⊤) (hp1 : 1 < p)
    (W₀ B W : Set (CoeffPair p)) (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) : Prop where
  angular : SourceAngularEtaLocalCommonDomainData hp hp1 W₀ B s
  source_open : IsOpen W
  real_subset : realTypeSourceLocus p ⊆ W
  source_subset : W ⊆ B
  analytic : AnalyticOnNhd ℂ (sourceBirkhoffMap hp hp1 s) W
  locally_bounded : ∀ φ ∈ W, ∃ U : Set (CoeffPair p), IsOpen U ∧ φ ∈ U ∧ U ⊆ W ∧
    ∃ M : ℝ, 0 ≤ M ∧ ∀ ψ ∈ U, ‖sourceBirkhoffMap hp hp1 s ψ‖ ≤ M
  coordinates : ∀ ψ ∈ W, ∀ n : ℤ,
    (sourceBirkhoffMap hp hp1 s ψ).1 n = sourceBirkhoffX hp hp1 n s ψ ∧
    (sourceBirkhoffMap hp hp1 s ψ).2 n = sourceBirkhoffY hp hp1 n s ψ
  action_radius : ∀ ψ ∈ W, ∀ n : ℤ,
    ((sourceBirkhoffMap hp hp1 s ψ).1 n)^2 + ((sourceBirkhoffMap hp hp1 s ψ).2 n)^2 =
      2*sourceComplexAction hp hp1 n ψ
  real_closed_gap_zero : ∀ ψ ∈ W, IsRealType (CoeffPair.toMax p ψ) → ∀ n : ℤ,
    sourcePeriodicGapDisplacement hp hp1 ψ n = 0 →
    (sourceBirkhoffMap hp hp1 s ψ).1 n = 0 ∧ (sourceBirkhoffMap hp hp1 s ψ).2 n = 0

/-- Actual spectral and angular estimates construct all fields, for
every finite exponent above one. No sequence-membership or local-bound
premises are left to the caller. -/
theorem exists_sourceBirkhoffMap_complex_analytic
    (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W₀ B W : Set (CoeffPair p), ∃ s : (k : ℤ) → CoeffPair p → DeletedCoeff p k,
      SourceBirkhoffMapComplexData hp hp1 W₀ B W s := by
  classical
  obtain ⟨W₀,B,V,hV,hrealV,hVB,s,D,hz,hzbound,hprod,hzero⟩ := exists_sourceGapWeightedEta_lemma15_1 hp hp1
  have hlocal (φ : realTypeSourceLocus p) :
      ∃ U : Set (CoeffPair p), IsOpen U ∧ φ.val ∈ U ∧ U ⊆ V ∧
        AnalyticOnNhd ℂ (sourceBirkhoffMap hp hp1 s) U ∧
        ∃ M : ℝ, 0 ≤ M ∧ ∀ ψ ∈ U, ‖sourceBirkhoffMap hp hp1 s ψ‖ ≤ M ∧ ∀ n : ℤ,
          ((sourceBirkhoffMap hp hp1 s ψ).1 n = sourceBirkhoffX hp hp1 n s ψ ∧
            (sourceBirkhoffMap hp hp1 s ψ).2 n = sourceBirkhoffY hp hp1 n s ψ) ∧
          (sourceNormalizedActionRoot hp hp1 n ψ)^2 = 4*sourceNormalizedActionComplexExtension hp hp1 n ψ ∧
          sourceComplexAction hp hp1 n ψ =
            (sourcePeriodicGapDisplacement hp hp1 ψ n)^2 * sourceNormalizedActionComplexExtension hp hp1 n ψ := by
    obtain ⟨Z,hZ,hφZ,hZV,Cz,hCz,hbound⟩ := hzbound φ.val (hrealV φ.property)
    obtain ⟨U,hU,hφU,hUZ,hA,M,hM,hdata⟩ := D.exists_local_birkhoffSequence_analytic
      Z hZ (hZV.trans hVB) (fun n sign => (hz n sign).mono hZV) Cz hCz.le hbound φ.val hφZ φ.property
    exact ⟨U,hU,hφU,hUZ.trans hZV,hA,M,hM,hdata⟩
  choose U hU hφU hUV hA M hM hdata using hlocal
  let W := ⋃ φ : realTypeSourceLocus p, U φ
  have hW : IsOpen W := isOpen_iUnion hU
  have hWV : W ⊆ V := iUnion_subset hUV
  have hrealW : realTypeSourceLocus p ⊆ W := fun φ hφ => mem_iUnion.mpr ⟨⟨φ,hφ⟩,hφU ⟨φ,hφ⟩⟩
  have hcoord ψ (hψ : ψ ∈ W) n :
      (sourceBirkhoffMap hp hp1 s ψ).1 n = sourceBirkhoffX hp hp1 n s ψ ∧
      (sourceBirkhoffMap hp hp1 s ψ).2 n = sourceBirkhoffY hp hp1 n s ψ := by
    obtain ⟨φ,hφ⟩ := mem_iUnion.mp hψ
    exact ((hdata φ ψ hφ).2 n).1
  refine ⟨W₀,B,W,s,⟨D,hW,hrealW,hWV.trans hVB,?_,?_,hcoord,?_,?_⟩⟩
  · intro ψ hψ
    obtain ⟨φ,hφ⟩ := mem_iUnion.mp hψ
    exact hA φ ψ hφ
  · intro ψ hψ
    obtain ⟨φ,hφ⟩ := mem_iUnion.mp hψ
    exact ⟨U φ,hU φ,hφ,subset_iUnion U φ,M φ,hM φ,fun χ hχ => (hdata φ χ hχ).1⟩
  · intro ψ hψ n
    obtain ⟨φ,hφ⟩ := mem_iUnion.mp hψ
    have hf := ((hdata φ ψ hφ).2 n).2
    rw [(hcoord ψ hψ n).1,(hcoord ψ hψ n).2]
    exact sourceBirkhoffX_sq_add_Y_sq hp hp1 n s ψ
      (by simpa only [sourcePeriodicGapDisplacement_apply] using hprod ψ (hWV hψ) n) hf.1 hf.2
  · intro ψ hψ hreal n hgap
    have hz := hzero ψ (hWV hψ) hreal n
      (by simpa only [sourcePeriodicGapDisplacement_apply] using hgap)
    rw [(hcoord ψ hψ n).1,(hcoord ψ hψ n).2]
    exact sourceBirkhoffXY_eq_zero_of_gapWeighted_eq_zero hp hp1 n s ψ (hz 1) (hz (-1))

end NLS.ZakharovShabat
