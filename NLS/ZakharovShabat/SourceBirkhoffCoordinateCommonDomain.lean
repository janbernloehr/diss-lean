import NLS.ZakharovShabat.SourceBirkhoffCoordinates

/-! # A common analytic domain for the actual rectangular coordinates

Intersect the gap-weighted eta domain with neighborhoods carrying all
normalized-action roots. Every rectangular coordinate is analytic on
the resulting neighborhood of the whole real source locus. Its squared
radius is twice the actual indexed action, also at complex closed gaps.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem exists_sourceBirkhoffCoordinates_analytic_common_domain
    (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ realTypeSourceLocus p ⊆ W ∧
      ∃ s : (k : ℤ) → CoeffPair p → DeletedCoeff p k,
        (∀ n : ℤ, AnalyticOnNhd ℂ (sourceBirkhoffX hp hp1 n s) W ∧
          AnalyticOnNhd ℂ (sourceBirkhoffY hp hp1 n s) W) ∧
        (∀ ψ ∈ W, ∀ n : ℤ, (sourceBirkhoffX hp hp1 n s ψ)^2 + (sourceBirkhoffY hp hp1 n s ψ)^2 =
          2*sourceComplexAction hp hp1 n ψ) ∧
        (∀ ψ ∈ W, IsRealType (CoeffPair.toMax p ψ) → ∀ n : ℤ,
          sourcePeriodicGapDisplacement hp hp1 ψ n = 0 →
          sourceBirkhoffX hp hp1 n s ψ = 0 ∧ sourceBirkhoffY hp hp1 n s ψ = 0) := by
  classical
  obtain ⟨W₀,B,V,hV,hrealV,hVB,s,D,hz,_,hprod,hzero⟩ := exists_sourceGapWeightedEta_lemma15_1 hp hp1
  have hlocal (φ : realTypeSourceLocus p) :=
    exists_local_sourceNormalizedActionRoot_allIndices_analytic hp hp1 φ.val φ.property
  choose U hU hφU hξ hfactor using hlocal
  let W := ⋃ φ : realTypeSourceLocus p, U φ ∩ V
  have hW : IsOpen W := isOpen_iUnion (fun φ => (hU φ).inter hV)
  have hWV : W ⊆ V := iUnion_subset (fun _ => inter_subset_right)
  have hrealW : realTypeSourceLocus p ⊆ W := by
    intro φ hφ
    exact mem_iUnion.mpr ⟨⟨φ,hφ⟩,hφU ⟨φ,hφ⟩,hrealV hφ⟩
  have hxy (n : ℤ) (ψ : CoeffPair p) (hψ : ψ ∈ W) :
      AnalyticAt ℂ (sourceBirkhoffX hp hp1 n s) ψ ∧ AnalyticAt ℂ (sourceBirkhoffY hp hp1 n s) ψ := by
    obtain ⟨φ,hφ⟩ := mem_iUnion.mp hψ
    exact analyticAt_sourceBirkhoffXY hp hp1 n s ψ (hξ φ n ψ hφ.1)
      (fun sign => hz n sign ψ hφ.2) (D.beta_series.analytic_correction n ψ (hVB hφ.2))
  refine ⟨W,hW,hrealW,s,(fun n => ⟨fun ψ hψ => (hxy n ψ hψ).1,fun ψ hψ => (hxy n ψ hψ).2⟩),?_,?_⟩
  · intro ψ hψ n
    obtain ⟨φ,hφ⟩ := mem_iUnion.mp hψ
    exact sourceBirkhoffX_sq_add_Y_sq hp hp1 n s ψ
      (by simpa only [sourcePeriodicGapDisplacement_apply] using hprod ψ hφ.2 n)
      (hfactor φ ψ hφ.1 n).1 (hfactor φ ψ hφ.1 n).2
  · intro ψ hψ hreal n hgap
    have hz := hzero ψ (hWV hψ) hreal n
      (by simpa only [sourcePeriodicGapDisplacement_apply] using hgap)
    exact sourceBirkhoffXY_eq_zero_of_gapWeighted_eq_zero hp hp1 n s ψ (hz 1) (hz (-1))

end NLS.ZakharovShabat
