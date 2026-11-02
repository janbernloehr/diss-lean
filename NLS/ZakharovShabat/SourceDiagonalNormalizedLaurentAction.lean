import NLS.ZakharovShabat.SourceDiagonalLaurentActionRatio

/-! # A chart-independent normalized inverse-frequency action

At an open gap the definition is the actual Laurent action divided by the
squared gap. At a closed gap it uses the ordinary normalized action and
the spectral midpoint. The local rationalized contour proves that these
two branches are one Banach analytic function near every real diagonal.
-/
noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def sourceNormalizedDiagonalLaurentAction (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n : ℤ) (ψ : CoeffPair p) : ℂ :=
  if canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem _) n = 0 then
    (sourceStandardRootMidpoint hp hp1 ψ n)⁻¹*sourceNormalizedActionComplexExtension hp hp1 n ψ
  else sourceDiagonalLaurentAction hp hp1 n 0 ψ /
    (canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem _) n)^2

/-- The piecewise normalized function equals the local rationalized contour
on a full complex neighborhood, and gives the actual Laurent action there. -/
theorem exists_local_sourceNormalizedDiagonalLaurentAction_eq_contour
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realDiagonalSourceLocus p) (n : ℤ) (hn : n ≠ 0) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ φ.val ∈ U ∧
      U ⊆ ball φ.val ((sourceDiagonalLaurentAtlas hp hp1).localChart φ).radius ∧
      (∀ k : ℤ, AnalyticOnNhd ℂ (((sourceDiagonalLaurentAtlas hp hp1).localChart φ).normalizedAction n k) U) ∧
      EqOn (((sourceDiagonalLaurentAtlas hp hp1).localChart φ).normalizedAction n 1)
        (sourceNormalizedActionComplexExtension hp hp1 n) U ∧
      EqOn (sourceNormalizedDiagonalLaurentAction hp hp1 n)
        (((sourceDiagonalLaurentAtlas hp hp1).localChart φ).normalizedAction n 0) U ∧
      ∀ ψ ∈ U, sourceDiagonalLaurentAction hp hp1 n 0 ψ =
        (canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem _) n)^2 *
          sourceNormalizedDiagonalLaurentAction hp hp1 n ψ := by
  let C := (sourceDiagonalLaurentAtlas hp hp1).localChart φ
  obtain ⟨U,hU,hφU,hUC,hAn,hone⟩ := C.exists_normalizedAction_one_eq n hn
  have heq : EqOn (sourceNormalizedDiagonalLaurentAction hp hp1 n) (C.normalizedAction n 0) U := by
    intro ψ hψ
    have hlocal : sourceDiagonalLaurentAction hp hp1 n 0 ψ = C.action n 0 ψ :=
      (sourceDiagonalLaurentAtlas hp hp1).action_eq_local n 0 hn φ (hUC hψ)
    by_cases hg : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem _) n = 0
    · rw [sourceNormalizedDiagonalLaurentAction,if_pos hg,← hone hψ]
      exact (C.normalizedAction_zero_eq_midpoint_inv_mul_one_of_zeroGap n hn ψ (hUC hψ) hg).symm
    · rw [sourceNormalizedDiagonalLaurentAction,if_neg hg,hlocal,
        C.action_eq_squaredGap_mul_normalizedAction n 0 hn ψ (hUC hψ)]
      exact mul_div_cancel_left₀ _ (pow_ne_zero 2 hg)
  refine ⟨U,hU,hφU,hUC,hAn,hone,heq,?_⟩
  intro ψ hψ
  rw [heq hψ]
  exact ((sourceDiagonalLaurentAtlas hp hp1).action_eq_local n 0 hn φ (hUC hψ)).trans
    (C.action_eq_squaredGap_mul_normalizedAction n 0 hn ψ (hUC hψ))

/-- Actual Banach analyticity and exact factorization include every closed gap. -/
theorem exists_local_sourceNormalizedDiagonalLaurentAction_analytic_factor
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realDiagonalSourceLocus p) (n : ℤ) (hn : n ≠ 0) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ φ.val ∈ U ∧
      AnalyticOnNhd ℂ (sourceNormalizedDiagonalLaurentAction hp hp1 n) U ∧
      ∀ ψ ∈ U, sourceDiagonalLaurentAction hp hp1 n 0 ψ =
        (canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem _) n)^2 *
          sourceNormalizedDiagonalLaurentAction hp hp1 n ψ := by
  obtain ⟨U,hU,hφU,_,hAn,_,heq,hfactor⟩ :=
    exists_local_sourceNormalizedDiagonalLaurentAction_eq_contour hp hp1 φ n hn
  refine ⟨U,hU,hφU,?_,hfactor⟩
  intro ψ hψ
  apply (hAn 0 ψ hψ).congr
  filter_upwards [hU.mem_nhds hψ] with χ hχ
  exact (heq hχ).symm

/-- The physical mKdV to ordinary NLS action ratio, regular at all zero actions. -/
def sourceDiagonalActionRatio (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (ψ : CoeffPair p) : ℂ :=
  sourceNormalizedDiagonalLaurentAction hp hp1 n ψ /
    (2*sourceNormalizedActionComplexExtension hp hp1 n ψ)

/-- The regularized ratio is real and strictly positive on the full
positive-index real diagonal, including at closed gaps and zero mean. -/
theorem sourceDiagonalActionRatio_real_positive
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realDiagonalSourceLocus p) (n : ℤ) (hn : 0 < n) :
    (sourceDiagonalActionRatio hp hp1 n φ.val).im = 0 ∧
      0 < (sourceDiagonalActionRatio hp hp1 n φ.val).re := by
  obtain ⟨U,_,hφU,hUC,_,hone,heq,_⟩ :=
    exists_local_sourceNormalizedDiagonalLaurentAction_eq_contour hp hp1 φ n (ne_of_gt hn)
  let C := (sourceDiagonalLaurentAtlas hp hp1).localChart φ
  have he : sourceDiagonalActionRatio hp hp1 n φ.val = C.actionRatio n φ.val := by
    unfold sourceDiagonalActionRatio SourceDiagonalLaurentLocalChart.actionRatio
    rw [heq hφU,hone hφU]
  rw [he]
  exact C.actionRatio_real_positive n hn φ (hUC hφU) (hone hφU)

/-- At a closed gap the exact physical ratio is one over twice the midpoint. -/
theorem sourceDiagonalActionRatio_zeroGap
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realDiagonalSourceLocus p) (n : ℤ)
    (hg : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem _) n = 0) :
    sourceDiagonalActionRatio hp hp1 n φ.val = (2*sourceStandardRootMidpoint hp hp1 φ.val n)⁻¹ := by
  have hne := sourceNormalizedActionComplexExtension_ne_zero_of_realType hp hp1 n φ.val φ.property.1
  unfold sourceDiagonalActionRatio sourceNormalizedDiagonalLaurentAction
  rw [if_pos hg]
  field_simp

end NLS.ZakharovShabat
