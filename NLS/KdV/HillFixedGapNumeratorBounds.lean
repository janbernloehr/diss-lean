import NLS.KdV.HillUniformAllContourBounds
import NLS.ComplexAnalysis.CompactParameterBounds

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

/-- Each fixed original free gap disc has a common normalized-numerator
bound on one source ball, chosen before every differential index n. -/
theorem exists_hillSelectedPsi_uniform_fixed_gap_disc_bound (k : ℕ) (hk : 1≤k) :
    ∃ δ B : ℝ, 0<δ ∧ 0<B ∧ ∀ n : ℕ, ∀ hn : 1≤n,
      ∃ G : ℂ × Coeff 2 → ℂ,
        AnalyticOnNhd ℂ G (univ ×ˢ ball 0 δ) ∧
        (∀ p∈ball 0 δ, ∀ E∈closedBall (hillRealGapCenter 0 h0q h0r k : ℂ)
          (hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k), ‖G (E,p)‖≤B) ∧
        ∀ q : RealPeriodOneHillPotential, ‖q.val‖<δ → ∀ E : ℂ,
          G (E,SpectralWeight.one.toCoeff q.val)=hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 n hn E := by
  obtain ⟨δg,S,hδg,hS,hcharts⟩ := exists_hillSelectedPsi_common_uniform_all_contour_charts h0q h0r
  let c : ℂ := hillRealGapCenter 0 h0q h0r k
  let R := hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k
  have hR : 0<R := add_pos_of_nonneg_of_pos (hillRealGapContour_geometry 0 h0q h0r k hk).1
    (hillRealGapContour_geometry 0 h0q h0r k hk).2.1
  let D := hillAbelianComplexRootDomain 0 h0q h0r
  have hbase (E : ℂ) (hE : E∈sphere c R) : (E,(0 : Coeff 2))∈D := by
    simpa only [map_zero] using mem_hillAbelianComplexRootDomain_base 0 h0q h0r E
      (hillRealGapContour_sphere_subset 0 h0q h0r k hk hE)
  obtain ⟨V,hV,h0V,C,hC,hbound⟩ := exists_local_uniform_bound_on_compact_of_continuousOn
    (hillAbelianComplexRoot 0 h0q h0r) D (isOpen_hillAbelianComplexRootDomain 0 h0q h0r)
    (analyticOnNhd_hillAbelianComplexRoot 0 h0q h0r).continuousOn (sphere c R) (isCompact_sphere c R)
    (0 : Coeff 2) hbase
  obtain ⟨ε,hε,hεV⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds h0V)
  let δ := min δg ε
  let B := (S/R)*C+1
  have hδ : 0<δ := lt_min hδg hε
  have hB : 0<B := by dsimp only [B];positivity
  have hδg' : δ≤δg := min_le_left _ _
  have hδε : δ≤ε := min_le_right _ _
  refine ⟨δ,B,hδ,hB,?_⟩
  intro n hn
  obtain ⟨G,hGa,hdata,hreal⟩ := hcharts n hn
  refine ⟨G,hGa.mono (prod_mono Subset.rfl (ball_subset_ball hδg')),?_,?_⟩
  · intro p hp
    have hpG := ball_subset_ball hδg' hp
    have hpV : p∈V := hεV (ball_subset_ball hδε hp)
    have houter (E : ℂ) (hE : E∈sphere c R) : ‖G (E,p)‖≤B := by
      obtain ⟨hdom,hquot⟩ := (hdata p hpG k hk).1 E hE
      have hroot := hillAbelianComplexRoot_ne_zero 0 h0q h0r (E,p) hdom
      have he : G (E,p)=(G (E,p)/hillAbelianComplexRoot 0 h0q h0r (E,p))*
          hillAbelianComplexRoot 0 h0q h0r (E,p) := (div_mul_cancel₀ _ hroot).symm
      rw [he,norm_mul]
      exact (mul_le_mul hquot (hbound p hpV E hE).2 (norm_nonneg _) (by positivity)).trans (by
        dsimp only [B]
        linarith)
    have hslice : AnalyticOnNhd ℂ (fun E => G (E,p)) (closedBall c R) := by
      intro E _
      exact (hGa (E,p) ⟨mem_univ _,hpG⟩).comp (f := fun E : ℂ => (E,p)) (analyticAt_id.prod analyticAt_const)
    intro E hE
    have hdc : DiffContOnCl ℂ (fun E => G (E,p)) (ball c R) :=
      DiffContOnCl.mk_ball (hslice.differentiableOn.mono ball_subset_closedBall) hslice.continuousOn
    apply Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hdc
    · intro z hz
      rw [frontier_ball c hR.ne'] at hz
      exact houter z hz
    · rw [closure_ball c hR.ne']
      exact hE
  · intro q hq E
    exact hreal q (hq.trans_le hδg') E

end NLS.KdV
