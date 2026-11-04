import NLS.KdV.HillDeletedPeriodIdentification
import NLS.KdV.HillSmallRealRootBox
import NLS.KdV.HillGlobalPeriodRoots

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal Classical

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

/-- On one common neighborhood of the free real source, the actual
analytic period-root charts coincide with every original physical
off-diagonal period-root selection in the original real gap box. -/
theorem exists_hillComplexPeriodRootCharts_common_real_root_matching :
    ∃ δ : ℝ, 0<δ ∧ ∀ n : ℕ, 1≤n →
      ∃ s : Coeff 2 → PositiveDeletedCoeff 2 (n : ℤ),
        AnalyticOnNhd ℂ s (ball 0 δ) ∧ s 0=0 ∧
        (∀ p∈ball 0 δ, hillComplexSupportedPeriodMap h0q h0r n (s p,p)=0) ∧
        ∀ q : RealPeriodOneHillPotential, ‖q.val‖<δ →
          ∀ roots : ℕ → ℝ, ∀ hroots : roots∈hillGapRootBox q.val q.property.1 q.property.2,
          (∀ k : ℕ, 1≤k → k≠n → hillAbelianCandidatePeriod q.val q.property.1 q.property.2 roots n k=0) →
          Coeff.positiveDeletedProjectionTo 2 (n : ℤ)
            (hillGapRootHilbertCoordinates q.val q.property.1 q.property.2 roots hroots)=
              s (SpectralWeight.one.toCoeff q.val) := by
  obtain ⟨ρ,δc,hρ,hδc,hcharts⟩ := exists_hillComplexFreeSupportedPeriods_common_analytic_root h0q h0r
  obtain ⟨δr,hδr,hrootbox⟩ := exists_hillGapRootHilbertCoordinates_uniform_small_at_zero h0q h0r ρ hρ
  obtain ⟨ε,D,hε,hD,hc⟩ := exists_hillComplexPeriodControl h0q h0r
  let δ := min δc (min δr ε)
  have hδ : 0<δ := by dsimp only [δ];positivity
  have hδc' : δ≤δc := min_le_left _ _
  have hδr' : δ≤δr := (min_le_right _ _).trans (min_le_left _ _)
  have hδε : δ≤ε := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨δ,hδ,?_⟩
  intro n hn
  obtain ⟨s,ha,hzero,hinfo⟩ := hcharts n hn
  refine ⟨s,ha.mono (ball_subset_ball hδc'),hzero,?_,?_⟩
  · intro p hp
    exact (hinfo p (ball_subset_ball hδc' hp)).2.1
  · intro q hq roots hroots hperiods
    let a := hillGapRootHilbertCoordinates q.val q.property.1 q.property.2 roots hroots
    let b := Coeff.positiveDeletedProjectionTo 2 (n : ℤ) a
    let p := SpectralWeight.one.toCoeff q.val
    have haρ : ‖a‖<ρ := hrootbox q (hq.trans_le hδr') roots hroots
    have hbρ : b∈ball 0 ρ := by
      rw [mem_ball,dist_zero_right]
      exact (Coeff.norm_positiveDeletedProjectionTo_le 2 (n : ℤ) a).trans_lt haρ
    have hpδ : p∈ball 0 δc := by
      rw [mem_ball,dist_zero_right]
      exact (SpectralWeight.one.norm_toCoeff_le q.val).trans_lt (hq.trans_le hδc')
    have hpε : p∈ball 0 ε := by
      rw [mem_ball,dist_zero_right]
      exact (SpectralWeight.one.norm_toCoeff_le q.val).trans_lt (hq.trans_le hδε)
    have hpε' : ‖p‖≤ε :=
      (show ‖p‖<ε by simpa only [mem_ball,dist_zero_right] using hpε).le
    have hperiod (k : ℕ) (hk : 1≤k) (hkn : k≠n) :
        hillAbelianComplexPeriod 0 h0q h0r n k ((b : Coeff 2),p)=0 := by
      rw [hillAbelianComplexPeriod_near_free_eq_physical h0q h0r ε D hc q.val q.property.1 q.property.2 hpε' n k hk]
      change hillAbelianHilbertPeriod q.val q.property.1 q.property.2 n k
        (Coeff.positiveDeletedProjection 2 (n : ℤ) a)=0
      rw [hillAbelianHilbertPeriod_positiveDeletedProjection]
      exact (hillAbelianHilbertPeriod_eq_genuine_period q.val q.property.1 q.property.2 roots hroots n k).trans
        (hperiods k hk hkn)
    have hzeroB : hillComplexFreeSupportedPeriodMap h0q h0r n (b,p)=0 :=
      (hillComplexFreeSupportedPeriodMap_zero_iff_periods h0q h0r n hn ε D hD.le hc b p hpε).mpr hperiod
    exact (hinfo p hpδ).2.2.2 b hbρ hzeroB

/-- In particular, the same common charts recover the original globally
selected real normalized period roots, uniformly in the coordinate index. -/
theorem exists_hillComplexPeriodRootCharts_common_selected_real_matching :
    ∃ δ : ℝ, 0<δ ∧ ∀ n : ℕ, ∀ hn : 1≤n,
      ∃ s : Coeff 2 → PositiveDeletedCoeff 2 (n : ℤ),
        AnalyticOnNhd ℂ s (ball 0 δ) ∧ s 0=0 ∧
        (∀ p∈ball 0 δ, hillComplexSupportedPeriodMap h0q h0r n (s p,p)=0) ∧
        ∀ q : RealPeriodOneHillPotential, ‖q.val‖<δ →
          Coeff.positiveDeletedProjectionTo 2 (n : ℤ)
            (hillGapRootHilbertCoordinates q.val q.property.1 q.property.2
              (hillAbelianSelectedGlobalRoots q.val q.property.1 q.property.2 n hn).val
              (hillAbelianSelectedGlobalRoots q.val q.property.1 q.property.2 n hn).property)=
              s (SpectralWeight.one.toCoeff q.val) := by
  obtain ⟨δ,hδ,hcharts⟩ := exists_hillComplexPeriodRootCharts_common_real_root_matching h0q h0r
  refine ⟨δ,hδ,?_⟩
  intro n hn
  obtain ⟨s,ha,hzero,hperiod,hmatch⟩ := hcharts n hn
  refine ⟨s,ha,hzero,hperiod,?_⟩
  intro q hq
  apply hmatch q hq (hillAbelianSelectedGlobalRoots q.val q.property.1 q.property.2 n hn).val
    (hillAbelianSelectedGlobalRoots q.val q.property.1 q.property.2 n hn).property
  intro k hk hkn
  have hdata := hillAbelianSelectedGlobalRoots_periods q.val q.property.1 q.property.2 n hn
  have hh := hdata.2 k hk
  rw [if_neg hkn] at hh
  exact (div_eq_zero_iff.mp hh).resolve_right hdata.1

end NLS.KdV
