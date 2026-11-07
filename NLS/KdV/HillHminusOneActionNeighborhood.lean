import NLS.KdV.HillHminusOneActionChartGluing

/-! # Actual analytic neighborhoods of high Hill action charts

The neighborhoods are constructed from the proved actual trace-square
family. One neighborhood works for all later indices, with the original
complex norm topology and exact normalized action-ratio estimate.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex NLS.ComplexAnalysis
namespace NLS.KdV

def HillHminusActionNeighborhood (n : ℕ+) (r : ℝ) (K : ℂ × PeriodOneHminusOne → ℂ)
    (V : Set PeriodOneHminusOne) : Prop :=
  0 < r ∧ IsOpen V ∧
  AnalyticOnNhd ℂ K (ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r) ×ˢ V) ∧
  AnalyticOnNhd ℂ (hillHminusJointNormalizedGapRoot n r K)
    (ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r) ×ˢ V) ∧
  ∀ q ∈ V, HillHminusActionChartValid n r K q

theorem HillHminusActionNeighborhood.valid
    {n : ℕ+} {r : ℝ} {K : ℂ × PeriodOneHminusOne → ℂ} {V : Set PeriodOneHminusOne}
    (h : HillHminusActionNeighborhood n r K V) {q : PeriodOneHminusOne} (hq : q ∈ V) :
    HillHminusActionChartValid n r K q := h.2.2.2.2 q hq

theorem HillHminusActionNeighborhood.analytic_ratio
    {n : ℕ+} {r : ℝ} {K : ℂ × PeriodOneHminusOne → ℂ} {V : Set PeriodOneHminusOne}
    (h : HillHminusActionNeighborhood n r K V) :
    AnalyticOnNhd ℂ (hillHminusNormalizedActionRatio n r K) V :=
  analyticOnNhd_hillHminusNormalizedActionRatio n r h.1 V h.2.1 K h.2.2.2.1
    (fun _ ha => (h.valid ha).2.2.2.2.2.2)

theorem HillHminusActionNeighborhood.analytic_squared_half_gap
    {n : ℕ+} {r : ℝ} {K : ℂ × PeriodOneHminusOne → ℂ} {V : Set PeriodOneHminusOne}
    (h : HillHminusActionNeighborhood n r K V) :
    AnalyticOnNhd ℂ (hillHminusSquaredHalfGap n r) V :=
  (analyticOnNhd_hillHminus_symmetric_gap_data n r h.1 V h.2.1
    (fun _ ha => (h.valid ha).2.2.2.2.2.2)).2

theorem exists_hillHminus_uniform_action_neighborhoods (q : PeriodOneHminusOne) :
    ∃ r : ℝ, 0 < r ∧ r ≤ Real.pi/4 ∧
      ∀ epsilon : ℝ, 0 < epsilon →
        ∃ N : ℕ, ∃ V : Set PeriodOneHminusOne, 0 < N ∧ IsOpen V ∧ q ∈ V ∧
      ∀ n : ℕ+, N ≤ (n : ℕ) → ∃ K : ℂ × PeriodOneHminusOne → ℂ,
        HillHminusActionNeighborhood n r K V ∧
        ∀ a ∈ V, ‖hillHminusNormalizedActionRatio n r K a-1‖ ≤ epsilon ∧
          hillHminusNormalizedActionRatio n r K a ≠ 0 := by
  obtain ⟨r,hr,hrpi,hfamily⟩ := exists_hillHminus_normalized_gap_squares q
  refine ⟨r,hr,hrpi,?_⟩
  intro epsilon hepsilon
  let eta : ℝ := min (1/2) epsilon
  have heta : 0 < eta := lt_min (by norm_num) hepsilon
  have heta1 : eta < 1 := (min_le_left _ _).trans_lt (by norm_num)
  have hetaε : eta ≤ epsilon := min_le_right _ _
  obtain ⟨N,V,hN,hV,hq,hfamily⟩ := hfamily eta heta
  refine ⟨N,V,hN,hV,hq,?_⟩
  intro n hn
  obtain ⟨K,hK,_,hrel,_,_,hpairs⟩ := hfamily n hn
  have hdata : ∀ a ∈ V, ∃ l u : ℂ, HillHminusHighGapPair a n r l u ∧
      (∀ z : ℂ, K (z,a) = (z-l)*(z-u)*twoRootDeflation (fun w => K (w,a)) l u z) ∧
      ∀ z ∈ hillHminusGapSquareDisc n r,
        ‖hillHminusNormalizedGapSquare n K a l u z-1‖ ≤ eta := by
    intro a ha
    obtain ⟨l,u,hpair,_,hfactor,hnorm⟩ := hpairs a ha
    exact ⟨l,u,hpair,hfactor,hnorm⟩
  obtain ⟨hJ,hproperties⟩ := hillHminusJointNormalizedGapRoot_properties n r eta hr heta1 V hV K hK hdata
  have hvalid : ∀ a ∈ V, HillHminusActionChartValid n r K a := by
    intro a ha
    have hKa : AnalyticOnNhd ℂ (fun z => K (z,a))
        (ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r)) := by
      intro z hz
      exact (hK (z,a) ⟨ball_subset_closedBall hz,ha⟩).comp
        (f := fun z : ℂ => (z,a)) (analyticAt_id.prod analyticAt_const)
    have hSa : AnalyticOnNhd ℂ (fun z => hillHminusJointNormalizedGapRoot n r K (z,a))
        (ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r)) := by
      intro z hz
      exact (hJ (z,a) ⟨hz,ha⟩).comp (f := fun z : ℂ => (z,a)) (analyticAt_id.prod analyticAt_const)
    refine ⟨hr,hKa,hSa,(fun z hz => hrel (z,a) ⟨ball_subset_closedBall hz,ha⟩),
      (fun z hz => (hproperties (z,a) ⟨hz,ha⟩).2.2),
      (fun z hz => (hproperties (z,a) ⟨hz,ha⟩).2.1.trans_lt heta1),?_⟩
    obtain ⟨l,u,hpair,_⟩ := hpairs a ha
    exact ⟨l,u,hpair⟩
  refine ⟨K,⟨hr,hV,hK.mono (fun t ht => ⟨ball_subset_closedBall ht.1,ht.2⟩),hJ,hvalid⟩,?_⟩
  intro a ha
  obtain ⟨l,u,hpair,_⟩ := hpairs a ha
  have hR := norm_hillHminusNormalizedActionRatio_sub_one_le n r eta hr K a l u hpair (hvalid a ha).2.2.1
    (fun z hz => (hproperties (z,a) ⟨hz,ha⟩).2.1)
  refine ⟨hR.trans hetaε,?_⟩
  intro he
  rw [he,zero_sub,norm_neg,norm_one] at hR
  linarith

end NLS.KdV
