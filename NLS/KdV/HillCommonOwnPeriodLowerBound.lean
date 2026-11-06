import NLS.KdV.HillHighOwnPeriodLowerBound
import NLS.KdV.HillMixedOwnPeriod
import NLS.ComplexAnalysis.FiniteFamilyLowerBound

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

/-- Uniform high-contour control and finite-head continuity give one
positive own-period lower bound along the actual common root families. -/
theorem exists_hillMixedOwnComplexPeriod_uniform_lower_bound
    (N : ℕ) (hN : 1≤N) (B D δ A C : ℝ) (hB : 0<B) (hδ : 0<δ) (hC : 0<C)
    (hc : HillComplexTailPeriodControl h0q h0r N B D) (hsource : ball (SpectralWeight.one.toCoeff q) δ⊆ball 0 B)
    (a : ∀ n : ℕ, 1≤n → Coeff 2 → Coeff 2)
    (ha : ∀ n hn, AnalyticOnNhd ℂ (a n hn) (ball (SpectralWeight.one.toCoeff q) δ))
    (hbase : ∀ n hn, a n hn (SpectralWeight.one.toCoeff q)=hillAbelianSelectedGlobalRootCoordinates q hq hr n hn)
    (hbound : ∀ n hn p, p∈ball (SpectralWeight.one.toCoeff q) δ → ‖a n hn p‖≤A ∧
      ‖a n hn p-hillAbelianSelectedGlobalRootCoordinates q hq hr n hn‖≤C*‖p-SpectralWeight.one.toCoeff q‖) :
    ∃ ε c : ℝ, 0<ε ∧ ε≤δ ∧ 0<c ∧ ∀ n : ℕ, ∀ hn : 1≤n,
      AnalyticOnNhd ℂ (fun p => hillMixedOwnComplexPeriod q hq hr h0q h0r N n (a n hn p,p))
        (ball (SpectralWeight.one.toCoeff q) ε) ∧
      ∀ p∈ball (SpectralWeight.one.toCoeff q) ε,
        c≤‖hillMixedOwnComplexPeriod q hq hr h0q h0r N n (a n hn p,p)‖ := by
  let p0 := SpectralWeight.one.toCoeff q
  obtain ⟨V,hV,hqV,hLow⟩ := exists_hillAbelianComplexPeriods_common_finite_neighborhood q hq hr N
  obtain ⟨δV,hδV,hδVball⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hqV)
  let r := min δ δV
  have hrpos : 0<r := by dsimp only [r];positivity
  have hrδ : r≤δ := min_le_left _ _
  have hrV : r≤δV := min_le_right _ _
  have hsub : ball p0 r⊆ball 0 B := (ball_subset_ball hrδ).trans hsource
  have hLow' (k : ℕ) (hk : 1≤k) (hkN : k<N) :
      AnalyticOnNhd ℂ (hillAbelianComplexPeriod q hq hr k k) (univ ×ˢ ball p0 r) :=
    (hLow k k hk hkN).mono (fun t ht => ⟨mem_univ _,hδVball (ball_subset_ball hrV ht.2)⟩)
  have hOwn (n : ℕ) (hn : 1≤n) : AnalyticOnNhd ℂ
      (fun p => hillMixedOwnComplexPeriod q hq hr h0q h0r N n (a n hn p,p)) (ball p0 r) := by
    have hj := analyticOnNhd_hillMixedOwnComplexPeriod q hq hr h0q h0r N n hn B D hc (ball p0 r) isOpen_ball hsub hLow'
    intro p hp
    exact (hj (a n hn p,p) ⟨mem_univ _,hp⟩).comp
      (f := fun p : Coeff 2 => (a n hn p,p)) ((ha n hn p (ball_subset_ball hrδ hp)).prod analyticAt_id)
  have hp0 : ‖p0‖≤B :=
    (show ‖p0‖<B by simpa only [mem_ball,dist_zero_right] using hsource (mem_ball_self hδ)).le
  have hOwn0 (n : ℕ) (hn : 1≤n) : hillMixedOwnComplexPeriod q hq hr h0q h0r N n (a n hn p0,p0)≠0 := by
    rw [hbase n hn]
    exact hillMixedOwnComplexPeriod_selected_ne_zero q hq hr h0q h0r N n hN hn B D hc hp0
  let K := range (fun roots : hillGapRootBox q hq hr => hillGapRootHilbertCoordinates q hq hr roots.val roots.property)
  obtain ⟨J0,η,hJ0,hη,hHigh⟩ := exists_hillAbelianComplexOwnPeriod_uniform_high_near_compact h0q h0r
    K (isCompact_range_hillGapRootHilbertCoordinates q hq hr) B A hB.le
  let J := max N J0
  let F : Fin J → Coeff 2 → ℂ := fun j p => if hj : 1≤j.val then
    hillMixedOwnComplexPeriod q hq hr h0q h0r N j.val (a j.val hj p,p) else 1
  have hF (j : Fin J) : ContinuousAt (F j) p0 := by
    by_cases hj : 1≤j.val
    · simpa only [F,dif_pos hj] using (hOwn j.val hj p0 (mem_ball_self hrpos)).continuousAt
    · simp only [F,dif_neg hj]
      exact continuousAt_const
  have hF0 (j : Fin J) : F j p0≠0 := by
    by_cases hj : 1≤j.val
    · simpa only [F,dif_pos hj] using hOwn0 j.val hj
    · simp only [F,dif_neg hj,ne_eq,one_ne_zero,not_false_eq_true]
  obtain ⟨ε0,c0,hε0,hc0,hHead⟩ := exists_finite_family_norm_lower_bound F p0 hF hF0
  let ε := min r (min ε0 (η/(C+1)))
  let c := min (1/2) c0
  have hε : 0<ε := by dsimp only [ε];positivity
  have hcpos : 0<c := by dsimp only [c];positivity
  have hεr : ε≤r := min_le_left _ _
  have hεδ : ε≤δ := hεr.trans hrδ
  have hε0' : ε≤ε0 := (min_le_right _ _).trans (min_le_left _ _)
  have hεη : ε≤η/(C+1) := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨ε,c,hε,hεδ,hcpos,?_⟩
  intro n hn
  refine ⟨(hOwn n hn).mono (ball_subset_ball hεr),?_⟩
  intro p hp
  by_cases hnJ : J≤n
  · have hpδ := ball_subset_ball hεδ hp
    have hpB : ‖p‖≤B := (show ‖p‖<B by simpa only [mem_ball,dist_zero_right] using hsource hpδ).le
    have hpη : ‖p-p0‖<η/(C+1) := by
      have hh : ‖p-p0‖<ε := by simpa only [mem_ball,dist_eq_norm] using hp
      exact hh.trans_le hεη
    have hprod : (C+1)*‖p-p0‖<η := by
      have hh := (lt_div_iff₀ (by positivity : 0<C+1)).mp hpη
      nlinarith only [hh]
    have hshift : ‖a n hn p-hillAbelianSelectedGlobalRootCoordinates q hq hr n hn‖<η :=
      (hbound n hn p hpδ).2.trans_lt (by nlinarith [norm_nonneg (p-p0)])
    have hfree := hHigh n ((le_max_right _ _).trans hnJ)
      (hillAbelianSelectedGlobalRootCoordinates q hq hr n hn) ⟨hillAbelianSelectedGlobalRoots q hq hr n hn,rfl⟩
      (a n hn p) p (hbound n hn p hpδ).1 hpB hshift
    have hnorm : (1/2 : ℝ)≤‖hillAbelianComplexPeriod 0 h0q h0r n n (a n hn p,p)‖ := by
      have hh := norm_le_norm_sub_add (1 : ℂ) (hillAbelianComplexPeriod 0 h0q h0r n n (a n hn p,p))
      rw [norm_one,norm_sub_rev] at hh
      linarith
    rw [hillMixedOwnComplexPeriod,if_neg (by have hh := (le_max_left N J0).trans hnJ;omega)]
    exact (min_le_left _ _).trans hnorm
  · let j : Fin J := ⟨n,by omega⟩
    have hh := hHead p (ball_subset_ball hε0' hp) j
    have hnorm : c0≤‖hillMixedOwnComplexPeriod q hq hr h0q h0r N n (a n hn p,p)‖ := by
      simpa only [F,j,dif_pos hn] using hh
    exact (min_le_right _ _).trans hnorm

/-- Every original real source admits actual bounded Hilbert root charts
and a common positive own-period lower bound for all differential indices. -/
theorem exists_hillMixedComplexPeriods_common_normalizable_root_coordinates :
    ∃ N : ℕ, ∃ B D δ A C c : ℝ, 1≤N ∧ 0<B ∧ 0<D ∧ HillComplexTailPeriodControl h0q h0r N B D ∧
      0<δ ∧ 0<A ∧ 0<C ∧ 0<c ∧ ball (SpectralWeight.one.toCoeff q) δ⊆ball 0 B ∧ ∀ n : ℕ, ∀ hn : 1≤n,
      ∃ a : Coeff 2 → Coeff 2, AnalyticOnNhd ℂ a (ball (SpectralWeight.one.toCoeff q) δ) ∧
        a (SpectralWeight.one.toCoeff q)=hillAbelianSelectedGlobalRootCoordinates q hq hr n hn ∧
        AnalyticOnNhd ℂ (fun p => hillMixedOwnComplexPeriod q hq hr h0q h0r N n (a p,p)) (ball (SpectralWeight.one.toCoeff q) δ) ∧
        ∀ p∈ball (SpectralWeight.one.toCoeff q) δ,
          ‖a p-hillAbelianSelectedGlobalRootCoordinates q hq hr n hn‖≤C*‖p-SpectralWeight.one.toCoeff q‖ ∧
          ‖a p‖≤A ∧ a p (n : ℤ)=hillAbelianSelectedGlobalRootCoordinates q hq hr n hn (n : ℤ) ∧
          hillMixedComplexPeriodSequence q hq hr h0q h0r N n (a p,p)=0 ∧
          (∀ k : ℕ, 1≤k → k≠n →
            (if k<N then hillAbelianComplexPeriod q hq hr n k (a p,p) else hillAbelianComplexPeriod 0 h0q h0r n k (a p,p))=0) ∧
          c≤‖hillMixedOwnComplexPeriod q hq hr h0q h0r N n (a p,p)‖ := by
  obtain ⟨N,B,D,δ,A,C,hN,hB,hD,hc,hδ,hA,hC,hsource,hcharts⟩ :=
    exists_hillMixedComplexPeriods_common_root_coordinates q hq hr h0q h0r
  choose a ha hbase hinfo using hcharts
  have hbound : ∀ n hn p, p∈ball (SpectralWeight.one.toCoeff q) δ → ‖a n hn p‖≤A ∧
      ‖a n hn p-hillAbelianSelectedGlobalRootCoordinates q hq hr n hn‖≤C*‖p-SpectralWeight.one.toCoeff q‖ := by
    intro n hn p hp
    exact ⟨(hinfo n hn p hp).2.1,(hinfo n hn p hp).1⟩
  obtain ⟨ε,c,hε,hεδ,hcpos,hOwn⟩ := exists_hillMixedOwnComplexPeriod_uniform_lower_bound q hq hr h0q h0r
    N hN B D δ A C hB hδ hC hc hsource a ha hbase hbound
  have hsub : ball (SpectralWeight.one.toCoeff q) ε⊆ball (SpectralWeight.one.toCoeff q) δ := ball_subset_ball hεδ
  refine ⟨N,B,D,ε,A,C,c,hN,hB,hD,hc,hε,hA,hC,hcpos,hsub.trans hsource,?_⟩
  intro n hn
  refine ⟨a n hn,(ha n hn).mono hsub,hbase n hn,(hOwn n hn).1,?_⟩
  intro p hp
  obtain ⟨hs,hA',hcoord,hzero,hperiods⟩ := hinfo n hn p (hsub hp)
  exact ⟨hs,hA',hcoord,hzero,hperiods,(hOwn n hn).2 p hp⟩

end NLS.KdV
