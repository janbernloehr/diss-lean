import NLS.KdV.HillCommonOwnPeriodLowerBound
import NLS.KdV.HillGlobalNormalizedDifferentials

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

/-- The actual original mixed contour functional, for any entire energy
numerator and the same low-original/high-free contour convention. -/
def hillMixedContourPeriod (N k : ℕ) (p : Coeff 2) (F : ℂ → ℂ) : ℂ :=
  if k<N then (2*(Real.pi : ℂ))⁻¹ * ∮ E in C((hillRealGapCenter q hq hr k : ℂ),
    hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k), F E/hillAbelianComplexRoot q hq hr (E,p)
  else (2*(Real.pi : ℂ))⁻¹ * ∮ E in C((hillRealGapCenter 0 h0q h0r k : ℂ),
    hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k), F E/hillAbelianComplexRoot 0 h0q h0r (E,p)

/-- The actual entire differential numerator divided by its own original
mixed normalization period. -/
def hillMixedNormalizedComplexPsi (N n : ℕ) (t : Coeff 2 × Coeff 2) (E : ℂ) : ℂ :=
  hillAbelianHilbertPsi n (E,t.1)/hillMixedOwnComplexPeriod q hq hr h0q h0r N n t

theorem hillMixedNormalizedComplexPsi_period_eq_ratio (N n k : ℕ) (t : Coeff 2 × Coeff 2) :
    hillMixedContourPeriod q hq hr h0q h0r N k t.2 (hillMixedNormalizedComplexPsi q hq hr h0q h0r N n t)=
      (if k<N then hillAbelianComplexPeriod q hq hr n k t else hillAbelianComplexPeriod 0 h0q h0r n k t)/
        hillMixedOwnComplexPeriod q hq hr h0q h0r N n t := by
  have he (root : ℂ → ℂ) : (fun E => hillMixedNormalizedComplexPsi q hq hr h0q h0r N n t E/root E)=
      (fun E => (hillMixedOwnComplexPeriod q hq hr h0q h0r N n t)⁻¹*(hillAbelianHilbertPsi n (E,t.1)/root E)) := by
    funext E
    unfold hillMixedNormalizedComplexPsi
    ring
  unfold hillMixedContourPeriod
  by_cases hkN : k<N
  · rw [if_pos hkN,if_pos hkN,he,circleIntegral.integral_const_mul]
    unfold hillAbelianComplexPeriod
    ring
  · rw [if_neg hkN,if_neg hkN,he,circleIntegral.integral_const_mul]
    unfold hillAbelianComplexPeriod
    ring

theorem analyticOnNhd_hillMixedNormalizedComplexPsi_chart
    (N n : ℕ) (a : Coeff 2 → Coeff 2) (U : Set (Coeff 2))
    (ha : AnalyticOnNhd ℂ a U)
    (hOwn : AnalyticOnNhd ℂ (fun p => hillMixedOwnComplexPeriod q hq hr h0q h0r N n (a p,p)) U)
    (hne : ∀ p∈U, hillMixedOwnComplexPeriod q hq hr h0q h0r N n (a p,p)≠0) :
    AnalyticOnNhd ℂ (fun t : ℂ × Coeff 2 => hillMixedNormalizedComplexPsi q hq hr h0q h0r N n (a t.2,t.2) t.1)
      (univ ×ˢ U) := by
  intro t ht
  have ha' : AnalyticAt ℂ (fun v : ℂ × Coeff 2 => a v.2) t := (ha t.2 ht.2).comp analyticAt_snd
  have hnum := (analyticOnNhd_hillAbelianHilbertPsi n (t.1,a t.2) (mem_univ _)).comp
    (f := fun v : ℂ × Coeff 2 => (v.1,a v.2)) (analyticAt_fst.prod ha')
  have hden := (hOwn t.2 ht.2).comp (f := fun v : ℂ × Coeff 2 => v.2) analyticAt_snd
  exact hnum.div hden (hne t.2 ht.2)

theorem hillMixedNormalizedComplexPsi_selected_at_base
    (N n : ℕ) (hN : 1≤N) (hn : 1≤n) (B D : ℝ)
    (hc : HillComplexTailPeriodControl h0q h0r N B D) (hp : ‖SpectralWeight.one.toCoeff q‖≤B) (E : ℂ) :
    hillMixedNormalizedComplexPsi q hq hr h0q h0r N n
      (hillAbelianSelectedGlobalRootCoordinates q hq hr n hn,SpectralWeight.one.toCoeff q) E=
      hillAbelianSelectedGlobalPsi q hq hr n hn E := by
  rw [hillMixedNormalizedComplexPsi,hillMixedOwnComplexPeriod_at_base q hq hr h0q h0r N n hN hn B D hc hp]
  rw [hillAbelianSelectedGlobalRootCoordinates,hillAbelianHilbertPsi_eq_genuine_candidate q hq hr
    (hillAbelianSelectedGlobalRoots q hq hr n hn).val (hillAbelianSelectedGlobalRoots q hq hr n hn).property n E,
    hillAbelianHilbertPeriod_eq_genuine_period q hq hr (hillAbelianSelectedGlobalRoots q hq hr n hn).val
      (hillAbelianSelectedGlobalRoots q hq hr n hn).property n n]
  rfl

/-- Common correctly normalized differential charts at every original
real source, with actual Kronecker periods and uniform own-period
reciprocal bounds on the whole complex source ball. -/
theorem exists_hillMixedNormalizedComplexPsi_common_charts :
    ∃ N : ℕ, ∃ B D δ A C c : ℝ, 1≤N ∧ 0<B ∧ 0<D ∧ HillComplexTailPeriodControl h0q h0r N B D ∧
      0<δ ∧ 0<A ∧ 0<C ∧ 0<c ∧ ball (SpectralWeight.one.toCoeff q) δ⊆ball 0 B ∧ ∀ n : ℕ, ∀ hn : 1≤n,
      ∃ a : Coeff 2 → Coeff 2, AnalyticOnNhd ℂ a (ball (SpectralWeight.one.toCoeff q) δ) ∧
        a (SpectralWeight.one.toCoeff q)=hillAbelianSelectedGlobalRootCoordinates q hq hr n hn ∧
        AnalyticOnNhd ℂ (fun t : ℂ × Coeff 2 => hillMixedNormalizedComplexPsi q hq hr h0q h0r N n (a t.2,t.2) t.1)
          (univ ×ˢ ball (SpectralWeight.one.toCoeff q) δ) ∧
        (∀ E : ℂ, hillMixedNormalizedComplexPsi q hq hr h0q h0r N n (a (SpectralWeight.one.toCoeff q),SpectralWeight.one.toCoeff q) E=
          hillAbelianSelectedGlobalPsi q hq hr n hn E) ∧
        ∀ p∈ball (SpectralWeight.one.toCoeff q) δ,
          ‖a p-hillAbelianSelectedGlobalRootCoordinates q hq hr n hn‖≤C*‖p-SpectralWeight.one.toCoeff q‖ ∧ ‖a p‖≤A ∧
          c≤‖hillMixedOwnComplexPeriod q hq hr h0q h0r N n (a p,p)‖ ∧
          ‖(hillMixedOwnComplexPeriod q hq hr h0q h0r N n (a p,p))⁻¹‖≤c⁻¹ ∧
          ∀ k : ℕ, 1≤k → hillMixedContourPeriod q hq hr h0q h0r N k p
            (hillMixedNormalizedComplexPsi q hq hr h0q h0r N n (a p,p))=if k=n then 1 else 0 := by
  obtain ⟨N,B,D,δ,A,C,c,hN,hB,hD,hc,hδ,hA,hC,hcpos,hsource,hcharts⟩ :=
    exists_hillMixedComplexPeriods_common_normalizable_root_coordinates q hq hr h0q h0r
  have hp0 : ‖SpectralWeight.one.toCoeff q‖≤B :=
    (show ‖SpectralWeight.one.toCoeff q‖<B by simpa only [mem_ball,dist_zero_right] using hsource (mem_ball_self hδ)).le
  refine ⟨N,B,D,δ,A,C,c,hN,hB,hD,hc,hδ,hA,hC,hcpos,hsource,?_⟩
  intro n hn
  obtain ⟨a,ha,hbase,hOwn,hinfo⟩ := hcharts n hn
  have hne (p : Coeff 2) (hp : p∈ball (SpectralWeight.one.toCoeff q) δ) :
      hillMixedOwnComplexPeriod q hq hr h0q h0r N n (a p,p)≠0 :=
    norm_pos_iff.mp (hcpos.trans_le (hinfo p hp).2.2.2.2.2)
  refine ⟨a,ha,hbase,analyticOnNhd_hillMixedNormalizedComplexPsi_chart q hq hr h0q h0r N n a _ ha hOwn hne,?_,?_⟩
  · intro E
    rw [hbase]
    exact hillMixedNormalizedComplexPsi_selected_at_base q hq hr h0q h0r N n hN hn B D hc hp0 E
  · intro p hp
    obtain ⟨hshift,hnorm,_,_,hperiods,hLower⟩ := hinfo p hp
    refine ⟨hshift,hnorm,hLower,?_,?_⟩
    · rw [norm_inv]
      exact inv_anti₀ hcpos hLower
    · intro k hk
      rw [hillMixedNormalizedComplexPsi_period_eq_ratio q hq hr h0q h0r N n k (a p,p)]
      by_cases hkn : k=n
      · subst k
        rw [if_pos rfl]
        change hillMixedOwnComplexPeriod q hq hr h0q h0r N n (a p,p)/hillMixedOwnComplexPeriod q hq hr h0q h0r N n (a p,p)=1
        exact div_self (hne p hp)
      · rw [if_neg hkn,hperiods k hk hkn,zero_div]

end NLS.KdV
