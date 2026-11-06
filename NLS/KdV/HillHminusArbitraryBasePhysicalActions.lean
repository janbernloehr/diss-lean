import NLS.KdV.HillHminusIntrinsicHighGapPairs
import NLS.KdV.HillHminusLocalActions

/-! # Original high actions on a neighborhood of any rough source

One complex H^-1 neighborhood and cutoff work before every high index.
On its entire real locus the analytic actions are the boundary integrals
between the intrinsic labels. Every physical L2 source in that rough
neighborhood has its ORIGINAL action, without any L2 norm restriction.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex NLS.ComplexAnalysis
namespace NLS.KdV

theorem exists_hillHminus_arbitrary_base_physical_high_actions (q : PeriodOneHminusOne) :
    ∃ r : ℝ, 0 < r ∧ r ≤ Real.pi/4 ∧ ∀ epsilon : ℝ, 0 < epsilon →
      ∃ N : ℕ, ∃ V : Set PeriodOneHminusOne, 2 ≤ N ∧ IsOpen V ∧ q ∈ V ∧
      ∀ n : ℕ+, N ≤ (n : ℕ) → ∃ K : ℂ × PeriodOneHminusOne → ℂ,
        AnalyticOnNhd ℂ K (hillHminusGapSquareDisc n r ×ˢ V) ∧
        (∀ t ∈ hillHminusGapSquareDisc n r ×ˢ V,
          squaredCosh (K t) = (-1 : ℂ)^(n : ℕ)*hillHminusDiscriminant t.2 t.1/2) ∧
        (∀ t ∈ (hillHminusGapSquareDisc n r ×ˢ V) ∩ hillHminusContinuationDomain,
          K t = (hillHminusContinuedPrimitive t+I*(n : ℂ)*Real.pi)^2) ∧
        AnalyticOnNhd ℂ (hillHminusJointNormalizedGapRoot n r K)
          (ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r) ×ˢ V) ∧
        AnalyticOnNhd ℂ (hillHminusLocalHighAction n r K) V ∧
        AnalyticOnNhd ℂ (hillHminusNormalizedActionRatio n r K) V ∧
        (∀ a ∈ V, ‖hillHminusNormalizedActionRatio n r K a-1‖ ≤ epsilon ∧
          hillHminusNormalizedActionRatio n r K a ≠ 0) ∧
        (∀ a ∈ V, ∀ ha : IsRealPeriodOneHminusOne a,
          hillHminusLocalHighAction n r K a = hillHminusGapBoundaryAction K a
            (hillHminusRealLabels a ha (2*(n : ℕ)-1))
            (hillHminusRealLabels a ha (2*(n : ℕ))) ∧
          hillHminusSquaredHalfGap n r a =
            (((hillHminusRealLabels a ha (2*(n : ℕ))-
              hillHminusRealLabels a ha (2*(n : ℕ)-1))/2 : ℝ) : ℂ)^2) ∧
        ∀ p : RealPeriodOneHillPotential, hillOriginalHminusSource p.val ∈ V →
          hillHminusLocalHighAction n r K (hillOriginalHminusSource p.val) =
            (hillRealGapIntegral p.val p.property.1 p.property.2 n 0 : ℂ) ∧
          hillHminusSquaredHalfGap n r (hillOriginalHminusSource p.val) =
            (hillRealGapHalfLength p.val p.property.1 p.property.2 n : ℂ)^2 := by
  obtain ⟨r,hr,hrpi,hfamily⟩ := exists_hillHminus_normalized_gap_squares q
  refine ⟨r,hr,hrpi,?_⟩
  intro epsilon hepsilon
  let eta : ℝ := min (1/2) epsilon
  have heta : 0 < eta := lt_min (by norm_num) hepsilon
  have heta1 : eta < 1 := (min_le_left _ _).trans_lt (by norm_num)
  have hetaε : eta ≤ epsilon := min_le_right _ _
  obtain ⟨N₁,V₁,_,hV₁,hq₁,hfamily⟩ := hfamily eta heta
  obtain ⟨N,s,V₂,hN₁,hN,hV₂,hq₂,hlabels⟩ := exists_hillHminusRealLabels_common_spec q N₁
  let V := V₁ ∩ V₂
  have hV : IsOpen V := hV₁.inter hV₂
  refine ⟨N,V,hN,hV,⟨hq₁,hq₂⟩,?_⟩
  intro n hn
  obtain ⟨K,hK,_,hrel,_,hmatch,hpairs⟩ := hfamily n (hN₁.trans hn)
  have hdata : ∀ a ∈ V₁, ∃ l u : ℂ, HillHminusHighGapPair a n r l u ∧
      (∀ z : ℂ, K (z,a) = (z-l)*(z-u)*twoRootDeflation (fun w => K (w,a)) l u z) ∧
      ∀ z ∈ hillHminusGapSquareDisc n r,
        ‖hillHminusNormalizedGapSquare n K a l u z-1‖ ≤ eta := by
    intro a ha
    obtain ⟨l,u,hpair,_,hf,hb⟩ := hpairs a ha
    exact ⟨l,u,hpair,hf,hb⟩
  obtain ⟨hJ,hproperties⟩ := hillHminusJointNormalizedGapRoot_properties n r eta hr heta1
    V₁ hV₁ K hK hdata
  have hP : ∀ a ∈ V, ∃ l u : ℂ, HillHminusHighGapPair a n r l u := by
    intro a ha
    obtain ⟨l,u,hpair,_⟩ := hpairs a ha.1
    exact ⟨l,u,hpair⟩
  have hJV : AnalyticOnNhd ℂ (hillHminusJointNormalizedGapRoot n r K)
      (ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r) ×ˢ V) :=
    fun t ht => hJ t ⟨ht.1,ht.2.1⟩
  have hf (a : PeriodOneHminusOne) (ha : a ∈ V) :=
    fun z hz => (hproperties (z,a) ⟨hz,ha.1⟩).2.2
  have hnorm (a : PeriodOneHminusOne) (ha : a ∈ V) :=
    fun z hz => (hproperties (z,a) ⟨hz,ha.1⟩).2.1
  have hcanonical (a : PeriodOneHminusOne) (ha : a ∈ V)
      (hreal : IsRealPeriodOneHminusOne a) :=
    (hlabels a ha.2 hreal).high_pair_of_radius hreal n hn (hP a ha)
  refine ⟨K,(fun t ht => hK t ⟨ht.1,ht.2.1⟩),
    (fun t ht => hrel t ⟨ht.1,ht.2.1⟩),
    (fun t ht => hmatch t ⟨⟨ht.1.1,ht.1.2.1⟩,ht.2⟩),hJV,
    analyticOnNhd_hillHminusLocalHighAction n r hr V hV K hJV hP,
    analyticOnNhd_hillHminusNormalizedActionRatio n r hr V hV K hJV hP,?_,?_,?_⟩
  · intro a ha
    obtain ⟨l,u,hpair⟩ := hP a ha
    have hS : AnalyticOnNhd ℂ (fun z => hillHminusJointNormalizedGapRoot n r K (z,a))
        (ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r)) := by
      intro z hz
      exact (hJV (z,a) ⟨hz,ha⟩).comp (f := fun w : ℂ => (w,a))
        (analyticAt_id.prod analyticAt_const)
    have hb := norm_hillHminusNormalizedActionRatio_sub_one_le n r eta hr K a l u
      hpair hS (hnorm a ha)
    refine ⟨hb.trans hetaε,?_⟩
    intro he
    rw [he,zero_sub,norm_neg,norm_one] at hb
    linarith
  · intro a ha hreal
    have hpair := hcanonical a ha hreal
    refine ⟨hillHminusLocalHighAction_eq_boundary n r eta hr heta1 V K hJV a ha _ _
      (monotone_hillHminusRealLabels a hreal (by omega)) hpair (hf a ha) (hnorm a ha),?_⟩
    rw [(hpair.symmetric_gap_data hr).2]
    push_cast
    rfl
  · intro p hp
    have hactual := HillHminusRealCharacteristicLabeling.physical_high_pair_of_radius p
      (hlabels _ hp.2 (hillOriginalHminusSource_real p.val p.property.2)) n hn (hP _ hp)
    constructor
    · calc
        hillHminusLocalHighAction n r K (hillOriginalHminusSource p.val) =
            hillHminusGapBoundaryAction K (hillOriginalHminusSource p.val)
              (hillRealLabels p.val p.property.1 p.property.2 (2*(n : ℕ)-1))
              (hillRealLabels p.val p.property.1 p.property.2 (2*(n : ℕ))) :=
          hillHminusLocalHighAction_eq_boundary n r eta hr heta1 V K hJV _ hp _ _
            (monotone_hillRealLabels p.val p.property.1 p.property.2 (by omega))
            hactual (hf _ hp) (hnorm _ hp)
        _ = _ := hillHminusGapBoundaryAction_eq_original_action p n r eta hr heta1
          V₁ K hK hmatch hp.1 hactual (hf _ hp) (hnorm _ hp)
    · rw [(hactual.symmetric_gap_data hr).2]
      simp only [hillRealGapHalfLength,ofReal_div,ofReal_sub,ofReal_ofNat]

end NLS.KdV
