import NLS.KdV.HillHminusLocalActions

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
namespace NLS.KdV

/-- One common complex H-minus-one neighborhood supports analytic extensions
of ALL sufficiently high ORIGINAL physical actions. One common original-real
neighborhood retains every physical action and label, including collapsed
gaps. The normalized analytic ratios are uniformly close to one without
dividing by the gap square. -/
theorem exists_hillOriginal_high_actions_common_hminus_extension
    (q : RealPeriodOneHillPotential) :
    ∃ r : ℝ, 0<r ∧ r≤Real.pi/4 ∧ ∀ epsilon : ℝ, 0<epsilon →
      ∃ N : ℕ, ∃ V : Set PeriodOneHminusOne, ∃ W : Set RealPeriodOneHillPotential,
        2≤N ∧ IsOpen V ∧ hillOriginalHminusSource q.val∈V ∧ IsOpen W ∧ q∈W ∧
        ∀ n : ℕ+, N≤(n : ℕ) → ∃ A R : PeriodOneHminusOne → ℂ,
          AnalyticOnNhd ℂ A V ∧ AnalyticOnNhd ℂ R V ∧
          (∀ a∈V, ‖R a-1‖≤epsilon ∧ R a≠0 ∧
            A a=hillHminusSquaredHalfGap n r a/(2*((Real.pi : ℂ)*(n : ℕ)))*R a) ∧
          ∀ p∈W, A (hillOriginalHminusSource p.val)=
            (hillRealGapIntegral p.val p.property.1 p.property.2 n 0 : ℂ) := by
  obtain ⟨r,hr,hrpi,hfamily⟩ := exists_hillHminus_normalized_gap_squares (hillOriginalHminusSource q.val)
  refine ⟨r,hr,hrpi,?_⟩
  intro epsilon hepsilon
  let eta : ℝ := min (1/2) epsilon
  have heta : 0<eta := lt_min (by norm_num) hepsilon
  have heta1 : eta<1 := (min_le_left _ _).trans_lt (by norm_num)
  have hetaε : eta≤epsilon := min_le_right _ _
  obtain ⟨N₁,V,hN₁,hV,hqV,hfamily⟩ := hfamily eta heta
  let B : ℝ := ‖q.val‖+1
  obtain ⟨N₂,hN₂⟩ := exists_nat_gt (max (8*B) (4*B/(Real.pi*r)))
  let N := max 2 (max N₁ N₂)
  let W : Set RealPeriodOneHillPotential :=
    {p | hillOriginalHminusSource p.val∈V ∧ ‖p.val‖<B}
  have hW : IsOpen W := (hV.preimage (hillOriginalHminusSource.continuous.comp continuous_subtype_val)).inter
    (isOpen_lt continuous_subtype_val.norm continuous_const)
  have hqW : q∈W := ⟨hqV,by dsimp only [B]; linarith⟩
  refine ⟨N,V,W,le_max_left _ _,hV,hqV,hW,hqW,?_⟩
  intro n hn
  have hn₁ : N₁≤(n : ℕ) := by dsimp only [N] at hn; omega
  have hn₂ : (N₂ : ℝ)≤(n : ℕ) := by
    exact_mod_cast (show N₂≤(n : ℕ) by dsimp only [N] at hn; omega)
  have hn2 : 2≤(n : ℕ) := (le_max_left _ _).trans hn
  obtain ⟨K,hK,_,_,_,hmatch,hpairs⟩ := hfamily n hn₁
  have hdata : ∀ a∈V, ∃ l u : ℂ, HillHminusHighGapPair a n r l u ∧
      (∀ z : ℂ, K (z,a)=(z-l)*(z-u)*twoRootDeflation (fun w => K (w,a)) l u z) ∧
      ∀ z∈hillHminusGapSquareDisc n r, ‖hillHminusNormalizedGapSquare n K a l u z-1‖≤eta := by
    intro a ha
    obtain ⟨l,u,hpair,_,hf,hb⟩ := hpairs a ha
    exact ⟨l,u,hpair,hf,hb⟩
  obtain ⟨hJ,hproperties⟩ := hillHminusJointNormalizedGapRoot_properties n r eta hr heta1 V hV K hK hdata
  have hP : ∀ a∈V, ∃ l u : ℂ, HillHminusHighGapPair a n r l u := by
    intro a ha
    obtain ⟨l,u,hpair,_⟩ := hpairs a ha
    exact ⟨l,u,hpair⟩
  let A := hillHminusLocalHighAction n r K
  let R := hillHminusNormalizedActionRatio n r K
  have hR := analyticOnNhd_hillHminusNormalizedActionRatio n r hr V hV K hJ hP
  refine ⟨A,R,analyticOnNhd_hillHminusLocalHighAction n r hr V hV K hJ hP,hR,?_,?_⟩
  · intro a ha
    obtain ⟨l,u,hpair⟩ := hP a ha
    have hS : AnalyticOnNhd ℂ (fun z => hillHminusJointNormalizedGapRoot n r K (z,a))
        (ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r)) := by
      intro z hz
      exact (hJ (z,a) ⟨hz,ha⟩).comp (f := fun z : ℂ => (z,a)) (analyticAt_id.prod analyticAt_const)
    have hb := norm_hillHminusNormalizedActionRatio_sub_one_le n r eta hr K a l u hpair hS
      (fun z hz => (hproperties (z,a) ⟨hz,ha⟩).2.1)
    refine ⟨hb.trans hetaε,?_,rfl⟩
    intro he
    have hh : 1≤eta := by simpa only [show hillHminusNormalizedActionRatio n r K a=0 from he,
      zero_sub,norm_neg,norm_one] using hb
    linarith
  · intro p hp
    have hc : 8*‖p.val‖≤(n : ℕ) :=
      (mul_le_mul_of_nonneg_left hp.2.le (by norm_num : (0 : ℝ)≤8)).trans
        ((le_max_left _ _).trans (hN₂.le.trans hn₂))
    have hb : 4*‖p.val‖≤Real.pi*(n : ℕ)*r := by
      have hd : 4*B/(Real.pi*r)≤(n : ℕ) := (le_max_right _ _).trans (hN₂.le.trans hn₂)
      have hh := (div_le_iff₀ (mul_pos Real.pi_pos hr)).mp hd
      have hBp : ‖p.val‖≤B := hp.2.le
      nlinarith
    obtain ⟨l,u,hpair⟩ := hP (hillOriginalHminusSource p.val) hp.1
    have hactual := hpair.original_labelled_pair p n hn2 r l u hc hb
    have hf := fun z hz => (hproperties (z,hillOriginalHminusSource p.val) ⟨hz,hp.1⟩).2.2
    have hnorm := fun z hz => (hproperties (z,hillOriginalHminusSource p.val) ⟨hz,hp.1⟩).2.1
    calc
      A (hillOriginalHminusSource p.val)=hillHminusGapBoundaryAction K (hillOriginalHminusSource p.val)
          (hillRealLabels p.val p.property.1 p.property.2 (2*(n : ℕ)-1))
          (hillRealLabels p.val p.property.1 p.property.2 (2*(n : ℕ))) :=
        hillHminusLocalHighAction_eq_boundary n r eta hr heta1 V K hJ _ hp.1 _ _
          (monotone_hillRealLabels p.val p.property.1 p.property.2 (by omega)) hactual hf hnorm
      _ = _ := hillHminusGapBoundaryAction_eq_original_action p n r eta hr heta1 V K hK hmatch hp.1 hactual hf hnorm

end NLS.KdV
