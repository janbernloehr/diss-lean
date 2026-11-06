import NLS.KdV.HillUniformComplexOwnPeriods
import NLS.KdV.HillUniformComplexPeriodRootBounds
import NLS.KdV.HillNearFreePhysicalPeriodRoots
import NLS.KdV.HillComplexNormalizedPeriodGerm
import NLS.KdV.HillGlobalNormalizedDifferentials

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal Classical

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

/-- Actual normalized differentials are jointly analytic on every common
chart on which their original own period is nonzero. -/
theorem analyticOnNhd_hillAbelianNormalizedComplexPsi_chart (n : ℕ) (hn : 1≤n)
    (ε D δ : ℝ) (hc : HillComplexPeriodControl h0q h0r ε D) (hδε : δ≤ε)
    (a : Coeff 2 → Coeff 2) (ha : AnalyticOnNhd ℂ a (ball 0 δ))
    (hne : ∀ p∈ball 0 δ, hillAbelianComplexPeriod 0 h0q h0r n n (a p,p)≠0) :
    AnalyticOnNhd ℂ (fun t : ℂ × Coeff 2 =>
      hillAbelianNormalizedComplexPsi h0q h0r n (a t.2,t.2) t.1) (univ ×ˢ ball 0 δ) := by
  have hP := analyticOnNhd_hillAbelianComplexPeriod_of_domain 0 h0q h0r n n hn
    (ball 0 ε) isOpen_ball
    (fun p hp E hE => (hc p (show ‖p‖≤ε from
      (show ‖p‖<ε by simpa only [mem_ball,dist_zero_right] using hp).le)).1 n hn E hE)
  intro t ht
  have ha' : AnalyticAt ℂ (fun v : ℂ × Coeff 2 => a v.2) t :=
    (ha t.2 ht.2).comp analyticAt_snd
  have hN := (analyticOnNhd_hillAbelianHilbertPsi n (t.1,a t.2) (mem_univ _)).comp
    (f := fun v : ℂ × Coeff 2 => (v.1,a v.2)) (analyticAt_fst.prod ha')
  have hD := (hP (a t.2,t.2) ⟨mem_univ _,ball_subset_ball hδε ht.2⟩).comp
    (f := fun v : ℂ × Coeff 2 => (a v.2,v.2)) (ha'.prod analyticAt_snd)
  exact hN.div hD (hne t.2 ht.2)

/-- Uniformly in n, the original common period roots have a nonzero own
normalization period, jointly analytic normalized numerator, and every
original normalized period equal to the Kronecker delta. -/
theorem exists_hillAbelianNormalizedComplexPsi_common_root_charts :
    ∃ δ C : ℝ, 0<δ ∧ 0<C ∧ ∀ n : ℕ, 1≤n →
      ∃ s : Coeff 2 → PositiveDeletedCoeff 2 (n : ℤ),
        AnalyticOnNhd ℂ s (ball 0 δ) ∧ s 0=0 ∧
        AnalyticOnNhd ℂ (fun t : ℂ × Coeff 2 =>
          hillAbelianNormalizedComplexPsi h0q h0r n ((s t.2 : Coeff 2),t.2) t.1)
          (univ ×ˢ ball 0 δ) ∧ (∀ p∈ball 0 δ,
          ‖s p‖≤C*‖p‖ ∧
          ‖hillAbelianComplexPeriod 0 h0q h0r n n ((s p : Coeff 2),p)-1‖<1/2 ∧
          1/2≤‖hillAbelianComplexPeriod 0 h0q h0r n n ((s p : Coeff 2),p)‖ ∧
          ∀ k : ℕ, 1≤k →
            (2*(Real.pi : ℂ))⁻¹ * ∮ E in C((hillRealGapCenter 0 h0q h0r k : ℂ),
              hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k),
              hillAbelianNormalizedComplexPsi h0q h0r n ((s p : Coeff 2),p) E/
                hillAbelianComplexRoot 0 h0q h0r (E,p) = if k=n then 1 else 0) ∧
        ∀ q : RealPeriodOneHillPotential, ‖q.val‖<δ →
          ∀ roots : ℕ → ℝ, ∀ hroots : roots∈hillGapRootBox q.val q.property.1 q.property.2,
          (∀ k : ℕ, 1≤k → k≠n → hillAbelianCandidatePeriod q.val q.property.1 q.property.2 roots n k=0) →
          Coeff.positiveDeletedProjectionTo 2 (n : ℤ)
            (hillGapRootHilbertCoordinates q.val q.property.1 q.property.2 roots hroots)=
              s (SpectralWeight.one.toCoeff q.val) := by
  obtain ⟨ρ,δc,C,hρ,hδc,hC,hcharts⟩ := exists_hillComplexFreeSupportedPeriods_common_linear_root_bound h0q h0r
  obtain ⟨r,L,hr,hL,hdev⟩ := exists_hillAbelianComplexOwnPeriod_common_linear_deviation h0q h0r
  obtain ⟨ε,D,hε,hD,hc⟩ := exists_hillComplexPeriodControl h0q h0r
  obtain ⟨δr,hδr,hrootbox⟩ := exists_hillGapRootHilbertCoordinates_uniform_small_at_zero h0q h0r ρ hρ
  let δbase := min δc (min ε (min (r/(C+1)) (1/(2*L*(C+1)))))
  let δ := min δbase δr
  have hbase : δ≤δbase := min_le_left _ _
  have hδbox : δ≤δr := min_le_right _ _
  have hδ : 0<δ := by dsimp only [δ,δbase];positivity
  have hδc' : δ≤δc := hbase.trans (min_le_left _ _)
  have hδε : δ≤ε := hbase.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδr : δ≤r/(C+1) := hbase.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hδL : δ≤1/(2*L*(C+1)) := hbase.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  refine ⟨δ,C,hδ,hC,?_⟩
  intro n hn
  obtain ⟨s,ha,hzero,hinfo⟩ := hcharts n hn
  have ha' : AnalyticOnNhd ℂ s (ball 0 δ) := ha.mono (ball_subset_ball hδc')
  have hsmall (p : Coeff 2) (hp : p∈ball 0 δ) :
      ‖hillAbelianComplexPeriod 0 h0q h0r n n ((s p : Coeff 2),p)-1‖<1/2 := by
    have hp' : ‖p‖<δ := by simpa only [mem_ball,dist_zero_right] using hp
    have hs := (hinfo p (ball_subset_ball hδc' hp)).1
    have ht : ‖((s p : Coeff 2),p)‖≤(C+1)*‖p‖ := by
      rw [Prod.norm_def,Submodule.norm_coe]
      apply max_le
      · nlinarith [norm_nonneg p]
      · nlinarith [norm_nonneg p]
    have ht' : (C+1)*‖p‖<r := by
      have hh := (lt_div_iff₀ (by positivity : 0<C+1)).mp (hp'.trans_le hδr)
      nlinarith
    have htball : ((s p : Coeff 2),p)∈ball 0 r := by
      rw [mem_ball,dist_zero_right]
      exact ht.trans_lt ht'
    apply (hdev n hn _ htball).trans_lt
    have hh : (2*L*(C+1))*‖p‖<1 := by
      have hh' := (lt_div_iff₀ (by positivity : 0<2*L*(C+1))).mp (hp'.trans_le hδL)
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_left ht hL.le]
  have hlow (p : Coeff 2) (hp : p∈ball 0 δ) :
      1/2≤‖hillAbelianComplexPeriod 0 h0q h0r n n ((s p : Coeff 2),p)‖ := by
    have hh := norm_sub_norm_le (1:ℂ) (hillAbelianComplexPeriod 0 h0q h0r n n ((s p : Coeff 2),p))
    rw [norm_one,norm_sub_rev] at hh
    linarith [hsmall p hp]
  have hne (p : Coeff 2) (hp : p∈ball 0 δ) :
      hillAbelianComplexPeriod 0 h0q h0r n n ((s p : Coeff 2),p)≠0 := by
    intro he
    have hh := hlow p hp
    rw [he,norm_zero] at hh
    norm_num at hh
  let inc := (ContinuousLinearMap.id ℂ (Coeff 2)-Coeff.positiveDeletedProjection 2 (n : ℤ)).ker.subtypeL
  have haCoeff : AnalyticOnNhd ℂ (fun p => (s p : Coeff 2)) (ball 0 δ) :=
    fun p hp => (inc.analyticAt (s p)).comp (ha' p hp)
  refine ⟨s,ha',hzero,analyticOnNhd_hillAbelianNormalizedComplexPsi_chart h0q h0r n hn ε D δ hc hδε
    (fun p => (s p : Coeff 2)) haCoeff hne,?_,?_⟩
  · intro p hp
    refine ⟨(hinfo p (ball_subset_ball hδc' hp)).1,hsmall p hp,hlow p hp,?_⟩
    intro k hk
    rw [hillAbelianNormalizedComplexPsi_period_eq_ratio]
    by_cases hkn : k=n
    · subst k
      rw [if_pos rfl,div_self (hne p hp)]
    · rw [if_neg hkn,(hinfo p (ball_subset_ball hδc' hp)).2.2.2.1 k hk hkn,zero_div]

  · intro q hq roots hroots hperiods
    let a := hillGapRootHilbertCoordinates q.val q.property.1 q.property.2 roots hroots
    let b := Coeff.positiveDeletedProjectionTo 2 (n : ℤ) a
    let p := SpectralWeight.one.toCoeff q.val
    have haρ : ‖a‖<ρ := hrootbox q (hq.trans_le hδbox) roots hroots
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
    exact (hinfo p hpδ).2.2.2.2 b hbρ hzeroB

include h0q h0r in
/-- Every original real root-box selection has its own physical period
uniformly close to one near zero; no normalized root selection is assumed. -/
theorem exists_hillAbelianCandidateOwnPeriod_uniform_lower_bound :
    ∃ δ : ℝ, 0<δ ∧ ∀ q : RealPeriodOneHillPotential, ‖q.val‖<δ →
      ∀ n : ℕ, 1≤n → ∀ roots : ℕ → ℝ,
        roots∈hillGapRootBox q.val q.property.1 q.property.2 →
          ‖hillAbelianCandidatePeriod q.val q.property.1 q.property.2 roots n n-1‖<1/2 ∧
          1/2≤‖hillAbelianCandidatePeriod q.val q.property.1 q.property.2 roots n n‖ := by
  obtain ⟨r,L,hr,hL,hdev⟩ := exists_hillAbelianComplexOwnPeriod_common_linear_deviation h0q h0r
  let η := min r (1/(4*L))
  have hη : 0<η := by dsimp only [η];positivity
  obtain ⟨δr,hδr,hbox⟩ := exists_hillGapRootHilbertCoordinates_uniform_small_at_zero h0q h0r η hη
  obtain ⟨ε,D,hε,_,hc⟩ := exists_hillComplexPeriodControl h0q h0r
  let δ := min δr (min η ε)
  have hδ : 0<δ := by dsimp only [δ];positivity
  refine ⟨δ,hδ,?_⟩
  intro q hq n hn roots hroots
  let a := hillGapRootHilbertCoordinates q.val q.property.1 q.property.2 roots hroots
  let p := SpectralWeight.one.toCoeff q.val
  have ha : ‖a‖<η := hbox q (hq.trans_le (min_le_left _ _)) roots hroots
  have hp : ‖p‖<η := (SpectralWeight.one.norm_toCoeff_le q.val).trans_lt
    (hq.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
  have hpε : ‖p‖≤ε := (SpectralWeight.one.norm_toCoeff_le q.val).trans
    (hq.le.trans ((min_le_right _ _).trans (min_le_right _ _)))
  have htη : ‖(a,p)‖<η := by rw [Prod.norm_def];exact max_lt ha hp
  have htr : (a,p)∈ball 0 r := by
    rw [mem_ball,dist_zero_right]
    exact htη.trans_le (min_le_left _ _)
  have he : hillAbelianComplexPeriod 0 h0q h0r n n (a,p)=
      hillAbelianCandidatePeriod q.val q.property.1 q.property.2 roots n n := by
    rw [hillAbelianComplexPeriod_near_free_eq_physical h0q h0r ε D hc q.val q.property.1 q.property.2 hpε n n hn]
    exact hillAbelianHilbertPeriod_eq_genuine_period q.val q.property.1 q.property.2 roots hroots n n
  have hsmall : ‖hillAbelianCandidatePeriod q.val q.property.1 q.property.2 roots n n-1‖<1/2 := by
    rw [← he]
    apply (hdev n hn _ htr).trans_lt
    have hh : ‖(a,p)‖<1/(4*L) := htη.trans_le (min_le_right _ _)
    have hh' := (lt_div_iff₀ (by positivity : 0<4*L)).mp hh
    nlinarith
  refine ⟨hsmall,?_⟩
  have hh := norm_sub_norm_le (1:ℂ) (hillAbelianCandidatePeriod q.val q.property.1 q.property.2 roots n n)
  rw [norm_one,norm_sub_rev] at hh
  linarith

/-- Exact matching of the original normalized complex numerator with the
original normalized physical numerator for every projected real root box. -/
theorem hillAbelianNormalizedComplexPsi_projected_real_roots
    (ε D : ℝ) (hc : HillComplexPeriodControl h0q h0r ε D)
    (q : RealPeriodOneHillPotential) (hp : ‖SpectralWeight.one.toCoeff q.val‖≤ε)
    (roots : ℕ → ℝ) (hroots : roots∈hillGapRootBox q.val q.property.1 q.property.2)
    (n : ℕ) (hn : 1≤n) (E : ℂ) :
    hillAbelianNormalizedComplexPsi h0q h0r n
      (Coeff.positiveDeletedProjection 2 (n : ℤ)
        (hillGapRootHilbertCoordinates q.val q.property.1 q.property.2 roots hroots),
        SpectralWeight.one.toCoeff q.val) E =
      hillAbelianPsiCandidate roots n E/hillAbelianCandidatePeriod q.val q.property.1 q.property.2 roots n n := by
  unfold hillAbelianNormalizedComplexPsi
  rw [hillAbelianHilbertPsi_positiveDeletedProjection,
    hillAbelianHilbertPsi_eq_genuine_candidate q.val q.property.1 q.property.2 roots hroots,
    hillAbelianComplexPeriod_near_free_eq_physical h0q h0r ε D hc q.val q.property.1 q.property.2 hp n n hn,
    hillAbelianHilbertPeriod_positiveDeletedProjection,
    hillAbelianHilbertPeriod_eq_genuine_period]

end NLS.KdV
