import NLS.KdV.HillUniformDeflatedGapCharts
import NLS.KdV.HillClosedGapCenteredData
import NLS.KdV.HillCenteredDeflatedMeanPhysical
import NLS.KdV.HillClosedGapAbelianCorrections
import NLS.KdV.HillGlobalRegularCorrection

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

include h0q h0r in
/-- Any original collapsed gap has common bounded analytic regular
correction charts, with exact physical matching and inverse-index size. -/
theorem exists_hillRegularAbelianCorrection_uniform_closed_gap_charts
    (k : ℕ) (hk : 1≤k) (hgap0 : hillRealGapHalfLength q hq hr k=0) :
    ∃ δ C : ℝ, ∃ V : Set RealPeriodOneHillPotential,
      0<δ ∧ 0<C ∧ IsOpen V ∧ (⟨q,hq,hr⟩ : RealPeriodOneHillPotential)∈V ∧
      (∀ p∈V, SpectralWeight.one.toCoeff p.val∈ball (SpectralWeight.one.toCoeff q) δ) ∧
      ∀ n : ℕ, ∀ hn : 1≤n, ∃ β : Coeff 2 → ℂ,
        AnalyticOnNhd ℂ β (ball (SpectralWeight.one.toCoeff q) δ) ∧
        (∀ p∈ball (SpectralWeight.one.toCoeff q) δ, ‖β p‖≤C/(n : ℝ)) ∧
        ∀ p∈V, β (SpectralWeight.one.toCoeff p.val)=
          hillRegularAbelianCorrection p.val p.property.1 p.property.2 n hn k hk := by
  obtain ⟨δh,Bh,E,Vh,hδh,hBh,hE,hVh,hgapE,hqVh,_,hcharts⟩ :=
    exists_hillDeflatedNormalizedDifferential_uniform_gap_charts q hq hr h0q h0r k hk
  obtain ⟨Er,Vr,hEr,hVr,hgapEr,hqVr,hrootmatch⟩ := exists_hillLocalDeflatedComplexRoot_gap_physical_matching q hq hr k hk
  let c : ℂ := hillRealGapCenter q hq hr k
  let p0 := SpectralWeight.one.toCoeff q
  let τ := hillLocalGapMidpoint q hq hr k
  let s : Coeff 2 → ℂ := fun p => hillLocalGapSquare q hq hr k p/4
  have hcenter : c=(hillRealLabels q hq hr (2*k-1) : ℂ) := by
    have hh := (hillRealGapContour_geometry q hq hr k hk).2.2.1
    rw [hgap0,sub_zero] at hh
    exact congrArg Complex.ofReal hh
  have hc : c∈E∩Er := by
    rw [hcenter]
    exact ⟨hgapE (left_mem_segment ℝ _ _),hgapEr (left_mem_segment ℝ _ _)⟩
  obtain ⟨r0,hr0,hr0sub⟩ := Metric.mem_nhds_iff.mp ((hE.inter hEr).mem_nhds hc)
  let r := r0/2
  have hradius : 0<r := by dsimp only [r];positivity
  have hball (z : ℂ) (hz : z∈closedBall c r) : z∈E∩Er := hr0sub
    (closedBall_subset_ball (by dsimp only [r];linarith : r<r0) hz)
  obtain ⟨δd,μ,Vd,hδd,hVd,hqVd,_,hμa,hτa,hsa,hdata,hdreal⟩ :=
    exists_hillClosedGap_centered_Dirichlet_data q hq hr k hk hgap0 r hradius
  have hμdom : (μ p0,p0)∈hillLocalDeflatedRootDomain q hq hr k := by
    rw [(hdreal (⟨q,hq,hr⟩ : RealPeriodOneHillPotential) hqVd).1]
    exact mem_hillLocalDeflatedRootDomain_base q hq hr k hk _
      (hillRealGapSegment_subset_intrinsic_contour_ball q hq hr k hk
        (ofReal_mem_ordered_segment _ _ _ (monotone_hillRealLabels q hq hr (by omega)) (hillDirichletEnergy_mem_gap q hq hr k hk)))
  let P : Coeff 2 → ℂ := fun p => I*hillDirichletSheetRoot p (μ p)/hillLocalDeflatedComplexRoot q hq hr k (μ p,p)
  have hPa0 : AnalyticAt ℂ P p0 := by
    have hm := hμa p0 (mem_ball_self hδd)
    have hroot := (analyticOnNhd_hillLocalDeflatedComplexRoot q hq hr k hk _ hμdom).comp
      (f := fun p : Coeff 2 => (μ p,p)) (hm.prod analyticAt_id)
    have hsheet := (analyticOnNhd_hillDirichletSheetRoot_joint (μ p0,p0) (mem_univ _)).comp
      (f := fun p : Coeff 2 => (μ p,p)) (hm.prod analyticAt_id)
    exact (analyticAt_const.mul hsheet).div hroot (hillLocalDeflatedComplexRoot_ne_zero q hq hr k hk _ hμdom)
  let T := ‖P p0‖+1
  have hT : 0<T := by dsimp only [T];positivity
  have hnear : {p : Coeff 2 | AnalyticAt ℂ P p ∧ ‖P p‖<T}∈𝓝 p0 :=
    inter_mem ((isOpen_analyticAt ℂ P).mem_nhds hPa0)
      (hPa0.continuousAt.norm.tendsto.eventually (isOpen_Iio.mem_nhds (show ‖P p0‖<T by dsimp only [T];linarith)))
  obtain ⟨ε,hε,hεnear⟩ := Metric.mem_nhds_iff.mp hnear
  let δ := min δh (min δd ε)
  have hδ : 0<δ := lt_min hδh (lt_min hδd hε)
  have hdh : δ≤δh := min_le_left _ _
  have hdd : δ≤δd := (min_le_right _ _).trans (min_le_left _ _)
  have hde : δ≤ε := (min_le_right _ _).trans (min_le_right _ _)
  let J : RealPeriodOneHillPotential → Coeff 2 := fun p => SpectralWeight.one.toCoeff p.val
  have hJ : Continuous J := SpectralWeight.one.toCoeff.continuous.comp continuous_subtype_val
  let V := ((Vh∩Vd)∩Vr)∩J ⁻¹' ball p0 δ
  have hV : IsOpen V := ((hVh.inter hVd).inter hVr).inter (isOpen_ball.preimage hJ)
  have hqV : (⟨q,hq,hr⟩ : RealPeriodOneHillPotential)∈V := by
    refine ⟨⟨⟨hqVh,hqVd⟩,hqVr⟩,?_⟩
    change p0∈ball p0 δ
    exact mem_ball_self hδ
  let C := T*(64*Real.pi*Bh/r)
  have hC : 0<C := by dsimp only [C];positivity
  refine ⟨δ,C,V,hδ,hC,hV,hqV,(fun p hp => hp.2),?_⟩
  intro n hn
  obtain ⟨H,hHa,hHb,hHreal⟩ := hcharts n hn
  let U : Set (Coeff 2) := ball p0 δ
  let f : ℂ × Coeff 2 → ℂ := fun t => H (τ t.2+t.1,t.2)
  have hpos (w : ℂ) (hw : w∈closedBall (0 : ℂ) (r/2)) (p : Coeff 2) (hp : p∈U) : τ p+w∈closedBall c r := by
    have ht := (hdata p (ball_subset_ball hdd hp)).1
    have hw' : ‖w‖≤r/2 := by simpa only [mem_closedBall,dist_zero_right] using hw
    rw [mem_closedBall,dist_eq_norm]
    have hh : ‖τ p+w-c‖≤‖τ p-c‖+‖w‖ := by
      rw [show τ p+w-c=(τ p-c)+w by ring]
      exact norm_add_le _ _
    linarith
  have hf : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) (r/2) ×ˢ U) := by
    intro t ht
    have hm := (hτa t.2 (ball_subset_ball hdd ht.2)).comp (f := fun u : ℂ × Coeff 2 => u.2) analyticAt_snd
    exact (hHa (τ t.2+t.1,t.2) ⟨(hball _ (hpos t.1 ht.1 t.2 ht.2)).1,ball_subset_ball hdh ht.2⟩).comp
      (f := fun u : ℂ × Coeff 2 => (τ u.2+u.1,u.2)) ((hm.add analyticAt_fst).prod analyticAt_snd)
  have hb (p : Coeff 2) (hp : p∈U) (w : ℂ) (hw : w∈closedBall (0 : ℂ) (r/2)) : ‖f (w,p)‖≤Bh/(n : ℝ) :=
    hHb p (ball_subset_ball hdh hp) _ (hball _ (hpos w hw p hp)).1
  have hs : AnalyticOnNhd ℂ s U := hsa.mono (ball_subset_ball hdd)
  have hsmall (p : Coeff 2) (hp : p∈U) : ‖s p‖<((r/2)/8)^2 := by
    have hh := (hdata p (ball_subset_ball hdd hp)).2.1
    nlinarith
  obtain ⟨Q,hQa,hODE,hQb⟩ := exists_bounded_analytic_centered_mean_free_quadratic_solution f s U isOpen_ball
    (r/2) (Bh/(n : ℝ)) (by positivity) (by positivity) hf hs hsmall hb
  have hr2 : (r/2)/2=r/4 := by ring
  have hr4 : (r/2)/4=r/8 := by ring
  rw [hr2] at hQa hODE
  rw [hr4] at hQb
  let β : Coeff 2 → ℂ := fun p => P p*Q (μ p-τ p,p)
  refine ⟨β,?_,?_,?_⟩
  · intro p hp
    have harg := (hdata p (ball_subset_ball hdd hp)).2.2.1
    have hw : μ p-τ p∈ball (0 : ℂ) (r/4) := by
      rw [mem_ball,dist_zero_right]
      exact harg.trans (by linarith)
    have hm := hμa p (ball_subset_ball hdd hp)
    have ht := hτa p (ball_subset_ball hdd hp)
    exact (hεnear (ball_subset_ball hde hp)).1.mul ((hQa (μ p-τ p,p) ⟨hw,hp⟩).comp
      (f := fun p : Coeff 2 => (μ p-τ p,p)) ((hm.sub ht).prod analyticAt_id))
  · intro p hp
    have harg := (hdata p (ball_subset_ball hdd hp)).2.2.1
    have hw : μ p-τ p∈closedBall (0 : ℂ) (r/8) := by simpa only [mem_closedBall,dist_zero_right] using harg.le
    have hPb : ‖P p‖≤T := (hεnear (ball_subset_ball hde hp)).2.le
    change ‖P p*Q (μ p-τ p,p)‖≤_
    rw [norm_mul]
    apply (mul_le_mul hPb (hQb p hp _ hw) (norm_nonneg _) hT.le).trans_eq
    dsimp only [C]
    field_simp
    ring
  · intro pR hpR
    let p := J pR
    have hp : p∈U := hpR.2
    obtain ⟨hmu,hMid,hSq⟩ := hdreal pR hpR.1.1.2
    change μ p=(hillDirichletEnergy pR.val pR.property.1 pR.property.2 k hk : ℂ) at hmu
    change τ p=(hillRealGapCenter pR.val pR.property.1 pR.property.2 k : ℂ) at hMid
    have hμK : μ p∈closedBall c r := by
      have hd := hdata p (ball_subset_ball hdd hp)
      rw [mem_closedBall,dist_eq_norm]
      exact (norm_sub_le_norm_sub_add_norm_sub (μ p) (τ p) c).trans (by linarith [hd.1,hd.2.2.1])
    have hμphysical : (hillDirichletEnergy pR.val pR.property.1 pR.property.2 k hk : ℂ)∈closedBall c r := by
      rw [←hmu]
      exact hμK
    have hβeq : β p=I*hillDirichletSheetRoot p (hillDirichletEnergy pR.val pR.property.1 pR.property.2 k hk)/
        hillDeflatedEnergyCanonicalRoot pR.val pR.property.1 pR.property.2 k (hillDirichletEnergy pR.val pR.property.1 pR.property.2 k hk)*
          Q ((hillDirichletEnergy pR.val pR.property.1 pR.property.2 k hk : ℂ)-
            (hillRealGapCenter pR.val pR.property.1 pR.property.2 k : ℂ),p) := by
      dsimp only [β,P]
      rw [hmu,hMid,(hrootmatch pR hpR.1.2 _ (hball _ hμphysical).2).2.2]
    have hτ : ‖(hillRealGapCenter pR.val pR.property.1 pR.property.2 k : ℂ)-c‖<r/32 := by
      have ht := (hdata p (ball_subset_ball hdd hp)).1
      change ‖τ p-c‖<r/32 at ht
      rwa [hMid] at ht
    have hsphysical : s p=(hillRealGapHalfLength pR.val pR.property.1 pR.property.2 k : ℂ)^2 := by
      dsimp only [s]
      rw [hSq]
      ring
    have hgapbound : ‖(hillRealGapHalfLength pR.val pR.property.1 pR.property.2 k : ℂ)‖<r/64 := by
      have hh := (hdata p (ball_subset_ball hdd hp)).2.1
      change ‖s p‖<(r/64)^2 at hh
      rw [hsphysical,norm_pow] at hh
      nlinarith [norm_nonneg (hillRealGapHalfLength pR.val pR.property.1 pR.property.2 k : ℂ)]
    have hpoint (w : ℂ) (hw : w∈ball (0:ℂ) (r/4)) :
        (hillRealGapCenter pR.val pR.property.1 pR.property.2 k : ℂ)+w∈closedBall c r := by
      have hw' : ‖w‖<r/4 := by simpa only [mem_ball,dist_zero_right] using hw
      rw [mem_closedBall,dist_eq_norm]
      have hh : ‖(hillRealGapCenter pR.val pR.property.1 pR.property.2 k : ℂ)+w-c‖≤
          ‖(hillRealGapCenter pR.val pR.property.1 pR.property.2 k : ℂ)-c‖+‖w‖ := by
        rw [show (hillRealGapCenter pR.val pR.property.1 pR.property.2 k : ℂ)+w-c=
          ((hillRealGapCenter pR.val pR.property.1 pR.property.2 k : ℂ)-c)+w by ring]
        exact norm_add_le _ _
      linarith
    have hcos (θ : ℝ) (_hθ : θ∈Icc (0:ℝ) Real.pi) :
        cosineGapPoint (hillRealGapCenter pR.val pR.property.1 pR.property.2 k)
          (hillRealGapHalfLength pR.val pR.property.1 pR.property.2 k) (θ : ℂ)∈closedBall c r := by
      have hc : ‖(Real.cos θ : ℂ)‖≤1 := by simpa only [norm_real,Real.norm_eq_abs] using Real.abs_cos_le_one θ
      rw [cosineGapPoint,← ofReal_cos,mem_closedBall,dist_eq_norm]
      have hh : ‖(hillRealGapCenter pR.val pR.property.1 pR.property.2 k : ℂ)+
          (hillRealGapHalfLength pR.val pR.property.1 pR.property.2 k : ℂ)*(Real.cos θ : ℂ)-c‖≤
          ‖(hillRealGapCenter pR.val pR.property.1 pR.property.2 k : ℂ)-c‖+
            ‖(hillRealGapHalfLength pR.val pR.property.1 pR.property.2 k : ℂ)‖ := by
        rw [show (hillRealGapCenter pR.val pR.property.1 pR.property.2 k : ℂ)+
          (hillRealGapHalfLength pR.val pR.property.1 pR.property.2 k : ℂ)*(Real.cos θ : ℂ)-c=
          ((hillRealGapCenter pR.val pR.property.1 pR.property.2 k : ℂ)-c)+
            (hillRealGapHalfLength pR.val pR.property.1 pR.property.2 k : ℂ)*(Real.cos θ : ℂ) by ring]
        apply (norm_add_le _ _).trans
        rw [norm_mul]
        exact add_le_add le_rfl (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hc (norm_nonneg _))
      linarith
    have hQphysical : AnalyticOnNhd ℂ (fun w => Q (w,p)) (ball (0:ℂ) (r/4)) := by
      intro w hw
      exact (hQa (w,p) ⟨hw,hp⟩).comp (f := fun z : ℂ => (z,p)) (analyticAt_id.prod analyticAt_const)
    have hODEphysical (w : ℂ) (hw : w∈ball (0:ℂ) (r/4)) :
        (w^2-(hillRealGapHalfLength pR.val pR.property.1 pR.property.2 k : ℂ)^2)*deriv (fun z => Q (z,p)) w+w*Q (w,p)=
          -I*hillAbelianSelectedGlobalPsi pR.val pR.property.1 pR.property.2 n hn
              ((hillRealGapCenter pR.val pR.property.1 pR.property.2 k : ℂ)+w)/
            hillDeflatedEnergyCanonicalRoot pR.val pR.property.1 pR.property.2 k
              ((hillRealGapCenter pR.val pR.property.1 pR.property.2 k : ℂ)+w)-(if k=n then 1 else 0) := by
      have hh := hODE p hp w hw
      rw [hsphysical] at hh
      exact hh.trans (centeredMeanFree_deflated_chart_eq_physical q hq hr H n k hn hk pR (closedBall c r)
        hMid hSq hcos (fun z hz => (hHreal pR hpR.1.1.1 z (hball z hz).1).2) w (hpoint w hw))
    by_cases hgap : hillRealGapHalfLength pR.val pR.property.1 pR.property.2 k=0
    · rw [hβeq,hillDirichletSheetRoot_eq_zero_of_halfLength_zero pR.val pR.property.1 pR.property.2 k hk hgap,
        mul_zero,zero_div,zero_mul,hillRegularAbelianCorrection_closed pR.val pR.property.1 pR.property.2 n hn k hk hgap]
    · let θ := hillDirichletSelectedRealAngle pR.val pR.property.1 pR.property.2 k hk hgap
      have hspec := hillDirichletSelectedRealAngle_spec pR.val pR.property.1 pR.property.2 k hk hgap
      have hh := hillRegularAbelian_terminal_eq_quadratic pR.val pR.property.1 pR.property.2 n k hn hk hgap
        (fun w => Q (w,p)) (r/4) (by linarith) hQphysical hODEphysical θ hspec.2.1 hspec.2.2
      rw [hβeq,hillRegularAbelianCorrection,dif_neg hgap,hillRegularAbelianPrimitive]
      exact hh

end NLS.KdV
