import NLS.KdV.HillFixedGapNumeratorBounds
import NLS.KdV.HillFixedGapFilledRootChart
import NLS.KdV.HillFixedGapCenteredDirichletData
import NLS.KdV.HillCenteredMeanFreePhysicalMatching
import NLS.KdV.HillClosedGapAbelianCorrections

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

include h0q h0r in
/-- For each fixed gap, the actual regular Abelian correction has one
bounded analytic source chart before every differential index. -/
theorem exists_hillFixedGap_regularAbelianCorrection_uniform_charts (k : ℕ) (hk : 1≤k) :
    ∃ δ C : ℝ, 0<δ ∧ 0<C ∧ ∀ n : ℕ, ∀ hn : 1≤n,
      ∃ β : Coeff 2 → ℂ, AnalyticOnNhd ℂ β (ball 0 δ) ∧
        (∀ p∈ball 0 δ, ‖β p‖≤C) ∧
        ∀ q : RealPeriodOneHillPotential, ‖q.val‖<δ →
          β (SpectralWeight.one.toCoeff q.val)=
            hillRegularAbelianCorrection q.val q.property.1 q.property.2 n hn k hk := by
  obtain ⟨δg,Bg,hδg,hBg,hcharts⟩ := exists_hillSelectedPsi_uniform_fixed_gap_disc_bound h0q h0r k hk
  obtain ⟨r,δr,Cr,hr,hδr,hCr,hrR,hra,hrb,hrreal⟩ := exists_hillFixedGap_filled_root_local_chart h0q h0r k hk
  obtain ⟨δd,μ,hδd,hμa,hτa,hsa,hdata,hdreal⟩ := exists_hillFixedGap_centered_Dirichlet_data h0q h0r k hk r hr
  let c : ℂ := hillRealGapCenter 0 h0q h0r k
  let R := hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k
  let τ := hillLocalGapMidpoint 0 h0q h0r k
  let s : Coeff 2 → ℂ := fun p => hillLocalGapSquare 0 h0q h0r k p/4
  let δ0 := min δg (min δr δd)
  have hδ0 : 0<δ0 := lt_min hδg (lt_min hδr hδd)
  have h0g : δ0≤δg := min_le_left _ _
  have hδ0r : δ0≤δr := (min_le_right _ _).trans (min_le_left _ _)
  have h0d : δ0≤δd := (min_le_right _ _).trans (min_le_right _ _)
  have hμK (p : Coeff 2) (hp : p∈ball 0 δ0) : μ p∈closedBall c r := by
    have hd := hdata p (ball_subset_ball h0d hp)
    rw [mem_closedBall,dist_eq_norm]
    exact (norm_sub_le_norm_sub_add_norm_sub (μ p) (τ p) c).trans (by linarith [hd.1,hd.2.2.1])
  let P : Coeff 2 → ℂ := fun p => I*hillDirichletSheetRoot p (μ p)/hillFilledFreeGapRoot h0q h0r k (μ p,p)
  have hPa : AnalyticOnNhd ℂ P (ball 0 δ0) := by
    intro p hp
    have hm := hμa p (ball_subset_ball h0d hp)
    have hpair := hm.prod analyticAt_id
    have hroot := (hra (μ p,p) ⟨hμK p hp,ball_subset_ball hδ0r hp⟩).comp
      (f := fun p : Coeff 2 => (μ p,p)) hpair
    have hsheet := (analyticOnNhd_hillDirichletSheetRoot_joint (μ p,p) (mem_univ _)).comp
      (f := fun p : Coeff 2 => (μ p,p)) hpair
    exact (analyticAt_const.mul hsheet).div hroot (hrb p (ball_subset_ball hδ0r hp) (μ p) (hμK p hp)).1
  let T := ‖P 0‖+1
  have hT : 0<T := by dsimp only [T];positivity
  have hPsmall : {p : Coeff 2 | ‖P p‖<T}∈𝓝 (0 : Coeff 2) :=
    ((hPa 0 (mem_ball_self hδ0)).continuousAt.norm.tendsto).eventually
      (isOpen_Iio.mem_nhds (by change ‖P 0‖<‖P 0‖+1;linarith))
  obtain ⟨ε,hε,hεP⟩ := Metric.mem_nhds_iff.mp hPsmall
  let δ := min δ0 ε
  have hδ : 0<δ := lt_min hδ0 hε
  have hd0 : δ≤δ0 := min_le_left _ _
  have hdg : δ≤δg := hd0.trans h0g
  have hdr : δ≤δr := hd0.trans hδ0r
  have hdd : δ≤δd := hd0.trans h0d
  let B := Bg*Cr
  let C := T*(64*Real.pi*B/r)
  have hB : 0<B := mul_pos hBg hCr
  have hC : 0<C := by dsimp only [C];positivity
  refine ⟨δ,C,hδ,hC,?_⟩
  intro n hn
  obtain ⟨G,hGa,hGb,hGreal⟩ := hcharts n hn
  let U : Set (Coeff 2) := ball 0 δ
  let f := hillCenteredComplexRegularGapNumerator h0q h0r G k
  have hpos (w : ℂ) (hw : w∈closedBall (0:ℂ) (r/2)) (p : Coeff 2) (hp : p∈U) :
      τ p+w∈closedBall c r := by
    have ht := (hdata p (ball_subset_ball hdd hp)).1
    have hw' : ‖w‖≤r/2 := by simpa only [mem_closedBall,dist_zero_right] using hw
    rw [mem_closedBall,dist_eq_norm]
    have hh : ‖τ p+w-c‖≤‖τ p-c‖+‖w‖ := by
      rw [show τ p+w-c=(τ p-c)+w by ring]
      exact norm_add_le _ _
    linarith
  have hg : AnalyticOnNhd ℂ (hillComplexRegularGapNumerator h0q h0r G k) (closedBall c r ×ˢ U) := by
    intro t ht
    exact (analyticAt_const.mul (hGa t ⟨mem_univ _,ball_subset_ball hdg ht.2⟩)).div
      (hra t ⟨ht.1,ball_subset_ball hdr ht.2⟩) (hrb t.2 (ball_subset_ball hdr ht.2) t.1 ht.1).1
  have hf : AnalyticOnNhd ℂ f (closedBall (0:ℂ) (r/2) ×ˢ U) := by
    intro t ht
    have hm := (hτa t.2 (ball_subset_ball hdd ht.2)).comp (f := fun u : ℂ × Coeff 2 => u.2) analyticAt_snd
    exact (hg (τ t.2+t.1,t.2) ⟨hpos t.1 ht.1 t.2 ht.2,ht.2⟩).comp
      (f := fun u : ℂ × Coeff 2 => (τ u.2+u.1,u.2)) ((hm.add analyticAt_fst).prod analyticAt_snd)
  have hb (p : Coeff 2) (hp : p∈U) (w : ℂ) (hw : w∈closedBall (0:ℂ) (r/2)) : ‖f (w,p)‖≤B := by
    have hz := hpos w hw p hp
    have hR : 0<R := add_pos_of_nonneg_of_pos (hillRealGapContour_geometry 0 h0q h0r k hk).1
      (hillRealGapContour_geometry 0 h0q h0r k hk).2.1
    have hzR : τ p+w∈closedBall c R := closedBall_subset_closedBall (by linarith : r≤R) hz
    change ‖-I*G (τ p+w,p)/hillFilledFreeGapRoot h0q h0r k (τ p+w,p)‖≤Bg*Cr
    rw [div_eq_mul_inv,norm_mul,norm_mul,norm_neg,norm_I,one_mul]
    exact mul_le_mul (hGb p (ball_subset_ball hdg hp) _ hzR)
      (hrb p (ball_subset_ball hdr hp) _ hz).2 (norm_nonneg _) hBg.le
  have hs : AnalyticOnNhd ℂ s U := hsa.mono (ball_subset_ball hdd)
  have hsmall (p : Coeff 2) (hp : p∈U) : ‖s p‖<((r/2)/8)^2 := by
    have hh := (hdata p (ball_subset_ball hdd hp)).2.1
    nlinarith
  obtain ⟨Q,hQa,hODE,hQb⟩ := exists_bounded_analytic_centered_mean_free_quadratic_solution f s U isOpen_ball
    (r/2) B (by positivity) hB.le hf hs hsmall hb
  have hr2 : (r/2)/2=r/4 := by ring
  have hr4 : (r/2)/4=r/8 := by ring
  rw [hr2] at hQa hODE
  rw [hr4] at hQb
  let β : Coeff 2 → ℂ := fun p => P p*Q (μ p-τ p,p)
  refine ⟨β,?_,?_,?_⟩
  · intro p hp
    have harg := (hdata p (ball_subset_ball hdd hp)).2.2.1
    have hw : μ p-τ p∈ball (0:ℂ) (r/4) := by
      rw [mem_ball,dist_zero_right]
      exact harg.trans (by linarith)
    have hm := hμa p (ball_subset_ball hdd hp)
    have ht := hτa p (ball_subset_ball hdd hp)
    exact (hPa p (ball_subset_ball hd0 hp)).mul ((hQa (μ p-τ p,p) ⟨hw,hp⟩).comp
      (f := fun p : Coeff 2 => (μ p-τ p,p)) ((hm.sub ht).prod analyticAt_id))
  · intro p hp
    have harg := (hdata p (ball_subset_ball hdd hp)).2.2.1
    have hw : μ p-τ p∈closedBall (0:ℂ) (r/8) := by
      simpa only [mem_closedBall,dist_zero_right] using harg.le
    have hPb : ‖P p‖≤T := (hεP (ball_subset_ball (min_le_right _ _) hp)).le
    change ‖P p*Q (μ p-τ p,p)‖≤C
    rw [norm_mul]
    apply (mul_le_mul hPb (hQb p hp _ hw) (norm_nonneg _) hT.le).trans_eq
    change T*(32*Real.pi*B/(r/2))=T*(64*Real.pi*B/r)
    congr 1
    field_simp
    ring
  · intro q hq
    let p := SpectralWeight.one.toCoeff q.val
    have hp : p∈U := by
      rw [mem_ball,dist_zero_right]
      exact (SpectralWeight.one.norm_toCoeff_le q.val).trans_lt hq
    obtain ⟨hmu,hMid,hSq⟩ := hdreal q (hq.trans_le hdd)
    change μ p=(hillDirichletEnergy q.val q.property.1 q.property.2 k hk : ℂ) at hmu
    change τ p=(hillRealGapCenter q.val q.property.1 q.property.2 k : ℂ) at hMid
    have hroot := hrreal q (hq.trans_le hdr)
    have hμphysical : (hillDirichletEnergy q.val q.property.1 q.property.2 k hk : ℂ)∈closedBall c r := by
      rw [←hmu]
      exact hμK p (ball_subset_ball hd0 hp)
    have hβeq : β p=I*hillDirichletSheetRoot p (hillDirichletEnergy q.val q.property.1 q.property.2 k hk)/
        hillDeflatedEnergyCanonicalRoot q.val q.property.1 q.property.2 k (hillDirichletEnergy q.val q.property.1 q.property.2 k hk)*
          Q ((hillDirichletEnergy q.val q.property.1 q.property.2 k hk : ℂ)-
            (hillRealGapCenter q.val q.property.1 q.property.2 k : ℂ),p) := by
      dsimp only [β,P]
      rw [hmu,hMid,hroot _ hμphysical]
    have hτ : ‖(hillRealGapCenter q.val q.property.1 q.property.2 k : ℂ)-c‖<r/32 := by
      have ht := (hdata p (ball_subset_ball hdd hp)).1
      change ‖τ p-c‖<r/32 at ht
      rwa [hMid] at ht
    have hsphysical : s p=(hillRealGapHalfLength q.val q.property.1 q.property.2 k : ℂ)^2 := by
      dsimp only [s]
      rw [hSq]
      ring
    have hgapbound : ‖(hillRealGapHalfLength q.val q.property.1 q.property.2 k : ℂ)‖<r/64 := by
      have hh := (hdata p (ball_subset_ball hdd hp)).2.1
      change ‖s p‖<(r/64)^2 at hh
      rw [hsphysical,norm_pow] at hh
      nlinarith [norm_nonneg (hillRealGapHalfLength q.val q.property.1 q.property.2 k : ℂ)]
    have hpoint (w : ℂ) (hw : w∈ball (0:ℂ) (r/4)) :
        (hillRealGapCenter q.val q.property.1 q.property.2 k : ℂ)+w∈closedBall c r := by
      have hw' : ‖w‖<r/4 := by simpa only [mem_ball,dist_zero_right] using hw
      rw [mem_closedBall,dist_eq_norm]
      have hh : ‖(hillRealGapCenter q.val q.property.1 q.property.2 k : ℂ)+w-c‖≤
          ‖(hillRealGapCenter q.val q.property.1 q.property.2 k : ℂ)-c‖+‖w‖ := by
        rw [show (hillRealGapCenter q.val q.property.1 q.property.2 k : ℂ)+w-c=
          ((hillRealGapCenter q.val q.property.1 q.property.2 k : ℂ)-c)+w by ring]
        exact norm_add_le _ _
      linarith
    have hcos (θ : ℝ) (_hθ : θ∈Icc (0:ℝ) Real.pi) :
        cosineGapPoint (hillRealGapCenter q.val q.property.1 q.property.2 k)
          (hillRealGapHalfLength q.val q.property.1 q.property.2 k) (θ : ℂ)∈closedBall c r := by
      have hc : ‖(Real.cos θ : ℂ)‖≤1 := by simpa only [norm_real,Real.norm_eq_abs] using Real.abs_cos_le_one θ
      rw [cosineGapPoint,← ofReal_cos,mem_closedBall,dist_eq_norm]
      have hh : ‖(hillRealGapCenter q.val q.property.1 q.property.2 k : ℂ)+
          (hillRealGapHalfLength q.val q.property.1 q.property.2 k : ℂ)*(Real.cos θ : ℂ)-c‖≤
          ‖(hillRealGapCenter q.val q.property.1 q.property.2 k : ℂ)-c‖+
            ‖(hillRealGapHalfLength q.val q.property.1 q.property.2 k : ℂ)‖ := by
        rw [show (hillRealGapCenter q.val q.property.1 q.property.2 k : ℂ)+
          (hillRealGapHalfLength q.val q.property.1 q.property.2 k : ℂ)*(Real.cos θ : ℂ)-c=
          ((hillRealGapCenter q.val q.property.1 q.property.2 k : ℂ)-c)+
            (hillRealGapHalfLength q.val q.property.1 q.property.2 k : ℂ)*(Real.cos θ : ℂ) by ring]
        apply (norm_add_le _ _).trans
        rw [norm_mul]
        exact add_le_add le_rfl (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hc (norm_nonneg _))
      linarith
    have hQphysical : AnalyticOnNhd ℂ (fun w => Q (w,p)) (ball (0:ℂ) (r/4)) := by
      intro w hw
      exact (hQa (w,p) ⟨hw,hp⟩).comp (f := fun z : ℂ => (z,p)) (analyticAt_id.prod analyticAt_const)
    have hODEphysical (w : ℂ) (hw : w∈ball (0:ℂ) (r/4)) :
        (w^2-(hillRealGapHalfLength q.val q.property.1 q.property.2 k : ℂ)^2)*deriv (fun z => Q (z,p)) w+w*Q (w,p)=
          -I*hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 n hn
              ((hillRealGapCenter q.val q.property.1 q.property.2 k : ℂ)+w)/
            hillDeflatedEnergyCanonicalRoot q.val q.property.1 q.property.2 k
              ((hillRealGapCenter q.val q.property.1 q.property.2 k : ℂ)+w)-(if k=n then 1 else 0) := by
      have hh := hODE p hp w hw
      rw [hsphysical] at hh
      exact hh.trans (centeredMeanFree_hillCenteredComplexRegularGapNumerator_eq_physical h0q h0r
        G n k hn hk q (closedBall c r) (hGreal q (hq.trans_le hdg)) hroot hMid hSq hcos w (hpoint w hw))
    by_cases hgap : hillRealGapHalfLength q.val q.property.1 q.property.2 k=0
    · rw [hβeq,hillDirichletSheetRoot_eq_zero_of_halfLength_zero q.val q.property.1 q.property.2 k hk hgap,
        mul_zero,zero_div,zero_mul,hillRegularAbelianCorrection_closed q.val q.property.1 q.property.2 n hn k hk hgap]
    · let θ := hillDirichletSelectedRealAngle q.val q.property.1 q.property.2 k hk hgap
      have hspec := hillDirichletSelectedRealAngle_spec q.val q.property.1 q.property.2 k hk hgap
      have hh := hillRegularAbelian_terminal_eq_quadratic q.val q.property.1 q.property.2 n k hn hk hgap
        (fun w => Q (w,p)) (r/4) (by linarith) hQphysical hODEphysical θ hspec.2.1 hspec.2.2
      rw [hβeq,hillRegularAbelianCorrection,dif_neg hgap,hillRegularAbelianPrimitive]
      exact hh

end NLS.KdV
