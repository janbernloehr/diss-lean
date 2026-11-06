import NLS.KdV.HillCenteredQuadraticDirichletValue
import NLS.KdV.HillCenteredMeanFreePhysicalMatching
import NLS.KdV.HillUniformNativeDirichletTerminal
import NLS.KdV.HillClosedGapAbelianCorrections
import NLS.KdV.HillFilledFreeGapPhysical
import NLS.KdV.HillUniformDirichletPhysical
import NLS.KdV.HillUniformRealGapLocalization
import NLS.KdV.HillLocallyUniformActionTails

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
/-- Actual own-gap regular corrections have one common complex analytic
chart and an O(1/n) bound on every native weighted source ball near zero. -/
theorem exists_hillOwnRegularAbelianCorrection_uniform_native_charts :
    ∃ δ M : ℝ, ∃ N : ℕ, 0<δ ∧ 0<M ∧ ∃ hN : 1≤N,
      ∀ n : ℕ, ∀ hn : N≤n, ∃ β : Coeff 2 → ℂ,
        AnalyticOnNhd ℂ β (ball 0 δ) ∧
        (∀ w : SpectralWeight, ∀ q : WeightedCoeff w.doubleIndex.toWeight 2, ‖q‖<δ →
          ‖β (hillPeriodOneCoefficientMap w q)‖≤M/(n : ℝ)) ∧
        ∀ q : RealPeriodOneHillPotential, ‖q.val‖<δ →
          β (SpectralWeight.one.toCoeff q.val)=
            hillRegularAbelianCorrection q.val q.property.1 q.property.2 n (hN.trans hn) n (hN.trans hn) := by
  obtain ⟨δ,B,Np,hδ,hB,hNp,hprimitives⟩ := exists_hillSelectedPsi_uniform_centered_mean_free_primitives h0q h0r
  obtain ⟨T,Nt,hT,_,hterminal⟩ := exists_hillNativeComplexDirichletGapTerminal_uniform_bound h0q h0r δ hδ.le
  obtain ⟨Nv,_,hvalue⟩ := exists_hillCenteredQuadraticDirichletValue_uniform_pointwise_bound h0q h0r δ
  obtain ⟨Nr,_,hrootmatch⟩ := exists_hillFilledFreeGapRoot_bounded_real_physical_matching h0q h0r δ
  obtain ⟨Ny,_,hsymmetric⟩ := exists_hillFreeGap_bounded_real_symmetric_data_matching h0q h0r δ
  obtain ⟨Nl,_,hlocal⟩ := exists_hillFreeGap_bounded_real_midpoint_halfgap_localization h0q h0r (1/32) (by norm_num) (by norm_num) δ
  obtain ⟨Nm,_,hmumatch⟩ := exists_hillScaledDirichletRoot_bounded_real_physical_matching h0q h0r (1/16) (by norm_num) (by norm_num) δ
  obtain ⟨Nd,_,hmuchart⟩ := exists_hillScaledDirichletRoot_bounded_complex_analytic_chart h0q h0r (1/16) (by norm_num) (by norm_num) δ
  let N := Np+Nt+Nv+Nr+Ny+Nl+Nm+Nd+1
  let M := 256*Real.pi*B*T/Real.pi^2
  have hN : 1≤N := by dsimp only [N];omega
  refine ⟨δ,M,N,hδ,by dsimp only [M];positivity,hN,?_⟩
  intro n hn
  have hn1 : 1≤n := hN.trans hn
  have hnP : Np≤n := by dsimp only [N] at hn;omega
  have hnT : Nt≤n := by dsimp only [N] at hn;omega
  have hnV : Nv≤n := by dsimp only [N] at hn;omega
  have hnR : Nr≤n := by dsimp only [N] at hn;omega
  have hnY : Ny≤n := by dsimp only [N] at hn;omega
  have hnL : Nl≤n := by dsimp only [N] at hn;omega
  have hnM : Nm≤n := by dsimp only [N] at hn;omega
  have hnD : Nd≤n := by dsimp only [N] at hn;omega
  obtain ⟨G,_,hsol,hreal⟩ := hprimitives n hn1
  obtain ⟨Q,hQa,hODE,hQb⟩ := hsol n hnP
  let R := hillRealGapHalfLength 0 h0q h0r n+hillRealGapCollar 0 h0q h0r n
  let c : ℂ := hillRealGapCenter 0 h0q h0r n
  have hR : 0<R := add_pos_of_nonneg_of_pos (hillRealGapContour_geometry 0 h0q h0r n hn1).1
    (hillRealGapContour_geometry 0 h0q h0r n hn1).2.1
  have hnpos : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hnreal : (1:ℝ)≤n := by exact_mod_cast hn1
  have hRlow : Real.pi^2*(n : ℝ)/4≤R := by
    dsimp only [R]
    rw [hillFreeGapHalfLength h0q h0r n hn1,zero_add,hillFreeGapCollar h0q h0r n hn1]
    nlinarith [sq_pos_of_pos Real.pi_pos]
  let β := hillCenteredQuadraticDirichletValue h0q h0r Q n
  have hval := hvalue (ball 0 δ) Subset.rfl n hnV Q hQa (64*Real.pi*B/R) hQb
  refine ⟨β,hval.1,?_,?_⟩
  · intro w q hq
    have hp : hillPeriodOneCoefficientMap w q∈ball 0 δ := by
      rw [mem_ball,dist_zero_right]
      exact (norm_hillPeriodOneCoefficientMap_le w q).trans_lt hq
    have ht := hterminal w q hq.le n hnT
    change ‖hillComplexDirichletGapTerminal h0q h0r n (hillPeriodOneCoefficientMap w q)‖≤T at ht
    apply ((hval.2 _ hp).trans (mul_le_mul_of_nonneg_right ht (by positivity : 0≤64*Real.pi*B/R))).trans
    calc
      T*(64*Real.pi*B/R) ≤ T*(64*Real.pi*B/(Real.pi^2*(n : ℝ)/4)) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left (by positivity) (by positivity) hRlow) hT.le
      _ = M/(n : ℝ) := by dsimp only [M];field_simp;ring
  · intro q hq
    let p := SpectralWeight.one.toCoeff q.val
    have hp : p∈ball 0 δ := by
      rw [mem_ball,dist_zero_right]
      exact (SpectralWeight.one.norm_toCoeff_le q.val).trans_lt hq
    have hpδ : ‖p‖≤δ := (SpectralWeight.one.norm_toCoeff_le q.val).trans hq.le
    have hmu := hmumatch q.val q.property.1 q.property.2 hpδ n hnM
    change hillScaledDirichletRoot h0q h0r (1/16) n p=
      (hillDirichletEnergy q.val q.property.1 q.property.2 n hn1 : ℂ) at hmu
    obtain ⟨hMid,hSq⟩ := hsymmetric q.val q.property.1 q.property.2 hpδ n hnY
    obtain ⟨hτ,hgapbound⟩ := hlocal q.val q.property.1 q.property.2 hpδ n hnL
    have hμK : (hillDirichletEnergy q.val q.property.1 q.property.2 n hn1 : ℂ)∈closedBall c R := by
      have hh := closedBall_subset_closedBall (by linarith : (1/16)*R≤R)
        (ball_subset_closedBall (((hmuchart n hnD).2 p hpδ).1))
      simpa only [hmu] using hh
    have hroot := hrootmatch q.val q.property.1 q.property.2 hpδ n hnR
    have hβeq : β p=I*hillDirichletSheetRoot p (hillDirichletEnergy q.val q.property.1 q.property.2 n hn1)/
        hillDeflatedEnergyCanonicalRoot q.val q.property.1 q.property.2 n (hillDirichletEnergy q.val q.property.1 q.property.2 n hn1)*
          Q ((hillDirichletEnergy q.val q.property.1 q.property.2 n hn1 : ℂ)-
            (hillRealGapCenter q.val q.property.1 q.property.2 n : ℂ),p) := by
      dsimp only [β,hillCenteredQuadraticDirichletValue,hillComplexDirichletGapTerminal]
      rw [hmu,hMid,hroot _ hμK]
      ring
    have hpoint (w : ℂ) (hw : w∈ball (0:ℂ) (R/4)) :
        (hillRealGapCenter q.val q.property.1 q.property.2 n : ℂ)+w∈closedBall c R := by
      have hw' : ‖w‖<R/4 := by simpa only [mem_ball,dist_zero_right] using hw
      rw [mem_closedBall,dist_eq_norm]
      have hh : ‖(hillRealGapCenter q.val q.property.1 q.property.2 n : ℂ)+w-c‖≤
          ‖(hillRealGapCenter q.val q.property.1 q.property.2 n : ℂ)-c‖+‖w‖ := by
        rw [show (hillRealGapCenter q.val q.property.1 q.property.2 n : ℂ)+w-c=
          ((hillRealGapCenter q.val q.property.1 q.property.2 n : ℂ)-c)+w by ring]
        exact norm_add_le _ _
      linarith
    have hcos (θ : ℝ) (_hθ : θ∈Icc (0:ℝ) Real.pi) :
        cosineGapPoint (hillRealGapCenter q.val q.property.1 q.property.2 n)
          (hillRealGapHalfLength q.val q.property.1 q.property.2 n) (θ : ℂ)∈closedBall c R := by
      have hc : ‖(Real.cos θ : ℂ)‖≤1 := by simpa only [norm_real,Real.norm_eq_abs] using Real.abs_cos_le_one θ
      rw [cosineGapPoint,← ofReal_cos,mem_closedBall,dist_eq_norm]
      have hh : ‖(hillRealGapCenter q.val q.property.1 q.property.2 n : ℂ)+
          (hillRealGapHalfLength q.val q.property.1 q.property.2 n : ℂ)*(Real.cos θ : ℂ)-c‖≤
          ‖(hillRealGapCenter q.val q.property.1 q.property.2 n : ℂ)-c‖+
            ‖(hillRealGapHalfLength q.val q.property.1 q.property.2 n : ℂ)‖ := by
        rw [show (hillRealGapCenter q.val q.property.1 q.property.2 n : ℂ)+
          (hillRealGapHalfLength q.val q.property.1 q.property.2 n : ℂ)*(Real.cos θ : ℂ)-c=
          ((hillRealGapCenter q.val q.property.1 q.property.2 n : ℂ)-c)+
            (hillRealGapHalfLength q.val q.property.1 q.property.2 n : ℂ)*(Real.cos θ : ℂ) by ring]
        apply (norm_add_le _ _).trans
        rw [norm_mul]
        exact add_le_add le_rfl (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hc (norm_nonneg _))
      linarith
    have hs : hillLocalGapSquare 0 h0q h0r n p/4=(hillRealGapHalfLength q.val q.property.1 q.property.2 n : ℂ)^2 := by
      rw [hSq]
      ring
    have hQphysical : AnalyticOnNhd ℂ (fun w => Q (w,p)) (ball (0:ℂ) (R/4)) := by
      intro w hw
      exact (hQa (w,p) ⟨hw,hp⟩).comp (f := fun z : ℂ => (z,p)) (analyticAt_id.prod analyticAt_const)
    have hODEphysical (w : ℂ) (hw : w∈ball (0:ℂ) (R/4)) :
        (w^2-(hillRealGapHalfLength q.val q.property.1 q.property.2 n : ℂ)^2)*deriv (fun z => Q (z,p)) w+w*Q (w,p)=
          -I*hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 n hn1
              ((hillRealGapCenter q.val q.property.1 q.property.2 n : ℂ)+w)/
            hillDeflatedEnergyCanonicalRoot q.val q.property.1 q.property.2 n
              ((hillRealGapCenter q.val q.property.1 q.property.2 n : ℂ)+w)-(if n=n then 1 else 0) := by
      have hh := hODE p hp w hw
      rw [hs] at hh
      exact hh.trans (centeredMeanFree_hillCenteredComplexRegularGapNumerator_eq_physical h0q h0r
        G n n hn1 hn1 q (closedBall c R) (hreal q hq) hroot hMid hSq hcos w (hpoint w hw))
    by_cases hgap : hillRealGapHalfLength q.val q.property.1 q.property.2 n=0
    · rw [hβeq,hillDirichletSheetRoot_eq_zero_of_halfLength_zero q.val q.property.1 q.property.2 n hn1 hgap,
        mul_zero,zero_div,zero_mul,hillRegularAbelianCorrection_closed q.val q.property.1 q.property.2 n hn1 n hn1 hgap]
    · let θ := hillDirichletSelectedRealAngle q.val q.property.1 q.property.2 n hn1 hgap
      have hspec := hillDirichletSelectedRealAngle_spec q.val q.property.1 q.property.2 n hn1 hgap
      have hh := hillRegularAbelian_terminal_eq_quadratic q.val q.property.1 q.property.2 n n hn1 hn1 hgap
        (fun w => Q (w,p)) (R/4) (by linarith) hQphysical hODEphysical θ hspec.2.1 hspec.2.2
      rw [hβeq,hillRegularAbelianCorrection,dif_neg hgap,hillRegularAbelianPrimitive]
      exact hh

include h0q h0r in
/-- The original own regular phase multiplier is analytic and uniformly
bounded on one common native weighted source ball, before the gap index
and the spectral weight. -/
theorem exists_hillOwnRegularPhaseMultiplier_uniform_native_analytic :
    ∃ δ M : ℝ, ∃ N : ℕ, 0<δ ∧ 0<M ∧ ∃ hN : 1≤N,
      ∀ n : ℕ, ∀ hn : N≤n, ∀ w : SpectralWeight,
      ∃ F : WeightedCoeff w.doubleIndex.toWeight 2 → ℂ,
        AnalyticOnNhd ℂ F (ball 0 δ) ∧
        (∀ q∈ball 0 δ, ‖F q‖≤Real.exp M) ∧
        ∀ q : RealHillWeightedPotential w, ‖q.val‖<δ →
          F q.val=Complex.exp (I*hillRegularAbelianCorrection (hillPeriodOneUnitPotential w q.val)
            (hillPeriodOneUnitPotential_even w q.val) (hillPeriodOneUnitPotential_real w q.val q.property)
            n (hN.trans hn) n (hN.trans hn)) := by
  obtain ⟨δ,M,N,hδ,hM,hN,hcharts⟩ := exists_hillOwnRegularAbelianCorrection_uniform_native_charts h0q h0r
  refine ⟨δ,M,N,hδ,hM,hN,?_⟩
  intro n hn w
  obtain ⟨β,hβa,hβb,hphysical⟩ := hcharts n hn
  let F : WeightedCoeff w.doubleIndex.toWeight 2 → ℂ := fun q =>
    Complex.exp (I*β (hillPeriodOneCoefficientMap w q))
  refine ⟨F,?_,?_,?_⟩
  · intro q hq
    have hp : hillPeriodOneCoefficientMap w q∈ball 0 δ := by
      rw [mem_ball,dist_zero_right]
      exact (norm_hillPeriodOneCoefficientMap_le w q).trans_lt
        (show ‖q‖<δ by simpa only [mem_ball,dist_zero_right] using hq)
    have hh := (hβa _ hp).comp ((hillPeriodOneCoefficientMap w).analyticAt q)
    exact (analyticAt_const.mul hh).cexp'
  · intro q hq
    have hn1 : (1:ℝ)≤n := by exact_mod_cast hN.trans hn
    have hh := (hβb w q (show ‖q‖<δ by simpa only [mem_ball,dist_zero_right] using hq)).trans
      (div_le_self hM.le hn1)
    change ‖Complex.exp (I*β (hillPeriodOneCoefficientMap w q))‖≤Real.exp M
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    apply (Complex.re_le_norm _).trans
    simpa only [norm_mul,norm_I,one_mul] using hh
  · intro q hq
    let r : RealPeriodOneHillPotential := ⟨hillPeriodOneUnitPotential w q.val,
      hillPeriodOneUnitPotential_even w q.val,hillPeriodOneUnitPotential_real w q.val q.property⟩
    have hr : ‖r.val‖<δ := (norm_hillPeriodOneUnitPotential_le w q.val).trans_lt hq
    change Complex.exp (I*β (hillPeriodOneCoefficientMap w q.val))=_
    rw [hillPeriodOneCoefficientMap_eq_unit,hphysical r hr]

end NLS.KdV
