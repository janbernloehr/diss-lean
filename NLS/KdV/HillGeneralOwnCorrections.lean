import NLS.KdV.HillCenteredQuadraticDirichletValue
import NLS.KdV.HillGeneralCenteredPrimitives
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



variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

include h0q h0r in
/-- Actual own-gap regular corrections have one common complex analytic
chart at every real source, with O(1/n) bounds on bounded native inputs. -/
theorem exists_hillOwnRegularAbelianCorrection_general_native_charts (L : ℝ) (hL : 0≤L) :
    ∃ δ M : ℝ, ∃ N : ℕ, ∃ V : Set RealPeriodOneHillPotential,
      0<δ ∧ 0<M ∧ ∃ hN : 1≤N, IsOpen V ∧ (⟨q,hq,hr⟩ : RealPeriodOneHillPotential)∈V ∧
      (∀ p∈V, SpectralWeight.one.toCoeff p.val∈ball (SpectralWeight.one.toCoeff q) δ) ∧
      ∀ n : ℕ, ∀ hn : N≤n, ∃ β : Coeff 2 → ℂ,
        AnalyticOnNhd ℂ β (ball (SpectralWeight.one.toCoeff q) δ) ∧
        (∀ w : SpectralWeight, ∀ r : WeightedCoeff w.doubleIndex.toWeight 2, ‖r‖≤L →
          hillPeriodOneCoefficientMap w r∈ball (SpectralWeight.one.toCoeff q) δ →
          ‖β (hillPeriodOneCoefficientMap w r)‖≤M/(n : ℝ)) ∧
        ∀ p∈V, β (SpectralWeight.one.toCoeff p.val)=
          hillRegularAbelianCorrection p.val p.property.1 p.property.2 n (hN.trans hn) n (hN.trans hn) := by
  obtain ⟨δ,B0,B,Np,V,hδ,hB0,hB,hNp,hsub,hV,hqV,hsource,hprimitives⟩ :=
    exists_hillSelectedPsi_general_centered_mean_free_primitives q hq hr h0q h0r
  obtain ⟨T,Nt,hT,_,hterminal⟩ := exists_hillNativeComplexDirichletGapTerminal_uniform_bound h0q h0r L hL
  obtain ⟨Nv,_,hvalue⟩ := exists_hillCenteredQuadraticDirichletValue_uniform_pointwise_bound h0q h0r B0
  obtain ⟨Nr,_,hrootmatch⟩ := exists_hillFilledFreeGapRoot_bounded_real_physical_matching h0q h0r B0
  obtain ⟨Ny,_,hsymmetric⟩ := exists_hillFreeGap_bounded_real_symmetric_data_matching h0q h0r B0
  obtain ⟨Nl,_,hlocal⟩ := exists_hillFreeGap_bounded_real_midpoint_halfgap_localization h0q h0r (1/32) (by norm_num) (by norm_num) B0
  obtain ⟨Nm,_,hmumatch⟩ := exists_hillScaledDirichletRoot_bounded_real_physical_matching h0q h0r (1/16) (by norm_num) (by norm_num) B0
  obtain ⟨Nd,_,hmuchart⟩ := exists_hillScaledDirichletRoot_bounded_complex_analytic_chart h0q h0r (1/16) (by norm_num) (by norm_num) B0
  let N := Np+Nt+Nv+Nr+Ny+Nl+Nm+Nd+1
  let M := 256*Real.pi*B*T/Real.pi^2
  have hN : 1≤N := by dsimp only [N];omega
  refine ⟨δ,M,N,V,hδ,by dsimp only [M];positivity,hN,hV,hqV,hsource,?_⟩
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
  have hval := hvalue (ball (SpectralWeight.one.toCoeff q) δ) hsub n hnV Q hQa (64*Real.pi*B/R) hQb
  refine ⟨β,hval.1,?_,?_⟩
  · intro w r hrnorm hrU
    have hp : hillPeriodOneCoefficientMap w r∈ball (SpectralWeight.one.toCoeff q) δ := hrU
    have ht := hterminal w r hrnorm n hnT
    change ‖hillComplexDirichletGapTerminal h0q h0r n (hillPeriodOneCoefficientMap w r)‖≤T at ht
    apply ((hval.2 _ hp).trans (mul_le_mul_of_nonneg_right ht (by positivity : 0≤64*Real.pi*B/R))).trans
    calc
      T*(64*Real.pi*B/R) ≤ T*(64*Real.pi*B/(Real.pi^2*(n : ℝ)/4)) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left (by positivity) (by positivity) hRlow) hT.le
      _ = M/(n : ℝ) := by dsimp only [M];field_simp;ring
  · intro pR hpR
    let p := SpectralWeight.one.toCoeff pR.val
    have hp : p∈ball (SpectralWeight.one.toCoeff q) δ := hsource pR hpR
    have hpδ : ‖p‖≤B0 :=
      (show ‖p‖<B0 by simpa only [mem_ball,dist_zero_right] using hsub hp).le
    have hmu := hmumatch pR.val pR.property.1 pR.property.2 hpδ n hnM
    change hillScaledDirichletRoot h0q h0r (1/16) n p=
      (hillDirichletEnergy pR.val pR.property.1 pR.property.2 n hn1 : ℂ) at hmu
    obtain ⟨hMid,hSq⟩ := hsymmetric pR.val pR.property.1 pR.property.2 hpδ n hnY
    obtain ⟨hτ,hgapbound⟩ := hlocal pR.val pR.property.1 pR.property.2 hpδ n hnL
    have hμK : (hillDirichletEnergy pR.val pR.property.1 pR.property.2 n hn1 : ℂ)∈closedBall c R := by
      have hh := closedBall_subset_closedBall (by linarith : (1/16)*R≤R)
        (ball_subset_closedBall (((hmuchart n hnD).2 p hpδ).1))
      simpa only [hmu] using hh
    have hroot := hrootmatch pR.val pR.property.1 pR.property.2 hpδ n hnR
    have hβeq : β p=I*hillDirichletSheetRoot p (hillDirichletEnergy pR.val pR.property.1 pR.property.2 n hn1)/
        hillDeflatedEnergyCanonicalRoot pR.val pR.property.1 pR.property.2 n (hillDirichletEnergy pR.val pR.property.1 pR.property.2 n hn1)*
          Q ((hillDirichletEnergy pR.val pR.property.1 pR.property.2 n hn1 : ℂ)-
            (hillRealGapCenter pR.val pR.property.1 pR.property.2 n : ℂ),p) := by
      dsimp only [β,hillCenteredQuadraticDirichletValue,hillComplexDirichletGapTerminal]
      rw [hmu,hMid,hroot _ hμK]
      ring
    have hpoint (w : ℂ) (hw : w∈ball (0:ℂ) (R/4)) :
        (hillRealGapCenter pR.val pR.property.1 pR.property.2 n : ℂ)+w∈closedBall c R := by
      have hw' : ‖w‖<R/4 := by simpa only [mem_ball,dist_zero_right] using hw
      rw [mem_closedBall,dist_eq_norm]
      have hh : ‖(hillRealGapCenter pR.val pR.property.1 pR.property.2 n : ℂ)+w-c‖≤
          ‖(hillRealGapCenter pR.val pR.property.1 pR.property.2 n : ℂ)-c‖+‖w‖ := by
        rw [show (hillRealGapCenter pR.val pR.property.1 pR.property.2 n : ℂ)+w-c=
          ((hillRealGapCenter pR.val pR.property.1 pR.property.2 n : ℂ)-c)+w by ring]
        exact norm_add_le _ _
      linarith
    have hcos (θ : ℝ) (_hθ : θ∈Icc (0:ℝ) Real.pi) :
        cosineGapPoint (hillRealGapCenter pR.val pR.property.1 pR.property.2 n)
          (hillRealGapHalfLength pR.val pR.property.1 pR.property.2 n) (θ : ℂ)∈closedBall c R := by
      have hc : ‖(Real.cos θ : ℂ)‖≤1 := by simpa only [norm_real,Real.norm_eq_abs] using Real.abs_cos_le_one θ
      rw [cosineGapPoint,← ofReal_cos,mem_closedBall,dist_eq_norm]
      have hh : ‖(hillRealGapCenter pR.val pR.property.1 pR.property.2 n : ℂ)+
          (hillRealGapHalfLength pR.val pR.property.1 pR.property.2 n : ℂ)*(Real.cos θ : ℂ)-c‖≤
          ‖(hillRealGapCenter pR.val pR.property.1 pR.property.2 n : ℂ)-c‖+
            ‖(hillRealGapHalfLength pR.val pR.property.1 pR.property.2 n : ℂ)‖ := by
        rw [show (hillRealGapCenter pR.val pR.property.1 pR.property.2 n : ℂ)+
          (hillRealGapHalfLength pR.val pR.property.1 pR.property.2 n : ℂ)*(Real.cos θ : ℂ)-c=
          ((hillRealGapCenter pR.val pR.property.1 pR.property.2 n : ℂ)-c)+
            (hillRealGapHalfLength pR.val pR.property.1 pR.property.2 n : ℂ)*(Real.cos θ : ℂ) by ring]
        apply (norm_add_le _ _).trans
        rw [norm_mul]
        exact add_le_add le_rfl (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hc (norm_nonneg _))
      linarith
    have hs : hillLocalGapSquare 0 h0q h0r n p/4=(hillRealGapHalfLength pR.val pR.property.1 pR.property.2 n : ℂ)^2 := by
      rw [hSq]
      ring
    have hQphysical : AnalyticOnNhd ℂ (fun w => Q (w,p)) (ball (0:ℂ) (R/4)) := by
      intro w hw
      exact (hQa (w,p) ⟨hw,hp⟩).comp (f := fun z : ℂ => (z,p)) (analyticAt_id.prod analyticAt_const)
    have hODEphysical (w : ℂ) (hw : w∈ball (0:ℂ) (R/4)) :
        (w^2-(hillRealGapHalfLength pR.val pR.property.1 pR.property.2 n : ℂ)^2)*deriv (fun z => Q (z,p)) w+w*Q (w,p)=
          -I*hillAbelianSelectedGlobalPsi pR.val pR.property.1 pR.property.2 n hn1
              ((hillRealGapCenter pR.val pR.property.1 pR.property.2 n : ℂ)+w)/
            hillDeflatedEnergyCanonicalRoot pR.val pR.property.1 pR.property.2 n
              ((hillRealGapCenter pR.val pR.property.1 pR.property.2 n : ℂ)+w)-(if n=n then 1 else 0) := by
      have hh := hODE p hp w hw
      rw [hs] at hh
      exact hh.trans (centeredMeanFree_hillCenteredComplexRegularGapNumerator_eq_physical h0q h0r
        G n n hn1 hn1 pR (closedBall c R) (hreal pR hpR) hroot hMid hSq hcos w (hpoint w hw))
    by_cases hgap : hillRealGapHalfLength pR.val pR.property.1 pR.property.2 n=0
    · rw [hβeq,hillDirichletSheetRoot_eq_zero_of_halfLength_zero pR.val pR.property.1 pR.property.2 n hn1 hgap,
        mul_zero,zero_div,zero_mul,hillRegularAbelianCorrection_closed pR.val pR.property.1 pR.property.2 n hn1 n hn1 hgap]
    · let θ := hillDirichletSelectedRealAngle pR.val pR.property.1 pR.property.2 n hn1 hgap
      have hspec := hillDirichletSelectedRealAngle_spec pR.val pR.property.1 pR.property.2 n hn1 hgap
      have hh := hillRegularAbelian_terminal_eq_quadratic pR.val pR.property.1 pR.property.2 n n hn1 hn1 hgap
        (fun w => Q (w,p)) (R/4) (by linarith) hQphysical hODEphysical θ hspec.2.1 hspec.2.2
      rw [hβeq,hillRegularAbelianCorrection,dif_neg hgap,hillRegularAbelianPrimitive]
      exact hh

end NLS.KdV
