import NLS.KdV.HillComplexFreeSupportedPeriodMap
import NLS.ComplexAnalysis.QuantitativeNeumannAnalyticInverse
import NLS.ComplexAnalysis.QuantitativeTriangularDerivative
import NLS.ComplexAnalysis.BanachHolomorphicC1

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal Classical

namespace NLS.KdV



variable
    (hq : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

def hillComplexFreePeriodJointMap (n : ℕ)
    (t : PositiveDeletedCoeff 2 (n : ℤ) × Coeff 2) : PositiveDeletedCoeff 2 (n : ℤ) × Coeff 2 :=
  (hillComplexFreeSupportedPeriodMap hq hr n t,t.2)

theorem norm_hillComplexFreePeriodJointMap_le (n : ℕ) (hn : 1≤n)
    (ε D : ℝ) (hD : 0≤D) (hc : HillComplexPeriodControl hq hr ε D)
    (R : ℝ) (hR : 0<R) (hRε : 4*R≤ε)
    (t : PositiveDeletedCoeff 2 (n : ℤ) × Coeff 2) (ht : t∈ball 0 (4*R)) :
    ‖hillComplexFreePeriodJointMap hq hr n t‖≤
      Real.exp ((2/Real.pi^2)*(4*R))*(4*R)+2*D*Real.exp ((8/Real.pi^2)*(4*R))*(4*R)+4*R := by
  have htR : ‖t‖≤4*R := (show ‖t‖<4*R by simpa only [mem_ball,dist_zero_right] using ht).le
  have haR : ‖t.1‖≤4*R := (le_max_left ‖t.1‖ ‖t.2‖).trans htR
  have hpR : ‖t.2‖≤4*R := (le_max_right ‖t.1‖ ‖t.2‖).trans htR
  have hh := norm_hillComplexFreeSupportedPeriodMap_le hq hr n hn ε D hD hc t.1 t.2 (hpR.trans hRε)
  have hfirst : Real.exp ((2/Real.pi^2)*‖t.1‖)*‖t.1‖≤Real.exp ((2/Real.pi^2)*(4*R))*(4*R) :=
    mul_le_mul (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left haR (by positivity))) haR
      (norm_nonneg _) (Real.exp_nonneg _)
  have hsecond : 2*D*Real.exp ((8/Real.pi^2)*‖t.1‖)*‖t.2‖≤2*D*Real.exp ((8/Real.pi^2)*(4*R))*(4*R) := by
    gcongr
  change max ‖hillComplexFreeSupportedPeriodMap hq hr n t‖ ‖t.2‖≤_
  apply max_le
  · exact (hh.trans (add_le_add hfirst hsecond)).trans (le_add_of_nonneg_right (by positivity))
  · have hnonneg : 0≤Real.exp ((2/Real.pi^2)*(4*R))*(4*R)+
        2*D*Real.exp ((8/Real.pi^2)*(4*R))*(4*R) := by positivity
    linarith

/-- The actual original complex off-diagonal period equations have a
common analytic root chart near the free source, with common root and
potential radii chosen before the coordinate index. -/
theorem exists_hillComplexFreeSupportedPeriods_common_analytic_root :
    ∃ ρ δ : ℝ, 0<ρ ∧ 0<δ ∧ ∀ n : ℕ, 1≤n →
      ∃ s : Coeff 2 → PositiveDeletedCoeff 2 (n : ℤ),
        AnalyticOnNhd ℂ s (ball 0 δ) ∧ s 0=0 ∧
        ∀ p∈ball 0 δ,
          (s p,p)∈ball 0 ρ ∧ hillComplexFreeSupportedPeriodMap hq hr n (s p,p)=0 ∧
          (∀ k : ℕ, 1≤k → k≠n → hillAbelianComplexPeriod 0 hq hr n k ((s p : Coeff 2),p)=0) ∧
          ∀ a∈ball 0 ρ, hillComplexFreeSupportedPeriodMap hq hr n (a,p)=0 → a=s p := by
  obtain ⟨ε,D,hε,hD,hc⟩ := exists_hillComplexPeriodControl hq hr
  let R := ε/8
  have hR : 0<R := by dsimp only [R];positivity
  have hRε : 4*R≤ε := by dsimp only [R];linarith
  let M := Real.exp ((2/Real.pi^2)*(4*R))*(4*R)+2*D*Real.exp ((8/Real.pi^2)*(4*R))*(4*R)+4*R
  have hM : 0≤M := by dsimp only [M];positivity
  let B := 2+2*M/R
  let L := 4*M/R^2
  have hB : 1≤B := by
    have hh : 0≤2*M/R := by positivity
    dsimp only [B]
    linarith
  have hBp : 0<B := lt_of_lt_of_le zero_lt_one hB
  have hL : 0≤L := by dsimp only [L];positivity
  let r := quantitativeNeumannRadius R B L
  have hrpos : 0<r := quantitativeNeumannRadius_pos hR hB hL
  have hrR : r≤R := min_le_left _ _
  let ρ := quantitativeInverseJointRadius r B L
  let δ := quantitativeInverseImageRadius r B L
  have hρ : 0<ρ := quantitativeInverseJointRadius_pos hrpos hBp hL
  have hδ : 0<δ := quantitativeInverseImageRadius_pos hrpos hBp hL
  have hρR : ρ≤R := (min_le_left _ _).trans (by linarith : r/2≤R)
  have hδρ : δ≤ρ := div_le_self hρ.le (by nlinarith : 1≤8*B)
  refine ⟨ρ,δ,hρ,hδ,?_⟩
  intro n hn
  let H := hillComplexFreeSupportedPeriodMap hq hr n
  let J := hillComplexFreePeriodJointMap hq hr n
  have hdom : ball (0 : PositiveDeletedCoeff 2 (n : ℤ) × Coeff 2) (4*R) ⊆ univ ×ˢ ball 0 ε := by
    intro t ht
    refine ⟨mem_univ _,?_⟩
    rw [mem_ball,dist_zero_right]
    have hp : ‖t.2‖≤‖t‖ := le_max_right _ _
    exact hp.trans_lt ((show ‖t‖<4*R by simpa only [mem_ball,dist_zero_right] using ht).trans_le hRε)
  have hH : AnalyticOnNhd ℂ H (ball 0 (4*R)) :=
    (analyticOnNhd_hillComplexFreeSupportedPeriodMap hq hr n hn ε D hD.le hc).mono hdom
  have hJ : AnalyticOnNhd ℂ J (ball 0 (4*R)) := hH.prod analyticOnNhd_snd
  have hbJ : ∀ t∈ball 0 (4*R), ‖J t‖≤M :=
    fun t ht => norm_hillComplexFreePeriodJointMap_le hq hr n hn ε D hD.le hc R hR hRε t ht
  have hH0 := hH 0 (mem_ball_self (by positivity : 0<4*R))
  let A := fderiv ℂ H 0
  have hA : ‖A‖≤2*M/R := by
    apply norm_fderiv_le_of_ball_bound H 0 0 R R M hR
      (hH.differentiableOn.mono (ball_subset_ball (by linarith))) _ (mem_ball_self hR)
    intro t ht
    have ht' : t∈ball 0 (4*R) := ball_subset_ball (by linarith : R+R≤4*R) ht
    exact (show ‖H t‖≤‖J t‖ from le_max_left _ _).trans (hbJ t ht')
  have hQ : A.comp (ContinuousLinearMap.inl ℂ (PositiveDeletedCoeff 2 (n : ℤ)) (Coeff 2))=
      -ContinuousLinearMap.id ℂ (PositiveDeletedCoeff 2 (n : ℤ)) :=
    hillComplexFreeSupportedPeriodMap_root_derivative_zero hq hr n hn ε D hε hD.le hc
  let S : PositiveDeletedCoeff 2 (n : ℤ) →L[ℂ] PositiveDeletedCoeff 2 (n : ℤ) :=
    -(ContinuousLinearMap.id ℂ _)
  have hQS : (A.comp (ContinuousLinearMap.inl ℂ (PositiveDeletedCoeff 2 (n : ℤ)) (Coeff 2))).comp S=
      ContinuousLinearMap.id ℂ _ := by
    rw [hQ]
    ext x
    simp only [ContinuousLinearMap.comp_apply,neg_apply,ContinuousLinearMap.id_apply,S,neg_neg]
  have hSQ : S.comp (A.comp (ContinuousLinearMap.inl ℂ (PositiveDeletedCoeff 2 (n : ℤ)) (Coeff 2)))=
      ContinuousLinearMap.id ℂ _ := by
    rw [hQ]
    ext x
    simp only [ContinuousLinearMap.comp_apply,neg_apply,ContinuousLinearMap.id_apply,S,neg_neg]
  have hS : ‖S‖≤1 := by
    apply ContinuousLinearMap.opNorm_le_bound S (by norm_num)
    intro x
    change ‖-x‖≤1*‖x‖
    simp
  obtain ⟨T,hT,hTB⟩ := exists_triangularLinearEquiv_norm_bound A S hQS hSQ
  have hDJ : fderiv ℂ J 0=A.prod (ContinuousLinearMap.snd ℂ (PositiveDeletedCoeff 2 (n : ℤ)) (Coeff 2)) := by
    change fderiv ℂ (fun t => (H t,t.2)) 0 = _
    simpa only [fderiv_snd] using hH0.differentiableAt.fderiv_prodMk differentiableAt_snd
  have hT' : (T : (PositiveDeletedCoeff 2 (n : ℤ) × Coeff 2) →L[ℂ]
      (PositiveDeletedCoeff 2 (n : ℤ) × Coeff 2))=fderiv ℂ J 0 := hT.trans hDJ.symm
  have hTB' : ‖(T.symm : (PositiveDeletedCoeff 2 (n : ℤ) × Coeff 2) →L[ℂ]
      (PositiveDeletedCoeff 2 (n : ℤ) × Coeff 2))‖≤B := by
    apply hTB.trans
    calc
      _ ≤ 1*(1+2*M/R)+1 := by
        have hh : 1+‖A‖≤1+2*M/R := by linarith only [hA]
        have hm := mul_le_mul hS hh (by positivity : 0≤1+‖A‖) (by norm_num : (0 : ℝ)≤1)
        nlinarith only [hm]
      _ = B := by dsimp only [B];ring
  have hLip (x : PositiveDeletedCoeff 2 (n : ℤ) × Coeff 2) (hx : x∈ball 0 R)
      (y : PositiveDeletedCoeff 2 (n : ℤ) × Coeff 2) (hy : y∈ball 0 R) :
      ‖fderiv ℂ J x-fderiv ℂ J y‖≤L*‖x-y‖ :=
    norm_fderiv_sub_le_of_holomorphic_ball_bound J 0 R M hR hJ.differentiableOn hbJ hy hx
  obtain ⟨G,hGa,hG0,hG⟩ := exists_analytic_inverse_on_neumann_ball J 0 R B L hR hB hL
    (hJ.mono (ball_subset_ball (by linarith))) T hT' hTB' hLip
  have hH00 : H (0,0)=0 := by
    rw [show H=hillComplexFreeSupportedPeriodMap hq hr n from rfl,
      hillComplexFreeSupportedPeriodMap_at_zero_parameter hq hr n hn ε D hε.le hD.le hc]
    exact hillFreeSupportedPeriodMap_zero hq hr n hn
  have hJ00 : J 0=0 := Prod.ext hH00 rfl
  rw [hJ00] at hGa hG0 hG
  let s := fun p : Coeff 2 => (G (0,p)).1
  refine ⟨s,?_,?_,?_⟩
  · intro p hp
    have hpair : (0,p)∈ball (0 : PositiveDeletedCoeff 2 (n : ℤ) × Coeff 2) δ := by
      simpa only [mem_ball,dist_zero_right,Prod.norm_def,norm_zero,max_eq_right (norm_nonneg _)] using hp
    exact ((ContinuousLinearMap.fst ℂ (PositiveDeletedCoeff 2 (n : ℤ)) (Coeff 2)).analyticAt _).comp
      ((hGa (0,p) hpair).comp (f := fun p : Coeff 2 => ((0 : PositiveDeletedCoeff 2 (n : ℤ)),p))
        (analyticAt_const.prod analyticAt_id))
  · have hh := congrArg Prod.fst hG0
    exact hh
  · intro p hp
    have hpair : (0,p)∈ball (0 : PositiveDeletedCoeff 2 (n : ℤ) × Coeff 2) δ := by
      simpa only [mem_ball,dist_zero_right,Prod.norm_def,norm_zero,max_eq_right (norm_nonneg _)] using hp
    obtain ⟨hmem,he,hunique⟩ := hG (0,p) hpair
    have hsecond : (G (0,p)).2=p := congrArg Prod.snd he
    have hfirst : H (G (0,p))=0 := congrArg Prod.fst he
    have hsPair : (s p,p)=G (0,p) := Prod.ext rfl hsecond.symm
    have hroot : hillComplexFreeSupportedPeriodMap hq hr n (s p,p)=0 := by
      rw [hsPair]
      exact hfirst
    have hpε : p∈ball 0 ε := by
      have hpδ : ‖p‖<δ := by simpa only [mem_ball,dist_zero_right] using hp
      rw [mem_ball,dist_zero_right]
      exact hpδ.trans_le (hδρ.trans (hρR.trans (by dsimp only [R];linarith)))
    have hmem' : (s p,p)∈ball 0 ρ := by rw [hsPair];exact hmem
    refine ⟨hmem',hroot,
      (hillComplexFreeSupportedPeriodMap_zero_iff_periods hq hr n hn ε D hD.le hc (s p) p hpε).mp hroot,?_⟩
    intro a ha hazero
    have hpρ : p∈ball 0 ρ := ball_subset_ball hδρ hp
    have haPair : (a,p)∈ball (0 : PositiveDeletedCoeff 2 (n : ℤ) × Coeff 2) ρ := by
      simpa only [mem_ball,dist_zero_right,Prod.norm_def,max_lt_iff] using And.intro ha hpρ
    have hJazero : J (a,p)=(0,p) := Prod.ext hazero rfl
    exact congrArg Prod.fst (hunique (a,p) haPair hJazero)

end NLS.KdV
