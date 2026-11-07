import NLS.Articles.KdVPseudomeasures.OriginalHillFiniteGapEnergyTrace
import NLS.Articles.KdVPseudomeasures.OriginalHillFiniteGapMiura
import NLS.KdV.HillMiuraWeightedQuarticContour
import NLS.KdV.HillRiccatiMeanZeroLift

/-! The actual original finite-gap H1 energy equals its weighted
quartic primitive contour, with exact normalization and genuine lifts. -/
noncomputable section
open Set Metric Complex NLS.KdV NLS.MKdV NLS.WeightedCoeff NLS.ZakharovShabat
open scoped ContDiff
namespace NLS.Articles.KdVPseudomeasures

theorem hillH1_complexHamiltonian_finiteGap_Miura_trace
    (q : RealSignedHilbert (signedStepOrder 0 1)) (u : PeriodOneRealL2) (c : ℝ)
    (hf : hillMiuraRealSource u ∈ sourceFiniteGapLocus (by simp) (by norm_num))
    (hi : periodOneMiura u.val=hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 q)+
      periodOneL2Inclusion (lp.single 2 0 (c:ℂ))) :
    periodOneKdVHamiltonian (signedOneRealToScalarDomain q)=
      (1/2:ℂ)*sourceFiniteGapNLSHamiltonian (by simp) (by norm_num) (hillMiuraRealSource u) hf 5-
        3*(c:ℂ)*sourceFiniteGapNLSHamiltonian (by simp) (by norm_num) (hillMiuraRealSource u) hf 3+
        2*(c:ℂ)^3 := by
  have hc := hillMiura_shift_eq_norm_sq (hillIntegerSourceInclusion 1 q) u c hi
  have hm : (∫ x in (0:ℝ)..1, (hillMiuraFiniteGapProfile u hf x)^2)=(c:ℂ) := by
    rw [integral_sq_hillMiuraFiniteGapProfile,← hc]
  have he := classicalKdVHamiltonian_centered_miura_NLS (hillMiuraFiniteGapProfile u hf)
    (contDiff_hillMiuraFiniteGapProfile u hf) (periodic_hillMiuraFiniteGapProfile u hf) c hm
  rw [← sourceFiniteGapNLSHamiltonian_hillMiura_eq_classical,
    ← sourceFiniteGapNLSHamiltonian_hillMiura_eq_classical] at he
  rw [periodOneKdVHamiltonian_eq_classical,hillH1_synthesis_eq_centered_finiteGap_Miura q u c hf hi,he]

theorem hillH1_finiteGap_Miura_weighted_quartic_energy_contour
    {W : Set (CoeffPair 2)}
    (C : SourceFullAbelianUniformCauchyFamily (by simp) (by norm_num) W)
    (q : RealSignedHilbert (signedStepOrder 0 1)) (u : PeriodOneRealL2) (c : ℝ)
    (hf : hillMiuraRealSource u ∈ sourceFiniteGapLocus (by simp) (by norm_num))
    (hi : periodOneMiura u.val=hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 q)+
      periodOneL2Inclusion (lp.single 2 0 (c:ℂ)))
    (hC : (hillMiuraRealSource u).val ∈ ball C.discs.source.val C.discs.sourceRadius) :
    ∃ T : ℝ, 0 < T ∧ ∀ R : ℝ, T ≤ R → ∀ n : ℤ,
      (∮ z in C(0,R), z*(sourceFullAbelianPrimitive (by simp) (by norm_num) W n
          (z,(hillMiuraRealSource u).val)-I*(Real.pi:ℂ)*n)^4)=
        (-(Real.pi:ℂ)*I/2)*periodOneKdVHamiltonian (signedOneRealToScalarDomain q) := by
  obtain ⟨T,hT,hcontour⟩ := hillMiura_finiteGap_weighted_quartic_contour C u hC hf
  have hmass : sourceFiniteGapNLSHamiltonian (by simp) (by norm_num) (hillMiuraRealSource u) hf 1=(c:ℂ) := by
    rw [sourceFiniteGapNLSHamiltonian_hillMiura_one,← hillMiura_shift_eq_norm_sq (hillIntegerSourceInclusion 1 q) u c hi]
  refine ⟨T,hT,?_⟩
  intro R hR n
  rw [hcontour R hR n,hmass,hillH1_complexHamiltonian_finiteGap_Miura_trace q u c hf hi]
  ring

theorem hillH1KdVHamiltonian_eq_real_quartic_contour
    {W : Set (CoeffPair 2)}
    (C : SourceFullAbelianUniformCauchyFamily (by simp) (by norm_num) W)
    (q : RealSignedHilbert (signedStepOrder 0 1)) (u : PeriodOneRealL2) (c : ℝ)
    (hf : hillMiuraRealSource u ∈ sourceFiniteGapLocus (by simp) (by norm_num))
    (hi : periodOneMiura u.val=hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 q)+
      periodOneL2Inclusion (lp.single 2 0 (c:ℂ)))
    (hC : (hillMiuraRealSource u).val ∈ ball C.discs.source.val C.discs.sourceRadius) :
    ∃ T : ℝ, 0 < T ∧ ∀ R : ℝ, T ≤ R → ∀ n : ℤ,
      hillH1KdVHamiltonian q=
        ((2*I/(Real.pi:ℂ))*(∮ z in C(0,R), z*(sourceFullAbelianPrimitive (by simp) (by norm_num) W n
          (z,(hillMiuraRealSource u).val)-I*(Real.pi:ℂ)*n)^4)).re := by
  obtain ⟨T,hT,hcontour⟩ := hillH1_finiteGap_Miura_weighted_quartic_energy_contour C q u c hf hi hC
  have hpi : (Real.pi:ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hn : (2*I/(Real.pi:ℂ))*(-(Real.pi:ℂ)*I/2)=1 := by
    calc
      _ = -(I*I) := by field_simp
      _ = _ := by rw [I_mul_I,neg_neg]
  refine ⟨T,hT,?_⟩
  intro R hR n
  rw [hcontour R hR n,← mul_assoc,hn,one_mul]
  rfl

theorem originalHill_exists_finiteGap_quartic_energy_contour
    (q : RealSignedHilbert (signedStepOrder 0 1))
    (hf : hillIntegerSourceInclusion 1 q ∈ hillRealFiniteGapLocus) :
    ∃ u : PeriodOneRealL2, ∃ W : Set (CoeffPair 2),
      ∃ C : SourceFullAbelianUniformCauchyFamily (by simp) (by norm_num) W,
        periodOneMiura u.val=hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 q)+
          periodOneL2Inclusion (lp.single 2 0 ((‖u.val‖^2:ℝ):ℂ)) ∧
        (hillMiuraRealSource u).val ∈ ball C.discs.source.val C.discs.sourceRadius ∧
        ∃ T : ℝ, 0 < T ∧ ∀ R : ℝ, T ≤ R → ∀ n : ℤ,
          (∮ z in C(0,R), z*(sourceFullAbelianPrimitive (by simp) (by norm_num) W n
              (z,(hillMiuraRealSource u).val)-I*(Real.pi:ℂ)*n)^4)=
            (-(Real.pi:ℂ)*I/2)*periodOneKdVHamiltonian (signedOneRealToScalarDomain q) := by
  obtain ⟨u,_,hi⟩ := exists_mean_zero_real_Miura_lift (hillIntegerSourceInclusion 1 q)
  have hfu := hillMiuraRealSource_finiteGap_of_hillRealFiniteGap (hillIntegerSourceInclusion 1 q) hf u (‖u.val‖^2) hi
  obtain ⟨W,_,_,hfamilies⟩ := exists_sourceFullAbelianUniformCauchyFamilies (p := 2) (by simp) (by norm_num)
  obtain ⟨C,hC⟩ := hfamilies (hillMiuraRealSource u)
  have huC : (hillMiuraRealSource u).val ∈ ball C.discs.source.val C.discs.sourceRadius := by
    rw [hC]
    exact mem_ball_self C.discs.sourceRadius_pos
  exact ⟨u,W,C,hi,huC,hillH1_finiteGap_Miura_weighted_quartic_energy_contour C q u (‖u.val‖^2) hfu hi huC⟩

end NLS.Articles.KdVPseudomeasures
