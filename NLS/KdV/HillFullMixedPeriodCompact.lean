import NLS.KdV.HillFullMixedPeriodMap

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem hillFullMixedComplexPeriodSequence_sub_free_high_coordinate
    (N : ℕ) (a p : Coeff 2)
    (m : ℤ) (hm : N ≤ m.natAbs) :
    (hillFullMixedComplexPeriodSequence q hq hr h0q h0r N (a,p)-hillFreeFullPeriodSequence a) m=
      hillFullComplexPeriodErrorSequence h0q h0r N (a,p) m := by
  have hlo : hillFullLowComplexPeriodSequence q hq hr N (a,p) m=0 := by
    by_cases hpos : 0<m
    · have hcast : (m.toNat : ℤ)=m := by omega
      rw [←hcast,hillFullLowComplexPeriodSequence_apply_nat q hq hr N m.toNat (by omega),if_neg (by omega)]
    · exact hillFullLowComplexPeriodSequence_apply_nonpositive q hq hr N (a,p) m (by omega)
  simp only [lp.coeFn_sub,Pi.sub_apply,hillFullMixedComplexPeriodSequence,lp.coeFn_add,Pi.add_apply,
    hlo,Coeff.fourierTail_apply,if_pos hm,zero_add,add_sub_cancel_left]

theorem isCompactOperator_fderiv_hillFullMixedPeriod_sub_free
    (N : ℕ) (hN : 1 ≤ N) (B D : ℝ) (hD : 0 ≤ D)
    (hc : HillComplexTailPeriodControl h0q h0r N B D) (a p : Coeff 2) (hp : ‖p‖ ≤ B)
    (hF : AnalyticOnNhd ℂ (fun b : Coeff 2 => hillFullMixedComplexPeriodSequence q hq hr h0q h0r N (b,p)) univ) :
    IsCompactOperator (fderiv ℂ (fun b : Coeff 2 =>
      hillFullMixedComplexPeriodSequence q hq hr h0q h0r N (b,p)-hillFreeFullPeriodSequence b) a) := by
  let M : ℝ := D*Real.exp ((8/Real.pi^2)*(‖a‖+2))*‖p‖
  let b : Coeff 2 := (M : ℂ) • Coeff.positivePuncturedLattice 2 (by norm_num)
  have hdiff : DifferentiableOn ℂ (fun v : Coeff 2 =>
      hillFullMixedComplexPeriodSequence q hq hr h0q h0r N (v,p)-hillFreeFullPeriodSequence v)
      (ball a (1+1)) :=
    (hF.differentiableOn.sub analyticOnNhd_hillFreeFullPeriodSequence.differentiableOn).mono (subset_univ _)
  apply Coeff.isCompactOperator_fderiv_of_tailCoordinateBound (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
    _ a 1 (by norm_num) hdiff b (Finset.Icc (-(N : ℤ)) N)
  intro m hm v hv
  have hcut : N ≤ m.natAbs := by simp only [Finset.mem_Icc] at hm;omega
  have hv2 : ‖v-a‖ < 2 := by simpa only [mem_ball,dist_eq_norm,show (1 : ℝ)+1=2 by norm_num] using hv
  have hva : ‖v‖ ≤ ‖a‖+2 := by
    have ht := norm_add_le (v-a) a
    rw [sub_add_cancel] at ht
    linarith
  rw [hillFullMixedComplexPeriodSequence_sub_free_high_coordinate q hq hr h0q h0r N v p m hcut,
    hillFullComplexPeriodErrorSequence_apply h0q h0r N hN B D hD hc v p hp]
  have hnorm := norm_hillFullComplexPeriodErrorCoordinate_le h0q h0r N hN B D hD hc v p hp m
  have hb : ‖b m‖ = M*‖Coeff.positivePuncturedLattice 2 (by norm_num) m‖ := by
    simp only [b,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,norm_mul,norm_real,
      Real.norm_eq_abs,abs_of_nonneg (show 0 ≤ M by dsimp [M];positivity)]
  rw [hb]
  apply hnorm.trans
  dsimp only [M]
  gcongr

theorem isCompactOperator_fderiv_hillFullMixedPeriod_add_projection
    (N : ℕ) (hN : 1 ≤ N) (B D : ℝ) (hD : 0 ≤ D)
    (hc : HillComplexTailPeriodControl h0q h0r N B D) (a p : Coeff 2) (hp : ‖p‖ ≤ B)
    (hF : AnalyticOnNhd ℂ (fun b : Coeff 2 => hillFullMixedComplexPeriodSequence q hq hr h0q h0r N (b,p)) univ) :
    IsCompactOperator (fderiv ℂ (fun b : Coeff 2 => hillFullMixedComplexPeriodSequence q hq hr h0q h0r N (b,p)) a+
      Coeff.positiveDeletedProjection 2 (0 : ℤ)) := by
  have hdiff := (hF a (mem_univ _)).differentiableAt.hasFDerivAt
  have hfree := (analyticOnNhd_hillFreeFullPeriodSequence a (mem_univ _)).differentiableAt.hasFDerivAt
  have herr := isCompactOperator_fderiv_hillFullMixedPeriod_sub_free q hq hr h0q h0r N hN B D hD hc a p hp hF
  have hder : fderiv ℂ (fun b : Coeff 2 =>
      hillFullMixedComplexPeriodSequence q hq hr h0q h0r N (b,p)-hillFreeFullPeriodSequence b) a =
        fderiv ℂ (fun b : Coeff 2 => hillFullMixedComplexPeriodSequence q hq hr h0q h0r N (b,p)) a-
          fderiv ℂ hillFreeFullPeriodSequence a := by
    simpa only [Pi.sub_def] using (hdiff.sub hfree).fderiv
  rw [hder] at herr
  have hfreecompact := isCompactOperator_fderiv_hillFreeFullPeriodSequence_add_projection a
  have h : IsCompactOperator
      ((fderiv ℂ (fun b : Coeff 2 => hillFullMixedComplexPeriodSequence q hq hr h0q h0r N (b,p)) a-
        fderiv ℂ hillFreeFullPeriodSequence a)+
        (fderiv ℂ hillFreeFullPeriodSequence a+Coeff.positiveDeletedProjection 2 (0 : ℤ)) :
        Coeff 2 →L[ℂ] Coeff 2) := herr.add hfreecompact
  convert! h using 1
  congr 1
  abel

end NLS.KdV
