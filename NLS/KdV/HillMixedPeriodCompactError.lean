import NLS.KdV.HillMixedPeriodErrorBound
import NLS.KdV.HillFreePeriodCompactRemainder
import NLS.SequenceSpaces.CompactTailCoordinateDerivative

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV



variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem isCompactOperator_fderiv_hillMixedPeriod_sub_free
    (N n : ℕ) (hn : 1 ≤ n) (B D : ℝ) (hD : 0 ≤ D)
    (hc : HillComplexTailPeriodControl h0q h0r N B D) (a p : Coeff 2) (hp : ‖p‖ ≤ B)
    (hF : AnalyticOnNhd ℂ (fun b : Coeff 2 => hillMixedComplexPeriodSequence q hq hr h0q h0r N n (b,p)) univ) :
    IsCompactOperator (fderiv ℂ (fun b : Coeff 2 =>
      hillMixedComplexPeriodSequence q hq hr h0q h0r N n (b,p)-hillFreeScaledPeriodSequence h0q h0r n hn b) a) := by
  let M : ℝ := D*Real.exp ((8/Real.pi^2)*(‖a‖+2))*‖p‖
  let b : Coeff 2 := (M : ℂ) • Coeff.positivePuncturedLattice 2 (by norm_num)
  have hdiff : DifferentiableOn ℂ (fun v : Coeff 2 =>
      hillMixedComplexPeriodSequence q hq hr h0q h0r N n (v,p)-hillFreeScaledPeriodSequence h0q h0r n hn v)
      (ball a (1+1)) :=
    (hF.differentiableOn.sub (analyticOnNhd_hillFreeScaledPeriodSequence h0q h0r n hn).differentiableOn).mono
      (subset_univ _)
  apply Coeff.isCompactOperator_fderiv_of_tailCoordinateBound (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
    _ a 1 (by norm_num) hdiff b (Finset.Icc (-(N : ℤ)) N)
  intro m hm v hv
  have hcut : N ≤ m.natAbs := by simp only [Finset.mem_Icc] at hm;omega
  have hv2 : ‖v-a‖ < 2 := by simpa only [mem_ball,dist_eq_norm,show (1 : ℝ)+1=2 by norm_num] using hv
  have hva : ‖v‖ ≤ ‖a‖+2 := by
    have ht := norm_add_le (v-a) a
    rw [sub_add_cancel] at ht
    linarith
  have hnorm := norm_hillMixedComplexPeriodSequence_sub_free_high_coordinate_le q hq hr h0q h0r N n hn B D hD hc v p hp m hcut
  have hb : ‖b m‖ = M*‖Coeff.positivePuncturedLattice 2 (by norm_num) m‖ := by
    simp only [b,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,norm_mul,norm_real,
      Real.norm_eq_abs,abs_of_nonneg (show 0 ≤ M by dsimp [M];positivity)]
  rw [hb]
  apply hnorm.trans
  dsimp only [M]
  gcongr

theorem isCompactOperator_fderiv_hillMixedPeriod_add_projection
    (N n : ℕ) (hn : 1 ≤ n) (B D : ℝ) (hD : 0 ≤ D)
    (hc : HillComplexTailPeriodControl h0q h0r N B D) (a p : Coeff 2) (hp : ‖p‖ ≤ B)
    (hF : AnalyticOnNhd ℂ (fun b : Coeff 2 => hillMixedComplexPeriodSequence q hq hr h0q h0r N n (b,p)) univ) :
    IsCompactOperator (fderiv ℂ (fun b : Coeff 2 => hillMixedComplexPeriodSequence q hq hr h0q h0r N n (b,p)) a+
      Coeff.positiveDeletedProjection 2 (n : ℤ)) := by
  have hdiff := (hF a (mem_univ _)).differentiableAt.hasFDerivAt
  have hfree := (analyticOnNhd_hillFreeScaledPeriodSequence h0q h0r n hn a (mem_univ _)).differentiableAt.hasFDerivAt
  have herr := isCompactOperator_fderiv_hillMixedPeriod_sub_free q hq hr h0q h0r N n hn B D hD hc a p hp hF
  have hder : fderiv ℂ (fun b : Coeff 2 =>
      hillMixedComplexPeriodSequence q hq hr h0q h0r N n (b,p)-hillFreeScaledPeriodSequence h0q h0r n hn b) a =
        fderiv ℂ (fun b : Coeff 2 => hillMixedComplexPeriodSequence q hq hr h0q h0r N n (b,p)) a-
          fderiv ℂ (hillFreeScaledPeriodSequence h0q h0r n hn) a := by
    simpa only [Pi.sub_def] using (hdiff.sub hfree).fderiv
  rw [hder] at herr
  have hfreecompact := isCompactOperator_fderiv_hillFreeScaledPeriodSequence_add_projection h0q h0r n hn a
  have h : IsCompactOperator
      ((fderiv ℂ (fun b : Coeff 2 => hillMixedComplexPeriodSequence q hq hr h0q h0r N n (b,p)) a-
        fderiv ℂ (hillFreeScaledPeriodSequence h0q h0r n hn) a)+
        (fderiv ℂ (hillFreeScaledPeriodSequence h0q h0r n hn) a+Coeff.positiveDeletedProjection 2 (n : ℤ)) :
        Coeff 2 →L[ℂ] Coeff 2) := herr.add hfreecompact
  convert! h using 1
  congr 1
  abel

end NLS.KdV
