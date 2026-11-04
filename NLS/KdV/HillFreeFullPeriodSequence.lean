import NLS.KdV.HillFreePeriodCompactRemainder

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



/-- The full positive free period coordinate, with no positive root omitted. -/
def hillFreeFullPeriodCoordinate (a : Coeff 2) (m : ℤ) : ℂ :=
  if 0<m ∧ m≠0 then -a m*hilbertWeightedProduct (hillFreeSeparatedWeight 0 m.toNat) a else 0

theorem norm_hillFreeFullPeriodCoordinate_le (a : Coeff 2) (m : ℤ) :
    ‖hillFreeFullPeriodCoordinate a m‖≤Real.exp ((2/Real.pi^2)*‖a‖)*‖a m‖ := by
  unfold hillFreeFullPeriodCoordinate
  split_ifs
  · rw [norm_mul,norm_neg]
    exact (mul_le_mul_of_nonneg_left (norm_hilbertWeightedProduct_hillSeparated_le 0 m.toNat a)
      (norm_nonneg _)).trans_eq (by ring)
  · rw [norm_zero]
    positivity

/-- Actual Hilbert realization of the full free scaled period coordinates. -/
def hillFreeFullPeriodSequence (a : Coeff 2) : Coeff 2 :=
  ⟨hillFreeFullPeriodCoordinate a,by
    apply ((lp.memℓp a).norm.const_mul (Real.exp ((2/Real.pi^2)*‖a‖))).mono
    exact norm_hillFreeFullPeriodCoordinate_le a⟩

theorem hillFreeFullPeriodSequence_apply (a : Coeff 2) (m : ℤ) :
    hillFreeFullPeriodSequence a m=hillFreeFullPeriodCoordinate a m := rfl

theorem norm_hillFreeFullPeriodSequence_le (a : Coeff 2) :
    ‖hillFreeFullPeriodSequence a‖≤Real.exp ((2/Real.pi^2)*‖a‖)*‖a‖ := by
  have hh : ‖hillFreeFullPeriodSequence a‖≤‖(Real.exp ((2/Real.pi^2)*‖a‖) : ℂ) • a‖ := by
    apply lp.norm_mono (by norm_num : (2:ℝ≥0∞)≠0)
    intro m
    simpa only [hillFreeFullPeriodSequence_apply,lp.coeFn_smul,Pi.smul_apply,norm_smul,
      norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] using norm_hillFreeFullPeriodCoordinate_le a m
  simpa only [norm_smul,norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] using hh

theorem analyticOnNhd_hillFreeFullPeriodCoordinate (m : ℤ) :
    AnalyticOnNhd ℂ (fun a : Coeff 2 => hillFreeFullPeriodSequence a m) univ := by
  by_cases hm : 0<m ∧ m≠0
  · intro a _
    change AnalyticAt ℂ (fun a => if 0<m ∧ m≠0 then -a m*hilbertWeightedProduct (hillFreeSeparatedWeight 0 m.toNat) a else 0) a
    simp only [if_pos hm]
    exact ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 m).analyticAt a).neg.mul
      (analyticOnNhd_hilbertWeightedProduct _ a (mem_univ _))
  · have he : (fun a : Coeff 2 => hillFreeFullPeriodSequence a m)=fun _ => 0 := by
      funext a
      exact if_neg hm
    rw [he]
    exact analyticOnNhd_const

theorem analyticOnNhd_hillFreeFullPeriodSequence : AnalyticOnNhd ℂ hillFreeFullPeriodSequence univ := by
  intro a _
  let R := ‖a‖+1
  let M := Real.exp ((2/Real.pi^2)*R)*R
  have hc (m : ℤ) : AnalyticOnNhd ℂ (fun b : Coeff 2 => hillFreeFullPeriodSequence b m) (ball a 1) :=
    (analyticOnNhd_hillFreeFullPeriodCoordinate m).mono (subset_univ _)
  have hb (b : Coeff 2) (hb : b∈ball a 1) : ‖hillFreeFullPeriodSequence b‖≤M := by
    have hd : ‖b-a‖<1 := by simpa only [mem_ball,dist_eq_norm] using hb
    have hR : ‖b‖≤R := (norm_le_norm_sub_add b a).trans (by dsimp only [R];linarith)
    exact (norm_hillFreeFullPeriodSequence_le b).trans (mul_le_mul
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hR (by positivity))) hR (norm_nonneg _) (Real.exp_nonneg _))
  exact Coeff.analyticOnNhd_of_bounded_coordinatewise hillFreeFullPeriodSequence isOpen_ball hc M hb a (mem_ball_self (by norm_num))

theorem fderiv_hillFreeFullPeriodSequence_coordinate (a h : Coeff 2) (m : ℤ) :
    fderiv ℂ hillFreeFullPeriodSequence a h m=
      if 0<m ∧ m≠0 then -h m*hilbertWeightedProduct (hillFreeSeparatedWeight 0 m.toNat) a-
        a m*fderiv ℂ (hilbertWeightedProduct (hillFreeSeparatedWeight 0 m.toNat)) a h else 0 := by
  have hdiff := (analyticOnNhd_hillFreeFullPeriodSequence a (mem_univ _)).differentiableAt
  rw [Coeff.fderiv_apply_of_differentiableAt _ a h m hdiff]
  by_cases hm : 0<m ∧ m≠0
  · rw [if_pos hm]
    have he : (fun b : Coeff 2 => hillFreeFullPeriodSequence b m)=
        (fun b => -b m*hilbertWeightedProduct (hillFreeSeparatedWeight 0 m.toNat) b) := by
      funext b
      exact if_pos hm
    rw [he]
    have hA : HasFDerivAt (fun b : Coeff 2 => -b m) (-(lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 m)) a := by
      convert! ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 m).hasFDerivAt (x := a)).neg using 1
    have hB := (analyticOnNhd_hilbertWeightedProduct (hillFreeSeparatedWeight 0 m.toNat) a (mem_univ _)).differentiableAt.hasFDerivAt
    have hh := congrArg (fun T : Coeff 2 →L[ℂ] ℂ => T h) (hA.mul hB).fderiv
    have heval (b : Coeff 2) : lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 m b=b m := rfl
    simpa only [add_apply,smul_apply,neg_apply,heval,smul_eq_mul,neg_mul,sub_eq_add_neg,add_comm,Pi.mul_def,mul_comm] using hh
  · rw [if_neg hm]
    have he : (fun b : Coeff 2 => hillFreeFullPeriodSequence b m)=fun _ => 0 := by
      funext b
      exact if_neg hm
    rw [he]
    exact congrArg (fun T : Coeff 2 →L[ℂ] ℂ => T h) (hasFDerivAt_const (0:ℂ) a).fderiv

/-- The full free period derivative is a compact perturbation of minus
the full positive projection, including its original diagonal correction. -/
theorem isCompactOperator_fderiv_hillFreeFullPeriodSequence_add_projection (a : Coeff 2) :
    IsCompactOperator (fderiv ℂ hillFreeFullPeriodSequence a+Coeff.positiveDeletedProjection 2 0) := by
  let D := Coeff.multiplierCLM (p := 2) (hillFreePeriodDiagonalCorrection 0 a)
  let K := fderiv ℂ hillFreeFullPeriodSequence a+Coeff.positiveDeletedProjection 2 0+D
  let C := 2*Real.exp ((2/Real.pi^2)*(‖a‖+2))
  let b : Coeff 2 := (C : ℂ) • a
  have hK : IsCompactOperator K := by
    apply Coeff.isCompactOperator_of_rowMajorant (by norm_num : (2:ℝ≥0∞)≠⊤) K b
    intro m h
    change ‖(fderiv ℂ hillFreeFullPeriodSequence a h+Coeff.positiveDeletedProjection 2 0 h+D h) m‖≤‖b m‖*‖h‖
    simp only [lp.coeFn_add,Pi.add_apply]
    rw [fderiv_hillFreeFullPeriodSequence_coordinate,Coeff.positiveDeletedProjection_apply]
    have hD : D h m=(if 0<m ∧ m≠0 then hilbertWeightedProduct (hillFreeSeparatedWeight 0 m.toNat) a-1 else 0)*h m := rfl
    rw [hD]
    by_cases hm : 0<m ∧ m≠0
    · rw [if_pos hm,if_pos hm,if_pos hm]
      have he : -h m*hilbertWeightedProduct (hillFreeSeparatedWeight 0 m.toNat) a-
          a m*fderiv ℂ (hilbertWeightedProduct (hillFreeSeparatedWeight 0 m.toNat)) a h+
          h m+(hilbertWeightedProduct (hillFreeSeparatedWeight 0 m.toNat) a-1)*h m=
          -(a m*fderiv ℂ (hilbertWeightedProduct (hillFreeSeparatedWeight 0 m.toNat)) a h) := by ring
      rw [he,norm_neg,norm_mul]
      have hh := ((fderiv ℂ (hilbertWeightedProduct (hillFreeSeparatedWeight 0 m.toNat)) a).le_opNorm h).trans
        (mul_le_mul_of_nonneg_right (norm_fderiv_hilbertWeightedProduct_hillSeparated_le 0 m.toNat a) (norm_nonneg h))
      have hb : ‖b m‖=C*‖a m‖ := by
        simp only [b,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,norm_mul,norm_real,Real.norm_eq_abs,
          abs_of_nonneg (show 0≤C by dsimp only [C];positivity)]
      rw [hb]
      nlinarith [mul_le_mul_of_nonneg_left hh (norm_nonneg (a m))]
    · rw [if_neg hm,if_neg hm,if_neg hm,zero_mul,zero_add,add_zero,norm_zero]
      positivity
  have hD : IsCompactOperator D := isCompactOperator_hillFreePeriodDiagonalCorrection 0 a
  have he : fderiv ℂ hillFreeFullPeriodSequence a+Coeff.positiveDeletedProjection 2 0=K-D := by dsimp only [K];abel
  rw [he]
  exact hK.sub hD

end NLS.KdV
