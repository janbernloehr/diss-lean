import NLS.KdV.ClassicalNormalizedZeroMap
import NLS.SequenceSpaces.CoordinateQuadraticDerivative
import NLS.ComplexAnalysis.AnalyticImplicitBanachRoot

/-! # Simultaneous analytic solutions of the normalized zero equation

The free unknown derivative is the actual identity on l2. The analytic
Banach implicit function theorem therefore constructs one l2 displacement
sequence for all positive indices other than the selected numerator mode.
-/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
namespace NLS.KdV
namespace ClassicalAllContourPeriodData
variable {N : ℕ} {V : Set (NLS.LinearVolterra.Curve ℂ)} {A : ℝ}
variable (D : ClassicalAllContourPeriodData N V A)
include D

theorem candidateRow_omitted_coordinate (n k : ℕ+)
    (t : NLS.Coeff 2 × NLS.LinearVolterra.Curve ℂ) (ht : t ∈ classicalHillCandidateDomain V) :
    classicalHillCandidateRow N n k t (n : ℤ) = 0 := by
  rw [(D.candidateRow_spec n k).1 t ht,classicalHillCandidateRowCoordinates,dif_pos (by exact_mod_cast n.pos)]
  have hi : positiveIntegerIndex (n : ℤ) (by exact_mod_cast n.pos) = n := by
    apply Subtype.ext
    exact Int.toNat_natCast _
  rw [hi,if_pos (Or.inr rfl)]

theorem zeroBracket_free
    (Q : NLS.LinearVolterra.Curve ℂ → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (hQ0 : Q 0 = ContinuousLinearMap.id ℂ (NLS.Coeff 2)) (n k : ℕ+) (x : NLS.Coeff 2)
    (hx : x ∈ ball (0 : NLS.Coeff 2) (Real.pi/16)) :
    classicalHillZeroBracket N Q n k (x,0) = 1 := by
  have he : classicalHillZeroCoefficients Q n 0 = (n : ℂ) • lp.single 2 (n : ℤ) 1 := by
    rw [classicalHillZeroCoefficients,hQ0,ContinuousLinearMap.id_apply]
  have hz := D.candidateRow_omitted_coordinate n k (x,0) ⟨hx,D.zero_mem⟩
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast n.ne_zero
  simp only [classicalHillZeroBracket,he,NLS.Coeff.dualPairing_apply,lp.coeFn_smul,
    Pi.smul_apply,smul_eq_mul,lp.single_apply,Pi.single_apply]
  simp [hz,hn0]

theorem zeroMap_auxiliary
    (Q : NLS.LinearVolterra.Curve ℂ → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (hQa : AnalyticOnNhd ℂ Q V) (hQ : ∀ q ∈ V, ‖Q q‖ ≤ 2) (n : ℕ+)
    (t : NLS.Coeff 2 × NLS.LinearVolterra.Curve ℂ) (ht : t ∈ classicalHillCandidateDomain V)
    (j : ℤ) (hj : j ≤ 0 ∨ j = (n : ℤ)) :
    classicalHillZeroMap N Q n t j = t.1 j := by
  rw [(D.zeroMap_spec Q hQa hQ n).1 t ht j,classicalHillZeroCoordinates]
  by_cases hj0 : 0 < j
  · rw [dif_pos hj0]
    have hjn : j = (n : ℤ) := hj.resolve_left (by omega)
    have he : positiveIntegerIndex j hj0 = n := by
      apply Subtype.ext
      change j.toNat = (n : ℕ)
      rw [hjn,Int.toNat_natCast]
    rw [if_pos he]
  · rw [dif_neg hj0]

theorem zeroMap_free_positive
    (Q : NLS.LinearVolterra.Curve ℂ → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (hQa : AnalyticOnNhd ℂ Q V) (hQ : ∀ q ∈ V, ‖Q q‖ ≤ 2)
    (hQ0 : Q 0 = ContinuousLinearMap.id ℂ (NLS.Coeff 2)) (n k : ℕ+) (hkn : k ≠ n)
    (x : NLS.Coeff 2) (hx : x ∈ ball (0 : NLS.Coeff 2) (Real.pi/16)) :
    classicalHillZeroMap N Q n (x,0) (k : ℤ) = x (k : ℤ)*(1+x (k : ℤ)/(2*(Real.pi : ℂ)*(k : ℂ))) := by
  rw [(D.zeroMap_spec Q hQa hQ n).1 (x,0) ⟨hx,D.zero_mem⟩,classicalHillZeroCoordinates,
    dif_pos (by exact_mod_cast k.pos)]
  have hi : positiveIntegerIndex (k : ℤ) (by exact_mod_cast k.pos) = k := by
    apply Subtype.ext
    exact Int.toNat_natCast _
  rw [hi,if_neg hkn]
  have hknI : (k : ℤ) ≠ (n : ℤ) := by exact_mod_cast hkn
  have hcoef : classicalHillZeroCoefficients Q n 0 (k : ℤ) = 0 := by
    simp only [classicalHillZeroCoefficients,hQ0,ContinuousLinearMap.id_apply,lp.coeFn_smul,
      Pi.smul_apply,smul_eq_mul,lp.single_apply,Pi.single_apply,if_neg hknI,mul_zero]
  have hfreq : classicalHillCriticalFrequency N k 0 = (Real.pi : ℂ)*(k : ℂ) := by
    rw [classicalHillCriticalFrequency,D.critical_free,sqrt_freeHillEnergy]
    ring
  rw [hcoef,mul_zero,zero_add,D.zeroBracket_free Q hQ0 n k x hx,mul_one,hfreq]
  congr 2
  ring

theorem zeroMap_free_derivative
    (Q : NLS.LinearVolterra.Curve ℂ → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (hQa : AnalyticOnNhd ℂ Q V) (hQ : ∀ q ∈ V, ‖Q q‖ ≤ 2)
    (hQ0 : Q 0 = ContinuousLinearMap.id ℂ (NLS.Coeff 2)) (n : ℕ+) :
    fderiv ℂ (fun x : NLS.Coeff 2 => classicalHillZeroMap N Q n (x,0)) 0 =
      ContinuousLinearMap.id ℂ (NLS.Coeff 2) := by
  have h00 : ((0 : NLS.Coeff 2),(0 : NLS.LinearVolterra.Curve ℂ)) ∈ classicalHillCandidateDomain V :=
    ⟨mem_ball_self (by positivity),D.zero_mem⟩
  have hF := (D.zeroMap_spec Q hQa hQ n).2 _ h00
  have hslice := hF.comp (f := fun x : NLS.Coeff 2 => (x,(0 : NLS.LinearVolterra.Curve ℂ)))
    (analyticAt_id.prod analyticAt_const)
  apply NLS.Coeff.fderiv_eq_id_of_coordinate_quadratic_germs
    (fun x : NLS.Coeff 2 => classicalHillZeroMap N Q n (x,0))
    (by simpa only [Function.comp_def] using! hslice.differentiableAt)
  intro j
  by_cases hj : 0 < j
  · let k := positiveIntegerIndex j hj
    have hkj : (k : ℤ) = j := positiveIntegerIndex_int j hj
    by_cases hkn : k = n
    · refine ⟨0,?_⟩
      filter_upwards [isOpen_ball.mem_nhds (mem_ball_self (by positivity : 0 < Real.pi/16) : (0 : NLS.Coeff 2) ∈ ball 0 (Real.pi/16))] with x hx
      have hjn : j = (n : ℤ) := by rw [← hkj,hkn]
      simpa only [zero_mul,add_zero] using D.zeroMap_auxiliary Q hQa hQ n (x,0) ⟨hx,D.zero_mem⟩ j (Or.inr hjn)
    · refine ⟨(2*(Real.pi : ℂ)*(k : ℂ))⁻¹,?_⟩
      filter_upwards [isOpen_ball.mem_nhds (mem_ball_self (by positivity : 0 < Real.pi/16) : (0 : NLS.Coeff 2) ∈ ball 0 (Real.pi/16))] with x hx
      have he := D.zeroMap_free_positive Q hQa hQ hQ0 n k hkn x hx
      rw [hkj] at he
      rw [he]
      simp only [div_eq_mul_inv]
      ring
  · refine ⟨0,?_⟩
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self (by positivity : 0 < Real.pi/16) : (0 : NLS.Coeff 2) ∈ ball 0 (Real.pi/16))] with x hx
    simpa only [zero_mul,add_zero] using D.zeroMap_auxiliary Q hQa hQ n (x,0) ⟨hx,D.zero_mem⟩ j (Or.inl (by omega))

/-- One analytic l2 displacement solves every retained filled zero
equation on a common potential neighborhood for the chosen omitted n. -/
theorem exists_analytic_normalized_root_displacements
    (Q : NLS.LinearVolterra.Curve ℂ → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (hQa : AnalyticOnNhd ℂ Q V) (hQ : ∀ q ∈ V, ‖Q q‖ ≤ 2)
    (hQ0 : Q 0 = ContinuousLinearMap.id ℂ (NLS.Coeff 2)) (n : ℕ+) :
    ∃ s : NLS.LinearVolterra.Curve ℂ → NLS.Coeff 2, ∃ U : Set (NLS.LinearVolterra.Curve ℂ),
      U ⊆ V ∧ IsOpen U ∧ 0 ∈ U ∧ s 0 = 0 ∧ AnalyticOnNhd ℂ s U ∧
      ∀ q ∈ U, ‖s q‖ < Real.pi/16 ∧ classicalHillZeroMap N Q n (s q,q) = 0 := by
  have h00 : ((0 : NLS.Coeff 2),(0 : NLS.LinearVolterra.Curve ℂ)) ∈ classicalHillCandidateDomain V :=
    ⟨mem_ball_self (by positivity),D.zero_mem⟩
  have hF := (D.zeroMap_spec Q hQa hQ n).2 _ h00
  have hzero : classicalHillZeroMap N Q n (0,0) = 0 := by
    ext j
    by_cases hj : 0 < j
    · let k := positiveIntegerIndex j hj
      have hkj : (k : ℤ) = j := positiveIntegerIndex_int j hj
      by_cases hkn : k = n
      · have hjn : j = (n : ℤ) := by rw [← hkj,hkn]
        simpa using D.zeroMap_auxiliary Q hQa hQ n (0,0) h00 j (Or.inr hjn)
      · have hh := D.zeroMap_free_positive Q hQa hQ hQ0 n k hkn 0 (mem_ball_self (by positivity))
        simpa only [hkj,lp.coeFn_zero,Pi.zero_apply,zero_mul] using hh
    · simpa using D.zeroMap_auxiliary Q hQa hQ n (0,0) h00 j (Or.inl (by omega))
  have hd := hF.differentiableAt.hasFDerivAt.comp
    (f := fun x : NLS.Coeff 2 => (x,(0 : NLS.LinearVolterra.Curve ℂ))) 0
    (hasFDerivAt_prodMk_left (0 : NLS.Coeff 2) (0 : NLS.LinearVolterra.Curve ℂ))
  have hbij : Function.Bijective ((fderiv ℂ (classicalHillZeroMap N Q n) (0,0)).comp
      (ContinuousLinearMap.inl ℂ (NLS.Coeff 2) (NLS.LinearVolterra.Curve ℂ))) := by
    have hd' : fderiv ℂ (fun x : NLS.Coeff 2 => classicalHillZeroMap N Q n (x,0)) 0 =
        (fderiv ℂ (classicalHillZeroMap N Q n) (0,0)).comp
          (ContinuousLinearMap.inl ℂ (NLS.Coeff 2) (NLS.LinearVolterra.Curve ℂ)) := by
      simpa only [Function.comp_def] using! hd.fderiv
    rw [← hd',D.zeroMap_free_derivative Q hQa hQ hQ0 n]
    exact Function.bijective_id
  obtain ⟨s,hsa,hs0,hroot⟩ := exists_analytic_implicitBanachRoot (classicalHillZeroMap N Q n) 0 0 hF hzero hbij
  have hsmall : ∀ᶠ q in 𝓝 (0 : NLS.LinearVolterra.Curve ℂ), ‖s q‖ < Real.pi/16 :=
    hsa.continuousAt.norm.eventually (gt_mem_nhds (by
      change ‖s 0‖ < Real.pi/16
      rw [hs0,norm_zero]
      positivity))
  obtain ⟨r,hr,hball⟩ := hsa.exists_ball_analyticOnNhd
  obtain ⟨W,hWsub,hW,h0W⟩ := _root_.mem_nhds_iff.mp (hsmall.and hroot)
  refine ⟨s,(V ∩ W) ∩ ball 0 r,fun _ hq => hq.1.1,(D.isOpen.inter hW).inter isOpen_ball,
    ⟨⟨D.zero_mem,h0W⟩,mem_ball_self hr⟩,hs0,hball.mono inter_subset_right,?_⟩
  intro q hq
  exact hWsub hq.1.2

end ClassicalAllContourPeriodData
end NLS.KdV
