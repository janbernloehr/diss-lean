import NLS.KdV.HillForwardSobolevBound
import NLS.Fourier.PeriodOneFourierUniqueness

/-! # Exact physical Sobolev norms, actual positive-index action series, Arnold normalization and representative uniqueness. -/

noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory Filter Topology NLS.Fourier NLS.ZakharovShabat
open scoped ComplexConjugate
namespace NLS.KdV
def hillSourceSobolevNorm (M j : ℕ) (hj : j ≤ M) (a : ScalarSobolev M) : ℝ :=
  ‖hillScalarToNativeInteger j (hillScalarSobolevLower M j hj a)‖

theorem hillSourceSobolevNorm_nonneg (M j : ℕ) (hj : j ≤ M) (a : ScalarSobolev M) :
    0 ≤ hillSourceSobolevNorm M j hj a := norm_nonneg _

theorem hillSourceSobolevNorm_sq (M j : ℕ) (hj : j ≤ M) (a : ScalarSobolev M) :
    HasSum (fun k : ℤ => (1+|2*Real.pi*(k : ℝ)|)^(2*j)*‖a.val k‖^2)
      ((hillSourceSobolevNorm M j hj a)^2) := by
  have h := hillPeriodOne_sobolev_norm_sq j (hillScalarToNativeInteger j (hillScalarSobolevLower M j hj a))
  simp only [hillScalarToNativeInteger_apply,hillScalarSobolevLower_apply] at h
  convert! h using 1

def hillPhysicalSobolevActionMass (M : ℕ) (hM : 1 ≤ M) (a : ScalarSobolev M)
    (hreal : ∀ x : AddCircle (2 : ℝ), (hillSharedPhysicalPotential M hM a x).im = 0)
    (j : ℕ) : ℝ :=
  ∑' n : ℕ, (2*Real.pi*(n+1 : ℕ))^(2*j+1)*
    hillRealGapIntegral (hillContinuousCoefficients (hillSharedPhysicalPotential M hM a))
      (hillContinuousCoefficients_mem_even _ (hillSharedPhysicalPotential_periodic M hM a))
      (isRealHillPotential_hillContinuousCoefficients _ hreal) (n+1) 0

def hillPhysicalSobolevNative (M : ℕ) (hM : 1 ≤ M) (a : ScalarSobolev M)
    (hreal : ∀ x : AddCircle (2 : ℝ), (hillSharedPhysicalPotential M hM a x).im = 0) :
    RealHillWeightedPotential (hillIntegerWeight M) :=
  ⟨hillScalarToNativeInteger M a,isReal_hillScalarToNativeInteger M a
    (hillSharedPhysicalPotential_real_coefficients M hM a hreal)⟩

theorem hillPhysicalSobolevNative_mean_zero (M : ℕ) (hM : 1 ≤ M) (a : ScalarSobolev M)
    (hreal : ∀ x : AddCircle (2 : ℝ), (hillSharedPhysicalPotential M hM a x).im = 0)
    (hmean : (∫ x in (0 : ℝ)..1, hillSharedPhysicalPotential M hM a (x : AddCircle (2 : ℝ))) = 0) :
    (hillPhysicalSobolevNative M hM a hreal).val.val 0 = 0 := by
  change (hillScalarToNativeInteger M a).val 0 = 0
  rw [hillScalarToNativeInteger_apply]
  exact (hillSharedPhysicalPotential_mean M hM a).symm.trans hmean

theorem hasSum_hillPhysicalSobolevActions (M : ℕ) (hM : 1 ≤ M) (a : ScalarSobolev M)
    (hreal : ∀ x : AddCircle (2 : ℝ), (hillSharedPhysicalPotential M hM a x).im = 0)
    (j : ℕ) (hj : j ≤ M) :
    HasSum (fun n : ℕ => (2*Real.pi*(n+1 : ℕ))^(2*j+1)*
      hillRealGapIntegral (hillContinuousCoefficients (hillSharedPhysicalPotential M hM a))
        (hillContinuousCoefficients_mem_even _ (hillSharedPhysicalPotential_periodic M hM a))
        (isRealHillPotential_hillContinuousCoefficients _ hreal) (n+1) 0)
      (hillNativeActionMass M j (hillPhysicalSobolevNative M hM a hreal)) := by
  let p := hillPhysicalSobolevNative M hM a hreal
  have h := hasSum_hillNativePositiveActions M j hj p
  have hc := hillContinuousCoefficients_sharedPhysical M hM a
  have he (n : ℕ) :
      hillRealGapIntegral (hillPeriodOneUnitPotential (hillIntegerWeight M) p.val)
        (hillPeriodOneUnitPotential_even (hillIntegerWeight M) p.val)
        (hillPeriodOneUnitPotential_real (hillIntegerWeight M) p.val p.property) (n+1) 0 =
      hillRealGapIntegral (hillContinuousCoefficients (hillSharedPhysicalPotential M hM a))
        (hillContinuousCoefficients_mem_even _ (hillSharedPhysicalPotential_periodic M hM a))
        (isRealHillPotential_hillContinuousCoefficients _ hreal) (n+1) 0 :=
    hillRealGapIntegral_congr _ _ _ _ _ _ hc.symm (n+1) 0
  have hf : (fun n : ℕ => (2*Real.pi*(n+1 : ℕ))^(2*j+1)*
      hillRealGapIntegral (hillPeriodOneUnitPotential (hillIntegerWeight M) p.val)
        (hillPeriodOneUnitPotential_even (hillIntegerWeight M) p.val)
        (hillPeriodOneUnitPotential_real (hillIntegerWeight M) p.val p.property) (n+1) 0) =
      (fun n : ℕ => (2*Real.pi*(n+1 : ℕ))^(2*j+1)*
      hillRealGapIntegral (hillContinuousCoefficients (hillSharedPhysicalPotential M hM a))
        (hillContinuousCoefficients_mem_even _ (hillSharedPhysicalPotential_periodic M hM a))
        (isRealHillPotential_hillContinuousCoefficients _ hreal) (n+1) 0) := by
    funext n
    rw [he n]
  rw [hf] at h
  exact h

theorem hillPhysicalSobolevActionMass_eq_native (M : ℕ) (hM : 1 ≤ M) (a : ScalarSobolev M)
    (hreal : ∀ x : AddCircle (2 : ℝ), (hillSharedPhysicalPotential M hM a x).im = 0)
    (j : ℕ) (hj : j ≤ M) :
    hillPhysicalSobolevActionMass M hM a hreal j =
      hillNativeActionMass M j (hillPhysicalSobolevNative M hM a hreal) :=
  (hasSum_hillPhysicalSobolevActions M hM a hreal j hj).tsum_eq

theorem hillNativeIntegerLower_scalarToNative (M j : ℕ) (hj : j ≤ M) (a : ScalarSobolev M) :
    hillNativeIntegerLower M j hj (hillScalarToNativeInteger M a) =
      hillScalarToNativeInteger j (hillScalarSobolevLower M j hj a) := by
  apply Subtype.ext
  funext k
  simp only [hillNativeIntegerLower_apply,hillScalarToNativeInteger_apply,hillScalarSobolevLower_apply]

theorem periodOneCoefficient_hillSharedPhysicalPotential (M : ℕ) (hM : 1 ≤ M)
    (a : ScalarSobolev M) (k : ℤ) :
    periodOneCoefficient (fun x : ℝ => hillSharedPhysicalPotential M hM a (x : AddCircle (2 : ℝ))) k = a.val k := by
  exact (periodOneCoefficient_periodOneSobolevSynthesis (hierarchySobolevToScalarDomain M hM a) k).trans
    (hierarchySobolevToScalarDomain_apply M hM a k)

theorem hillPhysicalSobolevAction_arnold (M : ℕ) (hM : 1 ≤ M) (a : ScalarSobolev M)
    (hreal : ∀ x : AddCircle (2 : ℝ), (hillSharedPhysicalPotential M hM a x).im = 0)
    (n : ℕ) (hn : 1 ≤ n) :
    let Q := hillSharedPhysicalPotential M hM a
    let q := hillContinuousCoefficients Q
    let hq := hillContinuousCoefficients_mem_even Q (hillSharedPhysicalPotential_periodic M hM a)
    let hr := isRealHillPotential_hillContinuousCoefficients Q hreal
    (hillRealGapIntegral q hq hr n 0 : ℂ) = (Real.pi : ℂ)⁻¹ *
      ∮ z in C((hillRealGapCenter q hq hr n : ℂ),hillRealGapHalfLength q hq hr n+hillRealGapCollar q hq hr n),
        z*deriv (hillL2Discriminant (SpectralWeight.one.toCoeff q)) z /
          hillL2RealCutRoot (SpectralWeight.one.toCoeff q) z := by
  dsimp only
  rw [← hillL2RealContourMoment_eq_gapIntegral _ _ _ n hn 0]
  simpa only [Nat.cast_zero,zero_add,one_mul,pow_one] using
    hillL2RealContourMoment_arnold_level
      (hillContinuousCoefficients (hillSharedPhysicalPotential M hM a))
      (hillContinuousCoefficients_mem_even _ (hillSharedPhysicalPotential_periodic M hM a))
      (isRealHillPotential_hillContinuousCoefficients _ hreal) n hn 0

theorem hillSharedPhysicalPotential_eq_of_coefficients (M : ℕ) (hM : 1 ≤ M)
    (a : ScalarSobolev M) (Q : C(AddCircle (2 : ℝ),ℂ))
    (hper : Function.Periodic (fun x : ℝ => Q (x : AddCircle (2 : ℝ))) 1)
    (hcoeff : ∀ k : ℤ, a.val k = periodOneCoefficient (fun x : ℝ => Q (x : AddCircle (2 : ℝ))) k) :
    hillSharedPhysicalPotential M hM a = Q := by
  have h := periodOneSobolevSynthesis_eq_of_coefficients (hierarchySobolevToScalarDomain M hM a)
    (fun x : ℝ => Q (x : AddCircle (2 : ℝ))) (by fun_prop) hper
    (fun k => (hierarchySobolevToScalarDomain_apply M hM a k).trans (hcoeff k))
  ext x
  induction x using QuotientAddGroup.induction_on with
  | H t => exact congrFun h t

def hillContinuousActionMass (Q : C(AddCircle (2 : ℝ),ℂ))
    (hper : Function.Periodic (fun x : ℝ => Q (x : AddCircle (2 : ℝ))) 1)
    (hreal : ∀ x : AddCircle (2 : ℝ), (Q x).im = 0) (j : ℕ) : ℝ :=
  ∑' n : ℕ, (2*Real.pi*(n+1 : ℕ))^(2*j+1)*
    hillRealGapIntegral (hillContinuousCoefficients Q) (hillContinuousCoefficients_mem_even Q hper)
      (isRealHillPotential_hillContinuousCoefficients Q hreal) (n+1) 0

end NLS.KdV
