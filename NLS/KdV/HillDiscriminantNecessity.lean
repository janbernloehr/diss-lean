import NLS.KdV.HillFullPeriod
import NLS.KdV.ClassicalHillMultipliers
import NLS.KdV.HillAnalytic

/-! # Physical periodic eigenvalues are zeros of the Hill radicand

For continuous period-one potentials, the actual periodic H2 eigenvector
has a nonzero initial state fixed by two unit propagations. This proves
vanishing of the actual period-one discriminant squared minus four,
including zero energy. The converse and equality of multiplicities remain
separate obligations.
-/

noncomputable section
open Set MeasureTheory Filter
open NLS.LinearVolterra
namespace NLS.KdV

/-- A nonzero physical eigenvector cannot have both initial position and
initial derivative zero. The proof uses both halves of the full period. -/
theorem physicalHillEigenvector_initial_ne_zero (Q : C(AddCircle (2 : ℝ), ℂ))
    (lambda : ℂ) (f : HillSobolevDomain) (hf : f ≠ 0)
    (he : physicalHillOperator (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ Q) f =
      lambda • ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ (hillRepresentative f)) :
    hillPhysicalState f 0 ≠ 0 := by
  intro hzero
  have hu := physicalHillEigenvector_eq_classicalFlow Q lambda f he
  change EqOn (hillPhysicalState f)
    (classicalHillFlow (hillUnitPotentialCurve Q) lambda (hillPhysicalState f 0)) (Icc 0 1) at hu
  rw [hzero] at hu
  have h1 : hillPhysicalState f 1 = 0 := by
    rw [hu (by norm_num), classicalHillFlow_zero_initial _ _ ⟨1,by norm_num⟩]
  have hs := physicalHillEigenvector_secondFlow Q lambda f he
  rw [h1] at hs
  have hz (x : ℝ) (hx : x ∈ Ioc (0 : ℝ) 2) : hillPhysicalState f x = 0 := by
    by_cases hx1 : x ≤ 1
    · rw [hu ⟨hx.1.le,hx1⟩, classicalHillFlow_zero_initial _ _ ⟨x,hx.1.le,hx1⟩]
    · have hxi : x-1 ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith [hx.2]⟩
      have h := hs hxi
      dsimp only at h
      rw [sub_add_cancel, classicalHillFlow_zero_initial _ _ ⟨x-1,hxi⟩] at h
      exact h
  have hae : (fun x : ℝ => hillRepresentative f (x : AddCircle (2 : ℝ)))
      =ᵐ[volume.restrict (Ioc 0 2)] (fun _ => (0 : ℂ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact congrArg Prod.fst (hz x hx)
  apply hf
  apply Subtype.ext
  funext k
  change f.val k = 0
  rw [← hillRepresentative_coefficient, ← Fourier.periodTwoCoefficient_circle,
    Fourier.periodTwoCoefficient_eq_fourierCoeffOn]
  have h := congrFun (fourierCoeffOn_congr_ae (by norm_num : (0 : ℝ) < 2) hae) k
  simpa only [fourierCoeffOn_eq_integral, smul_zero, intervalIntegral.integral_zero] using h

/-- The full periodic weak eigen-equation implies the actual period-one
Hill characteristic equation, with no nonzero-energy restriction. -/
theorem physicalHillEigenvector_discriminant_zero (Q : C(AddCircle (2 : ℝ), ℂ))
    (hQ : Function.Periodic (fun x : ℝ => Q (x : AddCircle (2 : ℝ))) 1)
    (lambda : ℂ) (f : HillSobolevDomain) (hf : f ≠ 0)
    (he : physicalHillOperator (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ Q) f =
      lambda • ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ (hillRepresentative f)) :
    classicalHillDiscriminant (hillUnitPotentialCurve Q) lambda ^ 2-4 = 0 := by
  have hcurve : hillSecondPotentialCurve Q = hillUnitPotentialCurve Q := by
    apply ContinuousMap.ext
    intro t
    exact hQ (t : ℝ)
  have hfull := physicalHillEigenvector_fullPeriod Q lambda f he
  rw [hcurve] at hfull
  exact classicalHillRadicand_zero_of_double_fixed _ lambda (hillPhysicalState f 0)
    (physicalHillEigenvector_initial_ne_zero Q lambda f hf he) hfull

/-- The unit-weight Hill potential is the actual continuous Fourier input. -/
def hillContinuousCoefficients (Q : C(AddCircle (2 : ℝ), ℂ)) :
    WeightedCoeff SpectralWeight.one.toWeight 2 :=
  (WeightedCoeff.weightIsometry SpectralWeight.one.toWeight 2).symm (Fourier.continuousFourierCLM Q)

@[simp] theorem hillContinuousCoefficients_apply (Q : C(AddCircle (2 : ℝ), ℂ)) (k : ℤ) :
    (hillContinuousCoefficients Q).val k = fourierCoeff Q k := by
  change Fourier.continuousFourierCLM Q k/(SpectralWeight.one k : ℂ) = _
  rw [SpectralWeight.one_apply, Complex.ofReal_one, div_one, Fourier.continuousFourierCLM_apply]

theorem l2Synthesis_hillContinuousCoefficients (Q : C(AddCircle (2 : ℝ), ℂ)) :
    Fourier.l2Synthesis (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) =
      ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ Q := by
  have he : SpectralWeight.one.toCoeff (hillContinuousCoefficients Q) = Fourier.continuousFourierCLM Q := by
    ext k
    simp only [SpectralWeight.toCoeff_apply, hillContinuousCoefficients_apply,
      Fourier.continuousFourierCLM_apply]
  rw [he]
  exact Fourier.l2Synthesis.apply_symm_apply _

/-- The actual high-strip Fourier reduction zero implies vanishing of
the actual scalar discriminant for the same continuous physical potential. -/
theorem hillReduced_zero_implies_classicalDiscriminant_zero
    (Q : C(AddCircle (2 : ℝ), ℂ))
    (hQ : Function.Periodic (fun x : ℝ => Q (x : AddCircle (2 : ℝ))) 1)
    (n : ℕ) (hn : 1 ≤ n) (lambda : ℂ) (hz : lambda ∈ reducedHillStrip n)
    (hcut : 8*‖hillContinuousCoefficients Q‖ ≤ (n : ℝ))
    (hd : hillReducedDeterminant SpectralWeight.one n (hillContinuousCoefficients Q,lambda) = 0) :
    classicalHillDiscriminant (hillUnitPotentialCurve Q) lambda ^ 2-4 = 0 := by
  have hd' : (hillReducedOperator SpectralWeight.one (hillContinuousCoefficients Q) n hn lambda hz hcut).toLinearMap.det = 0 :=
    (hillReducedDeterminant_eq SpectralWeight.one n hn (hillContinuousCoefficients Q,lambda) hz hcut).symm.trans hd
  obtain ⟨f, hf, he⟩ := (hillReduced_det_eq_zero_iff_physicalEigenvector
    (hillContinuousCoefficients Q) n hn lambda hz hcut).mp hd'
  rw [l2Synthesis_hillContinuousCoefficients] at he
  exact physicalHillEigenvector_discriminant_zero Q hQ lambda f hf he

end NLS.KdV
