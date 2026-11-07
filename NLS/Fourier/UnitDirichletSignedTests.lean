import NLS.Fourier.UnitIntervalDirichletIdentification
import NLS.Fourier.SobolevParitySynthesis
import NLS.KdV.SingularHillRieszContinuous

/-! SAME-PARITY extensions of EVERY original native Dirichlet test.
The signed extension equals the original test at every unit-interval point. -/
noncomputable section
open Set
namespace NLS.Fourier
open PeriodicFourierLebesgue

/-- The unit-period native insertion has the IDENTICAL physical representative. -/
theorem unitDirichletOriginalH1_representative (h : UnitDirichletH1) (x : ℝ) :
    NLS.KdV.singularHillContinuousDomainInclusion (unitDirichletOriginalH1 h) (x : AddCircle (2:ℝ)) =
      unitDirichletRepresentative h x := by
  change sobolevSynthesis (by simp) ((PeriodicFourierLebesgue.sobolevCoefficients 1 2)
    ((PeriodicFourierLebesgue.sobolevCoefficients 1 2).symm (Coeff.periodDoubleSobolev h.val)))
      (x : AddCircle (2:ℝ)) = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact congrArg (fun F : C(AddCircle (2:ℝ),ℂ) => F (x : AddCircle (2:ℝ)))
    (periodOneSobolevSynthesis_eq h.val).symm

/-- Both zero traces allow any integer parity in the signed H1 extension. -/
theorem unitDirichletRepresentative_signed_endpoint (r : ℤ) (h : UnitDirichletH1) :
    unitDirichletRepresentative h 1 = wave r 1*unitDirichletRepresentative h 0 := by simp

/-- The original full period-two H1 test with the requested parity. -/
def unitDirichletSignedH1 (r : ℤ) (h : UnitDirichletH1) : FourierLebesgueSpace (2:ℝ) 1 2 :=
  (PeriodicFourierLebesgue.sobolevCoefficients 1 2).symm (signedSobolevCoefficients r (unitDirichletRepresentative h)
    (unitDirichletRepresentative_mem_domain h).1 (unitDirichletRepresentative_signed_endpoint r h))

/-- Its exact continuous representative reconstructs both halves and their join. -/
theorem unitDirichletSignedH1_representative (r : ℤ) (h : UnitDirichletH1)
    (x : ℝ) (hx : x ∈ Icc (0:ℝ) 2) :
    NLS.KdV.singularHillContinuousDomainInclusion (unitDirichletSignedH1 r h) (x : AddCircle (2:ℝ)) =
      signedDouble (wave r 1) (unitDirichletRepresentative h) x := by
  change sobolevSynthesis (by simp) ((PeriodicFourierLebesgue.sobolevCoefficients 1 2)
    ((PeriodicFourierLebesgue.sobolevCoefficients 1 2).symm _)) (x : AddCircle (2:ℝ)) = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact sobolevSynthesis_signedSobolevCoefficients r _ _ _ hx

/-- The signed original test equals the native interval test including BOTH traces. -/
theorem unitDirichletSignedH1_on_unit (r : ℤ) (h : UnitDirichletH1)
    (x : ℝ) (hx : x ∈ Icc (0:ℝ) 1) :
    NLS.KdV.singularHillContinuousDomainInclusion (unitDirichletSignedH1 r h) (x : AddCircle (2:ℝ)) =
      unitDirichletRepresentative h x := by
  rw [unitDirichletSignedH1_representative r h x ⟨hx.1,hx.2.trans (by norm_num)⟩,
    signedDouble_left _ _ hx.2]

/-- Every original signed test has the requested global translation multiplier. -/
theorem unitDirichletSignedH1_translate_one (r : ℤ) (h : UnitDirichletH1) (x : ℝ) :
    NLS.KdV.singularHillContinuousDomainInclusion (unitDirichletSignedH1 r h) ((x+1:ℝ) : AddCircle (2:ℝ)) =
      wave r 1*NLS.KdV.singularHillContinuousDomainInclusion (unitDirichletSignedH1 r h) (x : AddCircle (2:ℝ)) := by
  change sobolevSynthesis (by simp) ((PeriodicFourierLebesgue.sobolevCoefficients 1 2)
    ((PeriodicFourierLebesgue.sobolevCoefficients 1 2).symm _)) ((x+1:ℝ) : AddCircle (2:ℝ)) =
      wave r 1*sobolevSynthesis (by simp) ((PeriodicFourierLebesgue.sobolevCoefficients 1 2)
        ((PeriodicFourierLebesgue.sobolevCoefficients 1 2).symm _)) (x : AddCircle (2:ℝ))
  simp only [LinearIsometryEquiv.apply_symm_apply]
  exact sobolevSynthesis_translate_one_of_parity r _
    (signedSobolevCoefficients_parity r _ _ _) x

end NLS.Fourier
