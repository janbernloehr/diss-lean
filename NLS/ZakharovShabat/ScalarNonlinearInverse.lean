import NLS.ZakharovShabat.ScalarNonlinearLinearization

/-! # global scalar nonlinear Fourier inverse

The scalar map is a global real analytic homeomorphism between original physical L2 and complex l2. Both inverse identities, exact norm preservation and the inverse Fourier differential retain the scalar normalization.
-/

noncomputable section
open Set MeasureTheory Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Read the original scalar class from a physical real pair. -/
def scalarPhysicalProjectionCLM : physicalRealSubmodule →L[ℝ] IntervalL2 :=
  (WithLp.fstL 2 ℝ IntervalL2 IntervalL2).comp physicalRealSubmodule.subtypeL

@[simp] theorem scalarPhysicalProjection_input (u : IntervalL2) :
    scalarPhysicalProjectionCLM (scalarPhysicalRealInput u) = u := rfl

/-- Every physical real pair is reconstructed from its scalar component. -/
@[simp] theorem scalarPhysicalInput_projection (u : physicalRealSubmodule) :
    scalarPhysicalRealInput (scalarPhysicalProjectionCLM u) = u := by
  apply Subtype.ext
  apply WithLp.ofLp_injective
  apply Prod.ext
  · rfl
  · change star u.val.ofLp.1 = u.val.ofLp.2
    apply Lp.ext
    have hu := (mem_physicalRealSubmodule u.val).mp u.property
    exact (Lp.coeFn_star u.val.ofLp.1).trans hu.symm

/-- Recover the native rectangular target from one normalized complex sequence. -/
def scalarPhysicalTargetCLM : Coeff 2 →L[ℝ] PhysicalRealBirkhoffTarget :=
  physicalRealTargetEquiv.symm.toContinuousLinearMap.comp
    (Birkhoff.decodeReal.comp
      ((ContinuousLinearMap.id ℝ (Coeff 2)).prod (starL' ℝ : Coeff 2 ≃L[ℝ] Coeff 2).toContinuousLinearMap))

@[simp] theorem normalizedScalar_target (a : Coeff 2) :
    normalizedPhysicalScalarCoordinate (scalarPhysicalTargetCLM a) = a := by
  have h : Birkhoff.IsConjugatePair (a,star a) := by
    intro n
    exact lp.star_apply a n
  have he := Birkhoff.encodeReal_decodeReal (a,star a) h
  exact congrArg Prod.fst he

@[simp] theorem scalarTarget_normalized (z : PhysicalRealBirkhoffTarget) :
    scalarPhysicalTargetCLM (normalizedPhysicalScalarCoordinate z) = z := by
  have h := Birkhoff.encodeReal_real z.ofLp
  have he : ((Birkhoff.encodeReal z.ofLp).1, star (Birkhoff.encodeReal z.ofLp).1) =
      Birkhoff.encodeReal z.ofLp := by
    apply Prod.ext
    · rfl
    · ext n
      exact (lp.star_apply _ n).trans (h n).symm
  apply WithLp.ofLp_injective
  change Birkhoff.decodeReal ((Birkhoff.encodeReal z.ofLp).1,star (Birkhoff.encodeReal z.ofLp).1) = z.ofLp
  rw [he,Birkhoff.decodeReal_encodeReal]

/-- The inverse nonlinear Fourier transform returns an original scalar L2 class. -/
def scalarNonlinearFourierInverse (a : Coeff 2) : IntervalL2 :=
  scalarPhysicalProjectionCLM
    (intrinsicPhysicalBirkhoffHomeomorph.symm (scalarPhysicalTargetCLM a))

/-- The scalar inverse is real analytic on every l2 input. -/
theorem scalarNonlinearFourierInverse_analytic :
    AnalyticOnNhd ℝ scalarNonlinearFourierInverse univ := by
  intro a _
  exact (scalarPhysicalProjectionCLM.analyticAt _).comp
    ((intrinsicPhysicalBirkhoffHomeomorph_analytic.2 _ (mem_univ _)).comp
      (scalarPhysicalTargetCLM.analyticAt a))

@[simp] theorem scalarNonlinearFourier_left_inv (u : IntervalL2) :
    scalarNonlinearFourierInverse (scalarNonlinearFourier u) = u := by
  change scalarPhysicalProjectionCLM
    (intrinsicPhysicalBirkhoffHomeomorph.symm
      (scalarPhysicalTargetCLM (normalizedPhysicalScalarCoordinate
        (intrinsicPhysicalBirkhoffMap (scalarPhysicalRealInput u))))) = u
  rw [scalarTarget_normalized,intrinsicPhysicalBirkhoffHomeomorph_left_inv,scalarPhysicalProjection_input]

@[simp] theorem scalarNonlinearFourier_right_inv (a : Coeff 2) :
    scalarNonlinearFourier (scalarNonlinearFourierInverse a) = a := by
  change normalizedPhysicalScalarCoordinate
    (intrinsicPhysicalBirkhoffMap (scalarPhysicalRealInput
      (scalarPhysicalProjectionCLM
        (intrinsicPhysicalBirkhoffHomeomorph.symm (scalarPhysicalTargetCLM a))))) = a
  rw [scalarPhysicalInput_projection,intrinsicPhysicalBirkhoffHomeomorph_right_inv,normalizedScalar_target]

/-- Nonlinear Parseval holds for the global inverse as well. -/
theorem scalarNonlinearFourierInverse_norm (a : Coeff 2) :
    ‖scalarNonlinearFourierInverse a‖ = ‖a‖ := by
  simpa only [scalarNonlinearFourier_right_inv] using
    (scalarNonlinearFourier_norm (scalarNonlinearFourierInverse a)).symm

/-- A global homeomorphism with the literal scalar nonlinear Fourier coefficients. -/
def scalarNonlinearFourierHomeomorph : IntervalL2 ≃ₜ Coeff 2 where
  toFun := scalarNonlinearFourier
  invFun := scalarNonlinearFourierInverse
  left_inv := scalarNonlinearFourier_left_inv
  right_inv := scalarNonlinearFourier_right_inv
  continuous_toFun := continuous_iff_continuousAt.mpr (fun u =>
    (scalarNonlinearFourier_analytic u (mem_univ _)).continuousAt)
  continuous_invFun := continuous_iff_continuousAt.mpr (fun a =>
    (scalarNonlinearFourierInverse_analytic a (mem_univ _)).continuousAt)

/-- The inverse fixes zero in the original scalar L2 space. -/
@[simp] theorem scalarNonlinearFourierInverse_zero : scalarNonlinearFourierInverse 0 = 0 := by
  apply norm_eq_zero.mp
  rw [scalarNonlinearFourierInverse_norm,norm_zero]

/-- The actual scalar inverse differential reconstructs the same signed reflected Fourier data. -/
theorem scalarNonlinearFourierInverse_fderiv_zero_coefficient (a : Coeff 2) (n : ℤ) :
    NLS.Fourier.intervalFourierCoefficient 1
      (fderiv ℝ scalarNonlinearFourierInverse 0 a) n = -a (-n) := by
  have hi := (scalarNonlinearFourierInverse_analytic 0 (mem_univ _)).differentiableAt.hasFDerivAt
  have hf : HasFDerivAt scalarNonlinearFourier (fderiv ℝ scalarNonlinearFourier 0)
      (scalarNonlinearFourierInverse 0) := by
    rw [scalarNonlinearFourierInverse_zero]
    exact (scalarNonlinearFourier_analytic 0 (mem_univ _)).differentiableAt.hasFDerivAt
  have hc := hf.comp 0 hi
  have hid : HasFDerivAt (fun b : Coeff 2 => b)
      ((fderiv ℝ scalarNonlinearFourier 0).comp (fderiv ℝ scalarNonlinearFourierInverse 0)) 0 := by
    simpa only [Function.comp_def,scalarNonlinearFourier_right_inv] using hc
  have he := congrArg (fun L : Coeff 2 →L[ℝ] Coeff 2 => L a (-n))
    (hid.unique (hasFDerivAt_id (0 : Coeff 2)))
  change fderiv ℝ scalarNonlinearFourier 0 (fderiv ℝ scalarNonlinearFourierInverse 0 a) (-n) = a (-n) at he
  rw [scalarNonlinearFourier_fderiv_zero_apply,neg_neg] at he
  exact neg_eq_iff_eq_neg.mp he

end NLS.ZakharovShabat
