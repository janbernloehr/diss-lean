import NLS.Fourier.UnitIntervalDirichlet
import NLS.KdV.SingularHillSesquilinear

/-! # The singular Dirichlet weak pencil

The domain is zero-trace interval H1 and the base is its full continuous
dual. Both tests and vectors are inserted as the identical unit-period
functions in the original period-two spaces. For unit-period potentials the original distributional
Hill operator is restricted to zero-trace tests, retaining its normalization.
The residual is not required to vanish on tests with nonzero endpoint trace.
-/
noncomputable section
open scoped ENNReal
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.SmoothPeriodicTest NLS.Fourier.PeriodicFourierLebesgue
open NLS.ZakharovShabat

/-- Restriction of an original distribution to all zero-trace H1 tests. -/
def singularDirichletRestriction : FourierLebesgueSpace (2 : ℝ) (-1) 2 →L[ℂ]
    UnitDirichletHminus := by
  let T : (FourierLebesgueSpace (2 : ℝ) 1 2 →L[ℂ] ℂ) →L[ℂ] UnitDirichletHminus :=
    { toFun := fun F => F.comp unitDirichletOriginalH1
      map_add' := by intros; ext g; rfl
      map_smul' := by intros; ext g; rfl
      cont := (continuous_id : Continuous
        (fun F : FourierLebesgueSpace (2 : ℝ) 1 2 →L[ℂ] ℂ => F)).clm_comp_const
          unitDirichletOriginalH1 }
  exact T.comp (sobolevDualIsometry 1 (by norm_num)).toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem singularDirichletRestriction_apply
    (v : FourierLebesgueSpace (2 : ℝ) (-1) 2) (g : UnitDirichletH1) :
    singularDirichletRestriction v g = singularHillPairing v (unitDirichletOriginalH1 g) := rfl

/-- The zero-trace interval conjugate is the same native physical conjugation. -/
theorem unitDirichletOriginalH1_conjugate (f : UnitDirichletH1) :
    sobolevConjugation 1 2 (unitDirichletOriginalH1 f) =
      unitDirichletOriginalH1 (unitDirichletConjugate f) := by
  apply Subtype.ext
  apply Distribution.ext_coefficients
  intro n
  rw [sobolevConjugation_coefficient]
  rw [show n = -(-n) by omega, unitDirichletOriginalH1_coefficient,
    unitDirichletOriginalH1_coefficient]
  simp only [neg_neg]
  by_cases hn : n % 2 = 0
  · have he : n = 2*(n/2) := by omega
    rw [he, show -(2*(n/2)) = 2*(-(n/2)) by ring,
      Coeff.periodDouble_even, Coeff.periodDouble_even]
    simp only [scalarInclusion_apply, unitDirichletConjugate_coefficient]
  · have he : n = 2*(n/2)+1 := by omega
    have he' : -n = 2*((-n)/2)+1 := by omega
    rw [he', Coeff.periodDouble_odd, he, Coeff.periodDouble_odd, star_zero]

/-- Domain inclusion into H-minus-one Dirichlet, using the actual L2 pairing. -/
def singularDirichletDomainInclusion : UnitDirichletH1 →L[ℂ] UnitDirichletHminus :=
  singularDirichletRestriction.comp (singularHillDomainInclusion.comp unitDirichletOriginalH1)

/-- The inclusion quadratic form is the positive original L2 energy. -/
theorem singularDirichletDomainInclusion_energy_pos (f : UnitDirichletH1) (hf : f ≠ 0) :
    0 < (singularDirichletDomainInclusion f (unitDirichletConjugate f)).re := by
  change 0 < (singularHillPairing
    (singularHillDomainInclusion (unitDirichletOriginalH1 f))
      (unitDirichletOriginalH1 (unitDirichletConjugate f))).re
  rw [← unitDirichletOriginalH1_conjugate]
  exact singularHillDomainInclusion_energy_pos _ (by
    intro h
    apply hf
    apply unitDirichletOriginalH1_injective
    simpa only [map_zero] using h)

theorem singularDirichletDomainInclusion_eq_zero_iff (f : UnitDirichletH1) :
    singularDirichletDomainInclusion f = 0 ↔ f = 0 := by
  constructor
  · intro h
    by_contra hf
    have hp := singularDirichletDomainInclusion_energy_pos f hf
    rw [h] at hp
    change (0 : ℝ) < 0 at hp
    exact (lt_irrefl 0) hp
  · rintro rfl
    exact map_zero _

/-- The base-space inclusion is injective on the full zero-trace H1 domain. -/
theorem singularDirichletDomainInclusion_injective :
    Function.Injective singularDirichletDomainInclusion := by
  intro f g h
  apply sub_eq_zero.mp
  apply (singularDirichletDomainInclusion_eq_zero_iff (f-g)).mp
  rw [map_sub, h, sub_self]

/-- The singular Hill expression tested against the full Dirichlet H1 domain. -/
def singularDirichletOperator (q : FourierLebesgueSpace (2 : ℝ) (-1) 2) :
    UnitDirichletH1 →L[ℂ] UnitDirichletHminus :=
  singularDirichletRestriction.comp ((singularHillOperator q).comp unitDirichletOriginalH1)

/-- The native domain-to-base spectral pencil at every complex energy. -/
def singularDirichletPencil (q : FourierLebesgueSpace (2 : ℝ) (-1) 2) (lambda : ℂ) :
    UnitDirichletH1 →L[ℂ] UnitDirichletHminus :=
  lambda • singularDirichletDomainInclusion-singularDirichletOperator q

/-- Exact bilinear weak form, with all original distributional actions retained. -/
theorem singularDirichletOperator_eigen_iff
    (q : FourierLebesgueSpace (2 : ℝ) (-1) 2) (lambda : ℂ) (f : UnitDirichletH1) :
    singularDirichletOperator q f = lambda • singularDirichletDomainInclusion f ↔
      ∀ g : UnitDirichletH1,
        singularHillPairing (singularHillOperator q (unitDirichletOriginalH1 f))
            (unitDirichletOriginalH1 g) =
          lambda * singularHillPairing (singularHillDomainInclusion (unitDirichletOriginalH1 f))
            (unitDirichletOriginalH1 g) := by
  constructor
  · intro h g
    exact congrArg (fun F : UnitDirichletHminus => F g) h
  · intro h
    ext g
    exact h g

/-- The independently defined weak pencil has exactly the native eigen-equation. -/
theorem singularDirichletPencil_eq_zero_iff
    (q : FourierLebesgueSpace (2 : ℝ) (-1) 2) (lambda : ℂ) (f : UnitDirichletH1) :
    singularDirichletPencil q lambda f = 0 ↔
      singularDirichletOperator q f = lambda • singularDirichletDomainInclusion f := by
  change lambda • singularDirichletDomainInclusion f-singularDirichletOperator q f = 0 ↔ _
  rw [sub_eq_zero, eq_comm]

/-- The original weak residual before zero-trace tests are imposed. -/
def singularDirichletResidual (q : FourierLebesgueSpace (2 : ℝ) (-1) 2)
    (lambda : ℂ) (f : UnitDirichletH1) : ScalarDomain 2 →L[ℂ] ℂ :=
  (sobolevDualIsometry 1 (by norm_num)
    (singularHillOperator q (unitDirichletOriginalH1 f) -
      lambda • singularHillDomainInclusion (unitDirichletOriginalH1 f))).comp unitSobolevOriginalH1

/-- Each full unit-period mode reads the corresponding original even residual coefficient. -/
theorem singularDirichletResidual_mode
    (q : FourierLebesgueSpace (2 : ℝ) (-1) 2) (lambda : ℂ) (f : UnitDirichletH1) (n : ℤ) :
    singularDirichletResidual q lambda f (scalarMode n 1) =
      (singularHillOperator q (unitDirichletOriginalH1 f)-
        lambda • singularHillDomainInclusion (unitDirichletOriginalH1 f)).val (mode (2*n)) := by
  change singularHillPairing _ (unitSobolevOriginalH1 (scalarMode n 1)) = _
  rw [singularHillPairing, sobolevDualIsometry_apply]
  have hm (k : ℤ) : (unitSobolevOriginalH1 (scalarMode n 1)).val (mode (-k)) =
      if k = 2*n then 1 else 0 := by
    rw [unitSobolevOriginalH1_coefficient]
    change (Coeff.periodDoubleSobolev (scalarMode n 1)).val k = _
    rw [Coeff.periodDoubleSobolev_scalarMode, scalarMode_apply]
  simp only [hm, ite_mul, one_mul, zero_mul, tsum_ite_eq]

theorem singularDirichletResidual_restriction
    (q : FourierLebesgueSpace (2 : ℝ) (-1) 2) (lambda : ℂ) (f : UnitDirichletH1) :
    unitDirichletDualRestriction (singularDirichletResidual q lambda f) =
      singularDirichletOperator q f-lambda • singularDirichletDomainInclusion f := by
  change singularDirichletRestriction
    (singularHillOperator q (unitDirichletOriginalH1 f)-
      lambda • singularHillDomainInclusion (unitDirichletOriginalH1 f)) = _
  rw [map_sub, map_smul]
  rfl

/-- Native eigenvectors have precisely an endpoint-evaluation residual.
This allows an unrestricted difference of endpoint quasi-derivative values. -/
theorem singularDirichletOperator_eigen_iff_boundary_defect
    (q : FourierLebesgueSpace (2 : ℝ) (-1) 2) (lambda : ℂ) (f : UnitDirichletH1) :
    singularDirichletOperator q f = lambda • singularDirichletDomainInclusion f ↔
      singularDirichletResidual q lambda f =
        singularDirichletResidual q lambda f (scalarMode 0 1) • unitDirichletTrace := by
  rw [← unitDirichletDualRestriction_eq_zero_iff,
    singularDirichletResidual_restriction, sub_eq_zero]

/-- In a native eigen-equation the endpoint defect has the same coefficient
at every original even frequency, including the central one. -/
theorem singularDirichlet_eigen_residual_coefficients
    (q : FourierLebesgueSpace (2 : ℝ) (-1) 2) (lambda : ℂ) (f : UnitDirichletH1)
    (he : singularDirichletOperator q f = lambda • singularDirichletDomainInclusion f)
    (n : ℤ) :
    (singularHillOperator q (unitDirichletOriginalH1 f)-
      lambda • singularHillDomainInclusion (unitDirichletOriginalH1 f)).val (mode (2*n)) =
        (singularHillOperator q (unitDirichletOriginalH1 f)-
          lambda • singularHillDomainInclusion (unitDirichletOriginalH1 f)).val (mode 0) := by
  have hd := (singularDirichletOperator_eigen_iff_boundary_defect q lambda f).mp he
  have hn := congrArg (fun F : ScalarDomain 2 →L[ℂ] ℂ => F (scalarMode n 1)) hd
  rw [singularDirichletResidual_mode] at hn
  simpa only [_root_.smul_apply, unitDirichletTrace_scalarMode, smul_eq_mul,
    mul_one, singularDirichletResidual_mode, mul_zero] using hn

/-- The true Dirichlet inclusion has real quadratic energy. -/
theorem singularDirichletDomainInclusion_energy_im (f : UnitDirichletH1) :
    (singularDirichletDomainInclusion f (unitDirichletConjugate f)).im = 0 := by
  change (singularHillPairing
    (singularHillDomainInclusion (unitDirichletOriginalH1 f))
      (unitDirichletOriginalH1 (unitDirichletConjugate f))).im = 0
  rw [← unitDirichletOriginalH1_conjugate]
  exact singularHillDomainInclusion_energy_im _

/-- Real original singular potentials give real native Dirichlet eigenvalues,
without any characteristic-function or root-label hypothesis. -/
theorem singularDirichlet_eigenvalue_im_eq_zero
    (q : FourierLebesgueSpace (2 : ℝ) (-1) 2) (hq : q.val = q.val.conjugate)
    (lambda : ℂ) (f : UnitDirichletH1) (hf : f ≠ 0)
    (he : singularDirichletOperator q f = lambda • singularDirichletDomainInclusion f) :
    lambda.im = 0 := by
  have hi : (singularDirichletOperator q f (unitDirichletConjugate f)).im = 0 := by
    change (singularHillPairing (singularHillOperator q (unitDirichletOriginalH1 f))
      (unitDirichletOriginalH1 (unitDirichletConjugate f))).im = 0
    rw [← unitDirichletOriginalH1_conjugate]
    exact singularHillOperator_energy_im q hq _
  rw [he] at hi
  change (lambda * singularDirichletDomainInclusion f (unitDirichletConjugate f)).im = 0 at hi
  rw [Complex.mul_im, singularDirichletDomainInclusion_energy_im, mul_zero, zero_add] at hi
  exact (mul_eq_zero.mp hi).resolve_right
    (ne_of_gt (singularDirichletDomainInclusion_energy_pos f hf))

/-- Green symmetry of the genuine domain inclusion. -/
theorem singularDirichletDomainInclusion_bilinear (f g : UnitDirichletH1) :
    singularDirichletDomainInclusion f g = singularDirichletDomainInclusion g f :=
  singularHillDomainInclusion_bilinear _ _

/-- Green symmetry of the full complex singular Dirichlet weak form. -/
theorem singularDirichletOperator_bilinear (q : FourierLebesgueSpace (2 : ℝ) (-1) 2)
    (f g : UnitDirichletH1) :
    singularDirichletOperator q f g = singularDirichletOperator q g f :=
  singularHillOperator_bilinear q _ _

end NLS.KdV
