import NLS.MKdV.PeriodOneMiuraSourceComparison
import NLS.MKdV.QuasiHillJointAnalytic
import NLS.ComplexAnalysis.SourceDiscriminantPrimitive
import NLS.ZakharovShabat.ContinuousPotentialSource
import NLS.ZakharovShabat.SourceCanonicalRootNormalization
import NLS.ComplexAnalysis.JointSpectralDerivative

/-! # Independent free-normalized Miura sheets for continuous profiles

The actual quasi-Hill IVP uses no derivative of its continuous profile.
Its root and primitive are constructed by source logarithmic integrals,
not defined by restriction of the NLS root or primitive.
-/
noncomputable section
open Set Complex Filter Topology NLS.LinearVolterra NLS.ComplexAnalysis
open NLS.KdV NLS.ZakharovShabat
open scoped ComplexConjugate ENNReal
namespace NLS.MKdV

def quasiHillPrimitiveData : SourceDiscriminantData (Curve ℂ) where
  discriminant t := quasiHillDiscriminant t.2 t.1
  energyDomain := slitPlane
  freePrimitive := classicalHillFreePrimitive
  energyDomain_open := isOpen_slitPlane
  discriminant_analytic := analyticOnNhd_quasiHillDiscriminant_joint
  freePrimitive_analytic := analyticOnNhd_classicalHillFreePrimitive
  free_trace z _ := by
    rw [quasiHillDiscriminant_zero]
    exact two_cosh_classicalHillFreePrimitive z

def miuraHillContinuationDomain : Set (ℂ × Curve ℂ) := quasiHillPrimitiveData.continuationDomain
def miuraHillRoot : ℂ × Curve ℂ → ℂ := quasiHillPrimitiveData.root
def miuraHillPrimitive : ℂ × Curve ℂ → ℂ := quasiHillPrimitiveData.primitive

theorem miuraDiagonalSource_realType (U : Curve ℂ) (hr : ∀ t, (U t).im = 0) :
    miuraDiagonalSourceCLM U ∈ realTypeSourceSubmodule 2 :=
  continuousPotentialSource_realType _ (fun t => (conj_eq_iff_im.mpr (hr t)).symm)

def miuraRealDiagonalSource (U : Curve ℂ) (hr : ∀ t, (U t).im = 0) :
    realTypeSourceSubmodule 2 := ⟨miuraDiagonalSourceCLM U,miuraDiagonalSource_realType U hr⟩

theorem miuraHillRadicand_ne_zero_of_real (U : Curve ℂ) (hr : ∀ t, (U t).im = 0)
    (z : ℂ) (hi : z.im ≠ 0) : quasiHillDiscriminant U (z^2)^2-4 ≠ 0 := by
  let φ := miuraRealDiagonalSource U hr
  have hz := sourceCanonicalRootDomain_of_im_ne_zero (by simp) (by norm_num) φ.val φ.property z hi
  have hs := sourceCanonicalRoot_sq_eq_discriminant_sq_sub_four (by simp) (by norm_num) φ.val z hz
  change sourceCanonicalRoot (by simp) (by norm_num) φ.val z ^ 2 =
    canonicalDiscriminant (by simp) (periodOnePotential (miuraDiagonalSourceCLM U)) z ^ 2-4 at hs
  rw [canonicalDiscriminant_miuraDiagonalSource] at hs
  intro he
  exact pow_ne_zero 2 (sourceCanonicalRoot_ne_zero_off_gaps _ _ _ _ hz) (hs.trans he)

theorem mem_miuraHillContinuationDomain_of_real
    (U : Curve ℂ) (hr : ∀ t, (U t).im = 0) (z : ℂ)
    (he : z^2 ∈ slitPlane) (hi : z.im ≠ 0) :
    (z^2,U) ∈ miuraHillContinuationDomain := by
  intro s _hs
  simp only [sourceSegmentMap,zero_add,sub_zero]
  change z^2 ∈ slitPlane ∧ quasiHillDiscriminant ((s : ℂ) • U) (z^2)^2-4 ≠ 0
  refine ⟨he,miuraHillRadicand_ne_zero_of_real _ ?_ z hi⟩
  intro t
  simp only [ContinuousMap.smul_apply,smul_eq_mul,mul_im,ofReal_re,ofReal_im,
    hr t,mul_zero,zero_mul,add_zero]

theorem miuraHillRoot_sq (t : ℂ × Curve ℂ) (ht : t ∈ miuraHillContinuationDomain) :
    miuraHillRoot t ^ 2 = quasiHillDiscriminant t.2 t.1 ^ 2-4 :=
  quasiHillPrimitiveData.root_sq t ht

theorem miuraHillPrimitive_trace (t : ℂ × Curve ℂ) (ht : t ∈ miuraHillContinuationDomain) :
    2*cosh (miuraHillPrimitive t) = quasiHillDiscriminant t.2 t.1 ∧
      2*sinh (miuraHillPrimitive t) = miuraHillRoot t :=
  quasiHillPrimitiveData.primitive_trace t ht

theorem hasFDerivAt_miuraHillPrimitive (t : ℂ × Curve ℂ)
    (ht : t ∈ miuraHillContinuationDomain) :
    HasFDerivAt miuraHillPrimitive ((miuraHillRoot t)⁻¹ •
      fderiv ℂ (fun t : ℂ × Curve ℂ => quasiHillDiscriminant t.2 t.1) t) t :=
  quasiHillPrimitiveData.primitive_hasFDerivAt t ht

theorem hasDerivAt_miuraHillPrimitive (t : ℂ × Curve ℂ)
    (ht : t ∈ miuraHillContinuationDomain) :
    HasDerivAt (fun μ => miuraHillPrimitive (μ,t.2))
      (deriv (quasiHillDiscriminant t.2) t.1 / miuraHillRoot t) t.1 := by
  have hinc : HasDerivAt (fun μ : ℂ => (μ,t.2)) (1,0) t.1 := by
    simpa using (hasDerivAt_id t.1).prodMk (hasDerivAt_const t.1 t.2)
  have h := (hasFDerivAt_miuraHillPrimitive t ht).comp_hasDerivAt t.1 hinc
  have hΔ := deriv_spectral_section_eq_fderiv
    (fun t : ℂ × Curve ℂ => quasiHillDiscriminant t.2 t.1) t.1 t.2
    (analyticOnNhd_quasiHillDiscriminant_joint t (mem_univ _)).differentiableAt
  convert! h using 1
  simp only [smul_apply,smul_eq_mul,← hΔ]
  ring

end NLS.MKdV
