import NLS.KdV.SingularHillMiuraFactorization
import NLS.KdV.SingularHillAlgebraicMultiplicity
import NLS.KdV.SingularHillRealSpectrum

/-! A fixed first-order companion for a rough native Miura potential.
Both components retain the full original H1 domain. -/
noncomputable section
open Complex
open scoped ENNReal
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.SmoothPeriodicTest NLS.Fourier.PeriodicFourierLebesgue
open NLS.ZakharovShabat

/-- The fixed first-order operator (i*(h'+u*h), i*(f'-u*f)). -/
def singularHillMiuraCompanion (u : Coeff 2) : Domain 2 →L[ℂ] PairSpace 2 :=
  ((I • (ZakharovShabat.derivative+potentialMul (by norm_num) u)).comp
    (ContinuousLinearMap.snd ℂ _ _)).prod
      ((I • (ZakharovShabat.derivative-potentialMul (by norm_num) u)).comp
        (ContinuousLinearMap.fst ℂ _ _))

/-- The full first-order eigenspace of the actual companion differential operator. -/
def singularHillMiuraCompanionEigenspace (u : Coeff 2) (z : ℂ) : Submodule ℂ (Domain 2) :=
  LinearMap.ker (singularHillMiuraCompanion u-z • domainInclusion).toLinearMap

/-- Exact row equations for the fixed companion operator. -/
theorem singularHillMiuraCompanion_eigen_iff (u : Coeff 2) (z : ℂ) (f g : ScalarDomain 2) :
    singularHillMiuraCompanion u (f,g) = z • domainInclusion (f,g) ↔
      ZakharovShabat.derivative g+potentialMul (by norm_num) u g = (-I*z) • scalarInclusion f ∧
      ZakharovShabat.derivative f-potentialMul (by norm_num) u f = (-I*z) • scalarInclusion g := by
  have hi : (-I:ℂ)*I = 1 := by simp
  have hi' : I*(-I*z) = z := by simp [← mul_assoc]
  constructor
  · intro h
    have h₁ := congrArg (fun p : PairSpace 2 => -I • p.1) h
    have h₂ := congrArg (fun p : PairSpace 2 => -I • p.2) h
    change -I • (I • (ZakharovShabat.derivative g+potentialMul (by norm_num) u g)) =
      -I • (z • scalarInclusion f) at h₁
    change -I • (I • (ZakharovShabat.derivative f-potentialMul (by norm_num) u f)) =
      -I • (z • scalarInclusion g) at h₂
    simp only [smul_smul, hi, one_smul] at h₁ h₂
    exact ⟨h₁,h₂⟩
  · rintro ⟨h₁,h₂⟩
    apply Prod.ext
    · change I • (ZakharovShabat.derivative g+potentialMul (by norm_num) u g) = z • scalarInclusion f
      rw [h₁, smul_smul, hi']
    · change I • (ZakharovShabat.derivative f-potentialMul (by norm_num) u f) = z • scalarInclusion g
      rw [h₂, smul_smul, hi']

theorem l2DerivativeOriginalHminus_scalarInclusion (f : ScalarDomain 2) :
    l2DerivativeOriginalHminus (scalarInclusion f) = l2OriginalHminus (ZakharovShabat.derivative f) := by
  apply Subtype.ext
  apply Distribution.ext_coefficients
  intro n
  rw [l2DerivativeOriginalHminus_coefficient, scalarInclusion_apply,
    l2OriginalHminus_coefficient, ZakharovShabat.derivative_apply]

theorem l2ProductOriginalHminus_scalarInclusion (u : Coeff 2) (f : ScalarDomain 2) :
    l2ProductOriginalHminus u (scalarInclusion f) = l2OriginalHminus (potentialMul (by norm_num) u f) := by
  apply Subtype.ext
  apply Distribution.ext_coefficients
  intro n
  rw [l2ProductOriginalHminus_coefficient, l2OriginalHminus_coefficient, potentialMul_apply]
  simp only [scalarInclusion_apply]

/-- Every companion eigenvector projects to an original Hill eigenvector
at energy z squared, also when the frequency is zero. -/
theorem singularHillMiuraCompanion_eigen_to_hill (u : Coeff 2) (z : ℂ) (f g : ScalarDomain 2)
    (h : singularHillMiuraCompanion u (f,g) = z • domainInclusion (f,g)) :
    singularHillOperator (singularHillMiuraPotential u) (scalarDomainOriginalH1 f) =
      z^2 • singularHillDomainInclusion (scalarDomainOriginalH1 f) := by
  obtain ⟨h₁,h₂⟩ := (singularHillMiuraCompanion_eigen_iff u z f g).mp h
  have hq : singularHillQuasiDerivative u f = (-I*z) • scalarInclusion g := h₂
  rw [singularHillOperator_miura_factorization, hq, map_smul, map_smul,
    l2DerivativeOriginalHminus_scalarInclusion, l2ProductOriginalHminus_scalarInclusion]
  have he : -((-I*z) • l2OriginalHminus (ZakharovShabat.derivative g))-
      (-I*z) • l2OriginalHminus (potentialMul (by norm_num) u g) =
      (I*z) • l2OriginalHminus (ZakharovShabat.derivative g+potentialMul (by norm_num) u g) := by
    simp only [map_add]
    module
  rw [he, h₁, map_smul, smul_smul, l2OriginalHminus_scalarInclusion]
  have hs : (I*z)*(-I*z) = z^2 := by ring_nf; simp [I_sq]
  rw [hs]

/-- The genuine L2 forcing associated to an original Hill eigenvector. -/
theorem singularHillMiura_eigen_forcing (u : Coeff 2) (z : ℂ) (f : ScalarDomain 2)
    (h : singularHillOperator (singularHillMiuraPotential u) (scalarDomainOriginalH1 f) =
      z^2 • singularHillDomainInclusion (scalarDomainOriginalH1 f)) :
    singularHillOperator (singularHillMiuraPotential u) (scalarDomainOriginalH1 f) =
      l2OriginalHminus (z^2 • scalarInclusion f) := by
  rw [map_smul, l2OriginalHminus_scalarInclusion]
  exact h

/-- The full H1 second component recovered from an original Hill eigenvector. -/
def singularHillMiuraEigenLift (u : Coeff 2) (z : ℂ) (f : ScalarDomain 2)
    (h : singularHillOperator (singularHillMiuraPotential u) (scalarDomainOriginalH1 f) =
      z^2 • singularHillDomainInclusion (scalarDomainOriginalH1 f)) : ScalarDomain 2 :=
  (I/z) • singularHillQuasiDerivativeLift u (z^2 • scalarInclusion f) f
    (singularHillMiura_eigen_forcing u z f h)

/-- Every original Hill eigenvector has a full companion-domain lift at
nonzero frequency, with no auxiliary-component regularity hypothesis. -/
theorem singularHillMiuraEigenLift_eigen (u : Coeff 2) (z : ℂ) (hz : z ≠ 0) (f : ScalarDomain 2)
    (h : singularHillOperator (singularHillMiuraPotential u) (scalarDomainOriginalH1 f) =
      z^2 • singularHillDomainInclusion (scalarDomainOriginalH1 f)) :
    singularHillMiuraCompanion u (f,singularHillMiuraEigenLift u z f h) =
      z • domainInclusion (f,singularHillMiuraEigenLift u z f h) := by
  let g := singularHillQuasiDerivativeLift u (z^2 • scalarInclusion f) f
    (singularHillMiura_eigen_forcing u z f h)
  have hg : scalarInclusion g = singularHillQuasiDerivative u f :=
    scalarInclusion_singularHillQuasiDerivativeLift _ _ _ _
  have hd : ZakharovShabat.derivative g = -potentialMul (by norm_num) u g-z^2 • scalarInclusion f :=
    derivative_singularHillQuasiDerivativeLift _ _ _ _
  apply (singularHillMiuraCompanion_eigen_iff u z f _).mpr
  change ZakharovShabat.derivative ((I/z) • g)+potentialMul (by norm_num) u ((I/z) • g) = _ ∧ _
  constructor
  · rw [map_smul, map_smul, hd]
    have hs : (I/z)*z^2 = I*z := by field_simp
    simp only [smul_sub, smul_neg, smul_smul, hs]
    module
  · change singularHillQuasiDerivative u f = (-I*z) • scalarInclusion ((I/z) • g)
    rw [map_smul, smul_smul, hg]
    have hs : (-I*z)*(I/z) = 1 := by field_simp; simp [I_sq]
    rw [hs, one_smul]

/-- Projection to the first component is complex linear on the full companion eigenspace. -/
def singularHillMiuraCompanionEigenToHill (u : Coeff 2) (z : ℂ) :
    singularHillMiuraCompanionEigenspace u z →ₗ[ℂ]
      singularHillEigenspace (singularHillMiuraPotential u) (z^2) where
  toFun v := ⟨scalarDomainOriginalH1 v.val.1, by
    apply (mem_singularHillEigenspace_iff _ _ _).mpr
    apply singularHillMiuraCompanion_eigen_to_hill u z v.val.1 v.val.2
    exact sub_eq_zero.mp v.property⟩
  map_add' v w := Subtype.ext ((sobolevCoefficients 1 2).symm.map_add v.val.1 w.val.1)
  map_smul' c v := Subtype.ext ((sobolevCoefficients 1 2).symm.map_smul c v.val.1)

/-- Nonzero frequency makes the first component determine the entire
companion eigenvector, without a regularity assumption on its potential. -/
theorem singularHillMiuraCompanionEigenToHill_injective (u : Coeff 2) (z : ℂ) (hz : z ≠ 0) :
    Function.Injective (singularHillMiuraCompanionEigenToHill u z) := by
  intro v w he
  have hf : v.val.1 = w.val.1 := (sobolevCoefficients 1 2).symm.injective
    (congrArg Subtype.val he)
  have hv := ((singularHillMiuraCompanion_eigen_iff u z v.val.1 v.val.2).mp
    (sub_eq_zero.mp v.property)).2
  have hw := ((singularHillMiuraCompanion_eigen_iff u z w.val.1 w.val.2).mp
    (sub_eq_zero.mp w.property)).2
  rw [hf] at hv
  have hc : (-I*z) • scalarInclusion v.val.2 = (-I*z) • scalarInclusion w.val.2 := hv.symm.trans hw
  have hne : -I*z ≠ 0 := mul_ne_zero (neg_ne_zero.mpr I_ne_zero) hz
  have hh := congrArg (fun a : Coeff 2 => (-I*z)⁻¹ • a) hc
  simp only [smul_smul, inv_mul_cancel₀ hne, one_smul] at hh
  exact Subtype.ext (Prod.ext hf (scalarInclusion_injective hh))

/-- Every original Hill eigenvector is represented by a full-domain companion
vector. The proof constructs its H1 second component from the physical equation. -/
theorem singularHillMiuraCompanionEigenToHill_surjective (u : Coeff 2) (z : ℂ) (hz : z ≠ 0) :
    Function.Surjective (singularHillMiuraCompanionEigenToHill u z) := by
  intro v
  let f := sobolevCoefficients 1 2 v.val
  have hf : scalarDomainOriginalH1 f = v.val := scalarDomainOriginalH1_sobolevCoefficients v.val
  have he : singularHillOperator (singularHillMiuraPotential u) (scalarDomainOriginalH1 f) =
      z^2 • singularHillDomainInclusion (scalarDomainOriginalH1 f) := by
    rw [hf]
    exact (mem_singularHillEigenspace_iff _ _ _).mp v.property
  let g := singularHillMiuraEigenLift u z f he
  refine ⟨⟨(f,g), ?_⟩, Subtype.ext hf⟩
  change singularHillMiuraCompanion u (f,g)-z • domainInclusion (f,g) = 0
  exact sub_eq_zero.mpr (singularHillMiuraEigenLift_eigen u z hz f he)

/-- Exact linear correspondence of the original second-order eigenspace and
its fixed full-domain first-order companion at nonzero square-root energy. -/
def singularHillMiuraEigenspaceEquiv (u : Coeff 2) (z : ℂ) (hz : z ≠ 0) :
    singularHillMiuraCompanionEigenspace u z ≃ₗ[ℂ]
      singularHillEigenspace (singularHillMiuraPotential u) (z^2) :=
  LinearEquiv.ofBijective (singularHillMiuraCompanionEigenToHill u z)
    ⟨singularHillMiuraCompanionEigenToHill_injective u z hz,
      singularHillMiuraCompanionEigenToHill_surjective u z hz⟩

/-- The actual geometric multiplicities agree on the unchanged full domains. -/
theorem finrank_singularHillMiuraCompanionEigenspace (u : Coeff 2) (z : ℂ) (hz : z ≠ 0) :
    Module.finrank ℂ (singularHillMiuraCompanionEigenspace u z) =
      Module.finrank ℂ (singularHillEigenspace (singularHillMiuraPotential u) (z^2)) :=
  (singularHillMiuraEigenspaceEquiv u z hz).finrank_eq

/-- At a real original Miura potential, its physical algebraic multiplicity
is the dimension of the exact companion eigenspace, by proved semisimplicity. -/
theorem singularHillAlgebraicMultiplicity_miura_companion (u : Coeff 2)
    (hu : (singularHillMiuraPotential u).val = (singularHillMiuraPotential u).val.conjugate)
    (z : ℂ) (hz : z ≠ 0) :
    singularHillAlgebraicMultiplicity (singularHillMiuraPotential u) (z^2) =
      Module.finrank ℂ (singularHillMiuraCompanionEigenspace u z) := by
  change Module.finrank ℂ (singularHillRootSpaceTop (singularHillMiuraPotential u) (z^2)) = _
  rw [singularHillRootSpaceTop_eq_one_of_real _ hu,
    ← (singularHillEigenspaceRootEquiv (singularHillMiuraPotential u) (z^2)).finrank_eq,
    ← finrank_singularHillMiuraCompanionEigenspace u z hz]

end NLS.KdV
