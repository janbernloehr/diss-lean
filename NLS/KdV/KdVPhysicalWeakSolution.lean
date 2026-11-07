import NLS.KdV.KdVWeakLimit
import NLS.KdV.SmoothKdVWeakEquivalence

/-! The independent Fourier weak equation on the original physical L²
potential space, and its bridge from smooth physical approximation. -/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
namespace NLS.KdV

/-- The physical Fourier-L² classical PDE notion already implies
continuity in the original potential norm. -/
theorem IsClassicalKdVTrajectory.continuous
    {u : ℝ → RealPeriodOneHillPotential} (hu : IsClassicalKdVTrajectory u) : Continuous u := by
  have hc : Continuous (fun t => SpectralWeight.one.toCoeff (u t).val) := by
    apply Differentiable.continuous (𝕜 := ℝ)
    intro t
    obtain ⟨_,_,h⟩ := hu t
    exact h.differentiableAt
  let I := WeightedCoeff.weightIsometry SpectralWeight.one.toWeight 2
  have he (q : WeightedCoeff SpectralWeight.one.toWeight 2) :
      SpectralWeight.one.toCoeff q = I q := by
    ext k
    rw [SpectralWeight.toCoeff_apply]
    change q.val k = WeightedCoeff.weightEquiv SpectralWeight.one.toWeight 2 q k
    rw [WeightedCoeff.weightEquiv_apply]
    simp only [SpectralWeight.one_apply,Complex.ofReal_one,one_mul]
  simp_rw [he] at hc
  have hv : Continuous (fun t => (u t).val) := by
    simpa only [Function.comp_def,I.symm_apply_apply] using I.symm.continuous.comp hc
  exact hv.subtype_mk _

def kdvPhysicalUnitCoefficientsCLM : WeightedCoeff SpectralWeight.one.toWeight 2 →L[ℂ] Coeff 2 :=
  (Coeff.restrictIndicesCLM (Coeff.parityEmbedding 0)).comp SpectralWeight.one.toCoeff

def kdvPhysicalUnitCoefficients (q : RealPeriodOneHillPotential) : Coeff 2 :=
  kdvPhysicalUnitCoefficientsCLM q.val

theorem kdvPhysicalUnitCoefficients_apply (q : RealPeriodOneHillPotential) (n : ℤ) :
    kdvPhysicalUnitCoefficients q n = q.val.val (2*n) := by
  change SpectralWeight.one.toCoeff q.val (2*n+0) = _
  simp only [add_zero,SpectralWeight.toCoeff_apply]

theorem uniformContinuous_kdvPhysicalUnitCoefficients : UniformContinuous kdvPhysicalUnitCoefficients :=
  kdvPhysicalUnitCoefficientsCLM.uniformContinuous.comp uniformContinuous_subtype_val

/-- Independent integrated KdV equation in every original unit-period
Fourier mode, with continuity in physical L². -/
def IsFourierWeakKdVTrajectory (u : ℝ → RealPeriodOneHillPotential) : Prop :=
  Continuous u ∧ IsFourierWeakKdVCoefficients (fun t => kdvPhysicalUnitCoefficients (u t))

theorem kdvPhysicalUnitCoefficients_eq_of_source
    (q : RealPeriodOneHillPotential) (Q : C(AddCircle (2 : ℝ),ℂ))
    (h : SpectralWeight.one.toCoeff q.val = Fourier.continuousFourierCLM Q) :
    kdvPhysicalUnitCoefficients q = kdvUnitFourierCLM Q := by
  change Coeff.restrictIndicesCLM _ (SpectralWeight.one.toCoeff q.val) = _
  rw [h]
  rfl

theorem isFourierWeakKdVTrajectory_of_smooth_physical
    (u : ℝ → RealPeriodOneHillPotential) (Q : ℝ → C(AddCircle (2 : ℝ),ℂ))
    (hsource : ∀ t, SpectralWeight.one.toCoeff (u t).val = Fourier.continuousFourierCLM (Q t))
    (hQ : IsSmoothPhysicalKdVTrajectory Q) : IsFourierWeakKdVTrajectory u := by
  refine ⟨(hQ.toClassicalKdVTrajectory u hsource).continuous,?_⟩
  have he : (fun t => kdvPhysicalUnitCoefficients (u t)) = fun t => kdvUnitFourierCLM (Q t) :=
    funext (fun t => kdvPhysicalUnitCoefficients_eq_of_source (u t) (Q t) (hsource t))
  rw [he]
  exact (isFourierWeakPhysicalKdV_iff_equation Q hQ.time_differentiable hQ.spatial_smooth hQ.periodic).mpr hQ.equation

/-- Passage to the weak equation for physical L² limits, independently of
any spectral conservation statement. -/
theorem isFourierWeakKdVTrajectory_of_locallyUniformLimit
    (v : ℕ → ℝ → RealPeriodOneHillPotential) (u : ℝ → RealPeriodOneHillPotential)
    (hv : ∀ N, IsFourierWeakKdVTrajectory (v N)) (hu : Continuous u)
    (hlim : ∀ T : ℝ, 0 ≤ T → TendstoUniformlyOn v u atTop (Icc (-T) T)) :
    IsFourierWeakKdVTrajectory u := by
  refine ⟨hu,isFourierWeakKdVCoefficients_of_locallyUniformLimit
    (fun N t => kdvPhysicalUnitCoefficients (v N t)) (fun t => kdvPhysicalUnitCoefficients (u t))
    (fun N => (hv N).2) (uniformContinuous_kdvPhysicalUnitCoefficients.continuous.comp hu) ?_⟩
  intro T hT
  exact uniformContinuous_kdvPhysicalUnitCoefficients.comp_tendstoUniformlyOn (hlim T hT)

end NLS.KdV
