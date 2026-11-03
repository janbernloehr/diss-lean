import NLS.FunctionalAnalysis.HermitianDualPositivity
import NLS.KdV.SingularHillSpectrum
import NLS.KdV.SingularHillSemibounded
import Mathlib.Topology.Order.DenselyOrdered

/-!
# The spectral lower bound is a full-domain quadratic-form bound

All forms use the original period-two H1 domain, the exact full H-minus-one
duality and the original normalized L2 energy. Positivity is transported along
the real resolvent interval below a spectral lower bound and then closed at
its endpoint. No endpoint membership of the potential is assumed.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue

/-- The shared full-duality real form is exactly the original physical Hill
quadratic form, with its original spectral shift and normalization. -/
theorem realDualityForm_singularHillPencil
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (a : ℝ)
    (f g : FourierLebesgueSpace (2:ℝ) 1 2) :
    realDualityForm (sobolevDualIsometry (L := 2) (p := 2) 1 (by norm_num))
      (sobolevConjugation (L := 2) 1 2)
      (singularHillOperator q-(a:ℂ) • singularHillDomainInclusion) f g =
    (singularHillSesquilinear (singularHillOperator q f) g).re -
      a*(singularHillSesquilinear (singularHillDomainInclusion f) g).re := by
  change (singularHillSesquilinear
    ((singularHillOperator q-(a:ℂ) • singularHillDomainInclusion) f) g).re = _
  rw [sub_apply,smul_apply,singularHillSesquilinear_sub_left,
    singularHillSesquilinear_smul_left,Complex.sub_re,Complex.mul_re,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]

/-- Reality of the potential gives symmetry of the full real duality pencil. -/
theorem realDualityForm_singularHillPencil_isSymm
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (hq : q.val = q.val.conjugate) (a : ℝ) :
    LinearMap.IsSymm (realDualityForm
      (sobolevDualIsometry (L := 2) (p := 2) 1 (by norm_num))
      (sobolevConjugation (L := 2) 1 2)
      (singularHillOperator q-(a:ℂ) • singularHillDomainInclusion)) := by
  constructor
  intro v w
  change realDualityForm _ _ _ v w = realDualityForm _ _ _ w v
  have hQ : (singularHillSesquilinear (singularHillOperator q v) w).re =
      (singularHillSesquilinear (singularHillOperator q w) v).re := by
    simpa only [Complex.star_def,Complex.conj_re] using
      congrArg Complex.re (singularHillOperator_hermitian q hq v w)
  have hJ : (singularHillSesquilinear (singularHillDomainInclusion v) w).re =
      (singularHillSesquilinear (singularHillDomainInclusion w) v).re := by
    simpa only [Complex.star_def,Complex.conj_re] using
      congrArg Complex.re (singularHillDomainInclusion_hermitian v w)
  rw [realDualityForm_singularHillPencil,realDualityForm_singularHillPencil,hQ,hJ]

/-- Every real lower bound on the actual full original spectrum is also a
lower bound for the actual quadratic form on every original H1 vector. -/
theorem singularHill_form_lower_bound_of_spectral_lower_bound
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (hq : q.val = q.val.conjugate)
    (a : ℝ) (ha : ∀ z ∈ singularHillSpectrum q, a ≤ z.re)
    (f : FourierLebesgueSpace (2:ℝ) 1 2) :
    a*(singularHillSesquilinear (singularHillDomainInclusion f) f).re ≤
      (singularHillSesquilinear (singularHillOperator q f) f).re := by
  let X := Iio a
  let : PreconnectedSpace X := Subtype.preconnectedSpace isPreconnected_Iio
  let D := sobolevDualIsometry (L := 2) (p := 2) (q := 2) 1
    (by norm_num : (2:ℝ≥0∞) ≠ ⊤)
  let C := sobolevConjugation (L := 2) 1 2
  let P := fun x : X => singularHillOperator q-(x.val:ℂ) • singularHillDomainInclusion
  have hP : Continuous P := continuous_const.sub
    ((Complex.continuous_ofReal.comp continuous_subtype_val).smul continuous_const)
  have hb : ∀ x : X, Function.Bijective (P x) := by
    intro x
    by_contra hn
    have hz : (x.val:ℂ) ∈ singularHillSpectrum q := hn
    have h := ha (x.val:ℂ) hz
    rw [Complex.ofReal_re] at h
    exact (not_le_of_gt x.property) h
  have hs : ∀ x : X, LinearMap.IsSymm (realDualityForm D C (P x)) :=
    fun x => realDualityForm_singularHillPencil_isSymm q hq x.val
  have hstart : ∃ x : X, ∀ v, 0 ≤ realDualityForm D C (P x) v v := by
    let b := min (a-1) (-singularHillLowerBoundConstant ‖q‖-1)
    have hba : b < a := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    refine ⟨⟨b,hba⟩,fun v => ?_⟩
    rw [realDualityForm_singularHillPencil]
    have hE : 0 ≤ (singularHillSesquilinear (singularHillDomainInclusion v) v).re := by
      rw [singularHillDomainInclusion_energy_eq_norm_sq,Complex.ofReal_re]
      exact sq_nonneg _
    have hbc : b ≤ -singularHillLowerBoundConstant ‖q‖ :=
      (min_le_right _ _).trans (by linarith)
    have hmul := mul_le_mul_of_nonneg_right hbc hE
    have hlow := singularHill_form_lower_bound q v
    linarith
  have hpos := nonneg_realDualityForm_of_preconnected D C P hP hb hs hstart
  have hclosed : IsClosed {x : ℝ |
      x*(singularHillSesquilinear (singularHillDomainInclusion f) f).re ≤
        (singularHillSesquilinear (singularHillOperator q f) f).re} :=
    isClosed_le (continuous_id.mul continuous_const) continuous_const
  have hsub : Iio a ⊆ {x : ℝ |
      x*(singularHillSesquilinear (singularHillDomainInclusion f) f).re ≤
        (singularHillSesquilinear (singularHillOperator q f) f).re} := by
    intro x hx
    have h := hpos ⟨x,hx⟩ f
    rw [realDualityForm_singularHillPencil] at h
    exact sub_nonneg.mp h
  apply closure_minimal hsub hclosed
  rw [closure_Iio]
  exact (show a ≤ a from le_rfl)

end NLS.KdV
