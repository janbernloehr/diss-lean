import NLS.KdV.SingularHillPhysical
import NLS.SequenceSpaces.WeightedFiniteCoefficients
import Mathlib.Topology.Algebra.Module.LinearPMap

/-! # The actual singular Hill partial operator on H-minus-one

The domain is precisely the image of original H1 under its unchanged-distribution
inclusion. This realizes the operator in the standard partial-linear-map API,
with its full physical expression and a proved dense original domain.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.SmoothPeriodicTest NLS.Fourier.PeriodicFourierLebesgue

/-- The actual H1 domain inclusion in H-minus-one is injective. -/
theorem singularHillDomainInclusion_injective : Function.Injective singularHillDomainInclusion := by
  intro f g h
  apply Subtype.ext
  simpa only [singularHillDomainInclusion_val] using
    congrArg (fun u : FourierLebesgueSpace (2:ℝ) (-1) 2 => u.val) h

/-- The original H1 domain is dense in the original H-minus-one base space. -/
theorem denseRange_singularHillDomainInclusion : DenseRange singularHillDomainInclusion := by
  have hd : DenseRange (fun a : ℤ →₀ ℂ => (sobolevCoefficients (L := 2) (-1) 2).symm
      (WeightedCoeff.ofFinsupp (Weight.sobolev (-1)) 2 a)) :=
    (sobolevCoefficients (L := 2) (-1) 2).symm.surjective.denseRange.comp
      (WeightedCoeff.denseRange_ofFinsupp _ 2 (by norm_num))
        (sobolevCoefficients (L := 2) (-1) 2).symm.continuous
  apply hd.mono
  rintro _ ⟨a, rfl⟩
  refine ⟨(sobolevCoefficients 1 2).symm (WeightedCoeff.ofFinsupp (Weight.sobolev 1) 2 a), ?_⟩
  apply Subtype.ext
  apply Distribution.ext_coefficients
  intro k
  rw [singularHillDomainInclusion_coefficient]
  change ((sobolevCoefficients 1 2) ((sobolevCoefficients 1 2).symm _)).val k =
    ((sobolevCoefficients (-1) 2) ((sobolevCoefficients (-1) 2).symm _)).val k
  rw [LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.apply_symm_apply]
  rfl

/-- The algebraic equivalence with the actual partial-operator domain in H-minus-one. -/
def singularHillDomainEquiv : FourierLebesgueSpace (2:ℝ) 1 2 ≃ₗ[ℂ]
    singularHillDomainInclusion.range :=
  LinearEquiv.ofInjective singularHillDomainInclusion.toLinearMap singularHillDomainInclusion_injective

@[simp] theorem singularHillDomainEquiv_val (f : FourierLebesgueSpace (2:ℝ) 1 2) :
    (singularHillDomainEquiv f).val = singularHillDomainInclusion f := rfl

/-- The source unbounded Hill operator on original H-minus-one with exactly original H1 domain. -/
def singularHillPartialOperator (q : FourierLebesgueSpace (2:ℝ) (-1) 2) :
    FourierLebesgueSpace (2:ℝ) (-1) 2 →ₗ.[ℂ] FourierLebesgueSpace (2:ℝ) (-1) 2 where
  domain := singularHillDomainInclusion.range
  toFun := (singularHillOperator q).toLinearMap.comp singularHillDomainEquiv.symm.toLinearMap

/-- The partial operator acts by the original physical Hill expression on every original H1 vector. -/
theorem singularHillPartialOperator_apply (q : FourierLebesgueSpace (2:ℝ) (-1) 2)
    (f : FourierLebesgueSpace (2:ℝ) 1 2) :
    singularHillPartialOperator q (singularHillDomainEquiv f) = singularHillOperator q f := by
  change singularHillOperator q (singularHillDomainEquiv.symm (singularHillDomainEquiv f)) = _
  rw [LinearEquiv.symm_apply_apply]

/-- The standard partial-map graph is exactly the full original physical graph. -/
theorem singularHillPartialOperator_graph (q : FourierLebesgueSpace (2:ℝ) (-1) 2) :
    ((singularHillPartialOperator q).graph :
      Set (FourierLebesgueSpace (2:ℝ) (-1) 2 × FourierLebesgueSpace (2:ℝ) (-1) 2)) =
      {p | ∃ f : FourierLebesgueSpace (2:ℝ) 1 2,
        singularHillDomainInclusion f = p.1 ∧ singularHillOperator q f = p.2} := by
  ext p
  change p ∈ (singularHillPartialOperator q).graph ↔
    ∃ f : FourierLebesgueSpace (2:ℝ) 1 2,
      singularHillDomainInclusion f = p.1 ∧ singularHillOperator q f = p.2
  rw [LinearPMap.mem_graph_iff]
  constructor
  · rintro ⟨v,hv,hq⟩
    let w : singularHillDomainInclusion.range := v
    refine ⟨singularHillDomainEquiv.symm w, ?_, ?_⟩
    · rw [← singularHillDomainEquiv_val, LinearEquiv.apply_symm_apply]
      exact hv
    · exact hq
  · rintro ⟨f,hf,hq⟩
    exact ⟨singularHillDomainEquiv f, hf, (singularHillPartialOperator_apply q f).trans hq⟩

/-- The actual partial operator has dense domain in its original H-minus-one base space. -/
theorem dense_domain_singularHillPartialOperator (q : FourierLebesgueSpace (2:ℝ) (-1) 2) :
    Dense ((singularHillPartialOperator q).domain :
      Set (FourierLebesgueSpace (2:ℝ) (-1) 2)) :=
  denseRange_singularHillDomainInclusion

end NLS.KdV
