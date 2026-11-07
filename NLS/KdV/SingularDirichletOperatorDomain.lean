import NLS.KdV.SingularDirichletPencil
import NLS.Fourier.UnitIntervalDirichletIdentification
import Mathlib.Topology.Algebra.Module.LinearPMap

/-! # The Dirichlet partial operator on its full H-minus-one base

The operator domain is the image of the complete zero-trace H1 space under
its injective L2-pairing inclusion. Every classical interval H1 function
with zero endpoints is represented, and no endpoint condition is imposed
on a quasi-derivative. Closedness, resolvents and characteristic matching
are separate proof obligations.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue

/-- The actual zero-trace domain identified with its image in the full dual base. -/
def singularDirichletDomainEquiv : UnitDirichletH1 ≃ₗ[ℂ]
    singularDirichletDomainInclusion.range :=
  LinearEquiv.ofInjective singularDirichletDomainInclusion.toLinearMap
    singularDirichletDomainInclusion_injective

@[simp] theorem singularDirichletDomainEquiv_val (f : UnitDirichletH1) :
    (singularDirichletDomainEquiv f).val = singularDirichletDomainInclusion f := rfl

/-- The induced singular Dirichlet partial operator acts on H-minus-one, with
precisely the full zero-trace H1 domain. Unit-period original potentials give
the source interval operator through its original distributional weak form. -/
def singularDirichletPartialOperator (q : FourierLebesgueSpace (2 : ℝ) (-1) 2) :
    UnitDirichletHminus →ₗ.[ℂ] UnitDirichletHminus where
  domain := singularDirichletDomainInclusion.range
  toFun := (singularDirichletOperator q).toLinearMap.comp
    singularDirichletDomainEquiv.symm.toLinearMap

theorem singularDirichletPartialOperator_apply
    (q : FourierLebesgueSpace (2 : ℝ) (-1) 2) (f : UnitDirichletH1) :
    singularDirichletPartialOperator q (singularDirichletDomainEquiv f) =
      singularDirichletOperator q f := by
  change singularDirichletOperator q
    (singularDirichletDomainEquiv.symm (singularDirichletDomainEquiv f)) = _
  rw [LinearEquiv.symm_apply_apply]

/-- The standard partial-map graph is exactly the zero-trace interval weak graph. -/
theorem singularDirichletPartialOperator_graph
    (q : FourierLebesgueSpace (2 : ℝ) (-1) 2) :
    ((singularDirichletPartialOperator q).graph : Set (UnitDirichletHminus × UnitDirichletHminus)) =
      {p | ∃ f : UnitDirichletH1,
        singularDirichletDomainInclusion f = p.1 ∧ singularDirichletOperator q f = p.2} := by
  ext p
  change p ∈ (singularDirichletPartialOperator q).graph ↔
    ∃ f : UnitDirichletH1,
      singularDirichletDomainInclusion f = p.1 ∧ singularDirichletOperator q f = p.2
  rw [LinearPMap.mem_graph_iff]
  constructor
  · rintro ⟨v, hv, hq⟩
    let w : singularDirichletDomainInclusion.range := v
    refine ⟨singularDirichletDomainEquiv.symm w, ?_, hq⟩
    rw [← singularDirichletDomainEquiv_val, LinearEquiv.apply_symm_apply]
    exact hv
  · rintro ⟨f, hf, hq⟩
    exact ⟨singularDirichletDomainEquiv f, hf,
      (singularDirichletPartialOperator_apply q f).trans hq⟩

/-- Eigenvectors of the partial operator coincide with eigenvectors of the
independent H1-to-H-minus-one Dirichlet pencil. -/
theorem singularDirichletPartialOperator_eigen_iff
    (q : FourierLebesgueSpace (2 : ℝ) (-1) 2) (lambda : ℂ) :
    (∃ v : (singularDirichletPartialOperator q).domain,
      v.val ≠ 0 ∧ singularDirichletPartialOperator q v = lambda • v.val) ↔
    ∃ f : UnitDirichletH1, f ≠ 0 ∧ singularDirichletPencil q lambda f = 0 := by
  constructor
  · rintro ⟨v, hv, he⟩
    let w : singularDirichletDomainInclusion.range := v
    let f := singularDirichletDomainEquiv.symm w
    have hvf : singularDirichletDomainInclusion f = v.val := by
      exact congrArg (fun u : singularDirichletDomainInclusion.range => u.val)
        (singularDirichletDomainEquiv.apply_symm_apply w)
    refine ⟨f, ?_, (singularDirichletPencil_eq_zero_iff q lambda f).mpr ?_⟩
    · intro h
      apply hv
      rw [← hvf, h, map_zero]
    · change singularDirichletOperator q f = lambda • v.val at he
      rw [hvf]
      exact he
  · rintro ⟨f, hf, he⟩
    refine ⟨singularDirichletDomainEquiv f, ?_, ?_⟩
    · change singularDirichletDomainInclusion f ≠ 0
      exact fun h => hf ((singularDirichletDomainInclusion_eq_zero_iff f).mp h)
    · rw [singularDirichletPartialOperator_apply, singularDirichletDomainEquiv_val]
      exact (singularDirichletPencil_eq_zero_iff q lambda f).mp he

end NLS.KdV
