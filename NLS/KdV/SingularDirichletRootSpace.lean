import NLS.KdV.SingularDirichletOperatorDomain
import NLS.FunctionalAnalysis.PencilRootSemisimple

/-! # Actual algebraic chains on the native Dirichlet H-minus-one base

Each step uses the complete zero-trace H1 domain through its injective
inclusion. The chain spaces are exactly those of the actual partial operator,
without a supplied spectrum, resolvent or semisimplicity assumption.
-/
noncomputable section
open scoped ENNReal
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue NLS.FunctionalAnalysis

/-- The entire native domain eigenspace. -/
def singularDirichletEigenspace (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (lambda : ℂ) :
    Submodule ℂ UnitDirichletH1 :=
  LinearMap.ker (singularDirichletPencil q lambda).toLinearMap

/-- Finite root-chain levels retain the original native domain at every step. -/
def singularDirichletRootSpace (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (lambda : ℂ) (n : ℕ) :
    Submodule ℂ UnitDirichletHminus :=
  pencilRootSpace singularDirichletDomainInclusion.toLinearMap
    (singularDirichletPencil q lambda).toLinearMap n

/-- The union of all finite native chains in the full H-minus-one base. -/
def singularDirichletRootSpaceTop (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (lambda : ℂ) :
    Submodule ℂ UnitDirichletHminus :=
  pencilRootSpaceTop singularDirichletDomainInclusion.toLinearMap
    (singularDirichletPencil q lambda).toLinearMap

theorem mem_singularDirichletRootSpace_succ
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (lambda : ℂ) (n : ℕ) (x : UnitDirichletHminus) :
    x ∈ singularDirichletRootSpace q lambda (n+1) ↔
      ∃ f : UnitDirichletH1, singularDirichletDomainInclusion f = x ∧
        singularDirichletPencil q lambda f ∈ singularDirichletRootSpace q lambda n :=
  mem_pencilRootSpace_succ _ _ n x

/-- These chains are EXACTLY the actual partial operator's own domain chains. -/
theorem singularDirichletRootSpace_eq_partial
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (lambda : ℂ) (n : ℕ) :
    singularDirichletRootSpace q lambda n =
      pencilRootSpace (D := (singularDirichletPartialOperator q).domain)
        (singularDirichletPartialOperator q).domain.subtype
        (lambda • (singularDirichletPartialOperator q).domain.subtype-
          (singularDirichletPartialOperator q).toFun) n := by
  let T := singularDirichletPartialOperator q
  let d : UnitDirichletH1 ≃ₗ[ℂ] T.domain := singularDirichletDomainEquiv
  let J' : T.domain →ₗ[ℂ] UnitDirichletHminus := T.domain.subtype
  let P' : T.domain →ₗ[ℂ] UnitDirichletHminus := lambda • J'-T.toFun
  have hJ (f : UnitDirichletH1) : J' (d f) = singularDirichletDomainInclusion f :=
    singularDirichletDomainEquiv_val f
  have hP (f : UnitDirichletH1) : P' (d f) = singularDirichletPencil q lambda f := by
    change lambda • (singularDirichletDomainEquiv f).val-
      T (singularDirichletDomainEquiv f) =
        lambda • singularDirichletDomainInclusion f-singularDirichletOperator q f
    rw [singularDirichletPartialOperator_apply, singularDirichletDomainEquiv_val]
  have he := pencilRootSpace_equiv (D' := T.domain) (E' := UnitDirichletHminus)
    singularDirichletDomainInclusion.toLinearMap (singularDirichletPencil q lambda).toLinearMap
    J' P' d (LinearEquiv.refl ℂ UnitDirichletHminus) hJ hP n
  ext x
  exact he x

/-- The full native algebraic root space is that of the actual partial operator. -/
theorem singularDirichletRootSpaceTop_eq_partial
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (lambda : ℂ) :
    singularDirichletRootSpaceTop q lambda =
      pencilRootSpaceTop (D := (singularDirichletPartialOperator q).domain)
        (singularDirichletPartialOperator q).domain.subtype
        (lambda • (singularDirichletPartialOperator q).domain.subtype-
          (singularDirichletPartialOperator q).toFun) := by
  unfold singularDirichletRootSpaceTop pencilRootSpaceTop
  exact iSup_congr (fun n => singularDirichletRootSpace_eq_partial q lambda n)

/-- Native domain eigenvectors and base-space first root vectors are linearly equivalent. -/
def singularDirichletEigenspaceRootEquiv
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (lambda : ℂ) :
    singularDirichletEigenspace q lambda ≃ₗ[ℂ] singularDirichletRootSpace q lambda 1 :=
  pencilKerRootEquiv singularDirichletDomainInclusion.toLinearMap
    (singularDirichletPencil q lambda).toLinearMap singularDirichletDomainInclusion_injective

end NLS.KdV
