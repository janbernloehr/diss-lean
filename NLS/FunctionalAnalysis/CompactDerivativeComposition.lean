import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Complex.Basic

/-! # Composition of actual derivatives with compact principal remainders -/
noncomputable section
set_option autoImplicit false
namespace NLS

theorem isCompactOperator_fderiv_comp_sub_principals
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedAddCommGroup G] [NormedSpace ℂ G]
    (f : E → F) (g : F → G) (a : E) (Qf : E →L[ℂ] F) (Qg : F →L[ℂ] G)
    (hf : DifferentiableAt ℂ f a) (hg : DifferentiableAt ℂ g (f a))
    (hfc : IsCompactOperator (fderiv ℂ f a-Qf))
    (hgc : IsCompactOperator (fderiv ℂ g (f a)-Qg)) :
    IsCompactOperator (fderiv ℂ (fun x => g (f x)) a-Qg.comp Qf) := by
  change IsCompactOperator (fderiv ℂ (g ∘ f) a-Qg.comp Qf)
  rw [(hg.hasFDerivAt.comp a hf.hasFDerivAt).fderiv]
  have he : (fderiv ℂ g (f a)).comp (fderiv ℂ f a)-Qg.comp Qf=
      (fderiv ℂ g (f a)-Qg).comp (fderiv ℂ f a)+Qg.comp (fderiv ℂ f a-Qf) := by
    ext x
    change fderiv ℂ g (f a) (fderiv ℂ f a x)-Qg (Qf x)=
      (fderiv ℂ g (f a) (fderiv ℂ f a x)-Qg (fderiv ℂ f a x))+Qg (fderiv ℂ f a x-Qf x)
    rw [map_sub]
    abel
  rw [he]
  exact (hgc.comp_clm (fderiv ℂ f a)).add (hfc.clm_comp Qg)

end NLS
