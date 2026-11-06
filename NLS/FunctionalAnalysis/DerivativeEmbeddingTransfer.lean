import NLS.SequenceSpaces.CompactHolderDerivative

/-! # Exact native derivative transfer through bounded embeddings -/
noncomputable section
set_option autoImplicit false
open Filter Topology
namespace NLS

/-- The literal derivative in bounded native source and target charts. -/
theorem fderiv_clm_pre_post
    {E F P Q : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup P] [NormedSpace ℂ P] [NormedAddCommGroup Q] [NormedSpace ℂ Q]
    (L : E →L[ℂ] P) (I : Q →L[ℂ] F) (f : P → Q) (q : E)
    (hf : DifferentiableAt ℂ f (L q)) :
    fderiv ℂ (fun x => I (f (L x))) q=I.comp ((fderiv ℂ f (L q)).comp L) :=
  (I.hasFDerivAt.comp q (hf.hasFDerivAt.comp q L.hasFDerivAt)).fderiv

/-- Compact derivative differences survive the EXACT bounded native charts. -/
theorem isCompactOperator_fderiv_clm_pre_post_sub
    {E F P Q : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup P] [NormedSpace ℂ P] [NormedAddCommGroup Q] [NormedSpace ℂ Q]
    (L : E →L[ℂ] P) (I : Q →L[ℂ] F) (f : P → Q) (q : E)
    (hf : DifferentiableAt ℂ f (L q)) (A : P →L[ℂ] Q)
    (hc : IsCompactOperator (fderiv ℂ f (L q)-A)) :
    IsCompactOperator (fderiv ℂ (fun x => I (f (L x))) q-I.comp (A.comp L)) := by
  rw [fderiv_clm_pre_post L I f q hf]
  have he : I.comp ((fderiv ℂ f (L q)).comp L)-I.comp (A.comp L)=
      I.comp ((fderiv ℂ f (L q)-A).comp L) := by
    ext x
    exact (I.map_sub _ _).symm
  rw [he]
  exact (hc.comp_clm L).clm_comp I

/-- An actual commuting complex germ transfers weak Jacobian injectivity
to the SAME native strong derivative. Only the source embedding must be injective. -/
theorem injective_fderiv_of_commuting_embedding
    {E F P Q : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup P] [NormedSpace ℂ P] [NormedAddCommGroup Q] [NormedSpace ℂ Q]
    (L : E →L[ℂ] P) (I : F →L[ℂ] Q) (f : E → F) (g : P → Q) (q : E)
    (hf : DifferentiableAt ℂ f q) (hg : DifferentiableAt ℂ g (L q))
    (he : (fun x => I (f x)) =ᶠ[𝓝 q] (fun x => g (L x)))
    (hL : Function.Injective L) (hgI : Function.Injective (fderiv ℂ g (L q))) :
    Function.Injective (fderiv ℂ f q) := by
  have hd : I.comp (fderiv ℂ f q)=(fderiv ℂ g (L q)).comp L :=
    ((I.hasFDerivAt.comp q hf.hasFDerivAt).congr_of_eventuallyEq he.symm).unique
      (hg.hasFDerivAt.comp q L.hasFDerivAt)
  intro x y hxy
  apply hL
  apply hgI
  calc
    _ = I (fderiv ℂ f q x) := (congrArg (fun A : E →L[ℂ] Q => A x) hd).symm
    _ = I (fderiv ℂ f q y) := congrArg I hxy
    _ = _ := congrArg (fun A : E →L[ℂ] Q => A y) hd

end NLS
