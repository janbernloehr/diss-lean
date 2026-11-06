import NLS.SequenceSpaces.MeanZeroWeightedReality

/-! # The physical real mean-zero normalized Hilbert space

The fixed space uses conjugate Fourier reflection, retaining the actual
physical reality convention at every symmetric weighted Sobolev order.
The bounded real projection permits real analytic restriction of actual
complex inverse germs without changing their coordinate functions.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
namespace NLS

theorem deletedL2Conjugation_add (a b : DeletedCoeff 2 0) :
    deletedL2Conjugation (a+b)=deletedL2Conjugation a+deletedL2Conjugation b :=
  Subtype.ext (periodOneL2Conjugation_add a.val b.val)

theorem deletedL2Conjugation_smul_real (r : ℝ) (a : DeletedCoeff 2 0) :
    deletedL2Conjugation (r • a)=r • deletedL2Conjugation a := by
  apply Subtype.ext
  change periodOneL2Conjugation ((r : ℂ) • a.val)=(r : ℂ) • periodOneL2Conjugation a.val
  rw [periodOneL2Conjugation_smul,conj_ofReal]

/-- Physical real normalized mean-zero sequences as an actual closed
real subspace of the ORIGINAL complex deleted Hilbert space. -/
def physicalRealDeletedSubmodule : Submodule ℝ (DeletedCoeff 2 0) where
  carrier := {a | deletedL2Conjugation a=a}
  zero_mem' := deletedL2Conjugation_zero
  add_mem' := by
    intro a b ha hb
    change deletedL2Conjugation (a+b)=a+b
    rw [deletedL2Conjugation_add,ha,hb]
  smul_mem' := by
    intro r a ha
    change deletedL2Conjugation (r • a)=r • a
    rw [deletedL2Conjugation_smul_real,ha]

@[simp] theorem mem_physicalRealDeletedSubmodule (a : DeletedCoeff 2 0) :
    a∈physicalRealDeletedSubmodule ↔ deletedL2Conjugation a=a := Iff.rfl

theorem isClosed_physicalRealDeletedSubmodule :
    IsClosed (physicalRealDeletedSubmodule : Set (DeletedCoeff 2 0)) :=
  isClosed_eq isometry_deletedL2Conjugation.continuous continuous_id

instance : CompleteSpace physicalRealDeletedSubmodule :=
  isClosed_physicalRealDeletedSubmodule.completeSpace_coe

/-- Actual physical conjugation, viewed as a bounded REAL linear map. -/
def deletedL2ConjugationRealCLM : DeletedCoeff 2 0 →L[ℝ] DeletedCoeff 2 0 :=
  LinearMap.mkContinuous
    { toFun := deletedL2Conjugation
      map_add' := deletedL2Conjugation_add
      map_smul' := deletedL2Conjugation_smul_real }
    1 (by intro a; change ‖deletedL2Conjugation a‖≤1*‖a‖; rw [norm_deletedL2Conjugation,one_mul])

/-- The physical real part in the exact normalized deleted space. -/
def deletedPhysicalRealPartCLM : DeletedCoeff 2 0 →L[ℝ] DeletedCoeff 2 0 :=
  (1/2 : ℝ) • (ContinuousLinearMap.id ℝ _+deletedL2ConjugationRealCLM)

@[simp] theorem deletedPhysicalRealPartCLM_apply (a : DeletedCoeff 2 0) :
    deletedPhysicalRealPartCLM a=(1/2 : ℝ) • (a+deletedL2Conjugation a) := rfl

theorem deletedPhysicalRealPartCLM_fixed (a : DeletedCoeff 2 0) :
    deletedL2Conjugation (deletedPhysicalRealPartCLM a)=deletedPhysicalRealPartCLM a := by
  rw [deletedPhysicalRealPartCLM_apply,deletedL2Conjugation_smul_real,
    deletedL2Conjugation_add,deletedL2Conjugation_involutive]
  rw [add_comm a]

/-- Bounded projection onto the ACTUAL physical real slice. -/
def physicalRealDeletedProjection : DeletedCoeff 2 0 →L[ℝ] physicalRealDeletedSubmodule :=
  deletedPhysicalRealPartCLM.codRestrict physicalRealDeletedSubmodule deletedPhysicalRealPartCLM_fixed

@[simp] theorem physicalRealDeletedProjection_coe (a : physicalRealDeletedSubmodule) :
    physicalRealDeletedProjection a.val=a := by
  apply Subtype.ext
  change (1/2 : ℝ) • (a.val+deletedL2Conjugation a.val)=a.val
  rw [a.property]
  module

/-- Real restriction of a complex germ in its ACTUAL physical real
Banach topology, using the fixed bounded projection. -/
def physicalRealDeletedRestriction (F : DeletedCoeff 2 0 → DeletedCoeff 2 0) :
    physicalRealDeletedSubmodule → physicalRealDeletedSubmodule :=
  fun a => physicalRealDeletedProjection (F a.val)

private theorem analytic_physical_real_linear_transport
    {E F G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F]
    [NormedAddCommGroup G] [NormedSpace ℂ G] [NormedSpace ℝ G] [IsScalarTower ℝ ℂ G]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (J : E →L[ℝ] F) (L : G →L[ℝ] H) (f : F → G) (a : E)
    (hf : AnalyticAt ℂ f (J a)) :
    AnalyticAt ℝ (fun b => L (f (J b))) a := by
  exact (L.analyticAt _).comp (f := fun b => f (J b))
    ((hf.restrictScalars (𝕜 := ℝ)).comp (J.analyticAt a))

theorem analyticAt_physicalRealDeletedRestriction
    {F : DeletedCoeff 2 0 → DeletedCoeff 2 0} {a : physicalRealDeletedSubmodule}
    (hF : AnalyticAt ℂ F a.val) :
    AnalyticAt ℝ (physicalRealDeletedRestriction F) a := by
  simpa only [physicalRealDeletedRestriction] using!
    analytic_physical_real_linear_transport
      (E := physicalRealDeletedSubmodule) (F := DeletedCoeff 2 0)
      (G := DeletedCoeff 2 0) (H := physicalRealDeletedSubmodule)
      physicalRealDeletedSubmodule.subtypeL physicalRealDeletedProjection F a hF

end NLS
