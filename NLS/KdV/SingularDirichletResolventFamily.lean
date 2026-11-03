import NLS.KdV.SingularDirichletResolvent

/-! # Native Dirichlet resolvent dependence on the full original H-minus-one potential

The normalization is fixed once, independently of potential and energy.
Analyticity takes values in the full operator norms of the actual native
H1 domain and its full continuous dual base.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue
-- Fix the native submodule norm instances before forming nested operator spaces.
local instance dirichletResolventFamilyH1NormedGroup : NormedAddCommGroup UnitDirichletH1 := unitDirichletSubspace.normedAddCommGroup
local instance dirichletResolventFamilyH1NormedSpace : NormedSpace ℂ UnitDirichletH1 := unitDirichletSubspace.normedSpace
local instance dirichletResolventFamilyBaseNormedGroup : NormedAddCommGroup UnitDirichletHminus := inferInstance
local instance dirichletResolventFamilyBaseNormedSpace : NormedSpace ℂ UnitDirichletHminus := inferInstance

/-- Joint norm analyticity of the full native Dirichlet pencil. -/
theorem analyticAt_singularDirichletNormalizedPencil_joint
    (p : FourierLebesgueSpace (2:ℝ) (-1) 2 × ℂ) :
    AnalyticAt ℂ (fun x : FourierLebesgueSpace (2:ℝ) (-1) 2 × ℂ =>
      singularDirichletNormalizedPencil x.1 x.2) p := by
  have hV := ((hminusOneMultiplicationFamily (L := 2)).analyticAt p.1).comp analyticAt_fst
  have hA : AnalyticAt ℂ (fun x : FourierLebesgueSpace (2:ℝ) (-1) 2 × ℂ =>
      singularDirichletOperator x.1) p :=
    SchurComplement.analyticAt_compCLM analyticAt_const
      (SchurComplement.analyticAt_compCLM (analyticAt_const.add hV) analyticAt_const)
  have hJ : AnalyticAt ℂ (fun x : FourierLebesgueSpace (2:ℝ) (-1) 2 × ℂ =>
      x.2 • singularDirichletDomainInclusion) p :=
    analyticAt_snd.smul analyticAt_const
  exact SchurComplement.analyticAt_compCLM analyticAt_const (hA.sub hJ)

/-- The complete joint native resolvent locus is open. -/
theorem isOpen_singularDirichletJointResolvent :
    IsOpen {p : FourierLebesgueSpace (2:ℝ) (-1) 2 × ℂ |
      p.2 ∈ singularDirichletResolventSet p.1} := by
  have hc : Continuous (fun p : FourierLebesgueSpace (2:ℝ) (-1) 2 × ℂ =>
      singularDirichletNormalizedPencil p.1 p.2) :=
    continuous_iff_continuousAt.mpr fun p =>
      (analyticAt_singularDirichletNormalizedPencil_joint p).continuousAt
  have he : {p : FourierLebesgueSpace (2:ℝ) (-1) 2 × ℂ |
      p.2 ∈ singularDirichletResolventSet p.1} =
      (fun p => singularDirichletNormalizedPencil p.1 p.2) ⁻¹' {T | IsUnit T} := by
    ext p
    exact mem_singularDirichletResolventSet_iff_isUnit p.1 p.2
  rw [he]
  exact Units.isOpen.preimage hc

/-- Every valid pair has a jointly analytic inverse into the entire zero-trace H1 domain. -/
theorem analyticAt_singularDirichletResolventToH1_joint
    (p : FourierLebesgueSpace (2:ℝ) (-1) 2 × ℂ)
    (hp : p.2 ∈ singularDirichletResolventSet p.1) :
    AnalyticAt ℂ (fun x : FourierLebesgueSpace (2:ℝ) (-1) 2 × ℂ =>
      singularDirichletResolventToH1 x.1 x.2) p := by
  have hi := (analyticOnNhd_inverse (𝕜 := ℂ) _
    ((mem_singularDirichletResolventSet_iff_isUnit p.1 p.2).mp hp)).comp
      (f := fun x : FourierLebesgueSpace (2:ℝ) (-1) 2 × ℂ =>
        singularDirichletNormalizedPencil x.1 x.2)
      (analyticAt_singularDirichletNormalizedPencil_joint p)
  exact SchurComplement.analyticAt_compCLM hi analyticAt_const

/-- Joint analyticity of the actual inverse on the full H-minus-one base. -/
theorem analyticAt_singularDirichletBaseResolvent_joint
    (p : FourierLebesgueSpace (2:ℝ) (-1) 2 × ℂ)
    (hp : p.2 ∈ singularDirichletResolventSet p.1) :
    AnalyticAt ℂ (fun x : FourierLebesgueSpace (2:ℝ) (-1) 2 × ℂ =>
      singularDirichletBaseResolvent x.1 x.2) p :=
  SchurComplement.analyticAt_compCLM analyticAt_const
    (analyticAt_singularDirichletResolventToH1_joint p hp)

end NLS.KdV
