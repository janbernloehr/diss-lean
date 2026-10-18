import NLS.ZakharovShabat.PhysicalAngularPaths
import NLS.ZakharovShabat.SourceAngularOriginalEtaPaths

/-! # Physical Dirichlet paths and integral values

Paths run from the physical left periodic endpoint to the physical
Dirichlet root. The terminal anti-discriminant fixes the sheet at regular
terminals. The definitions contain no source family or source labels.
-/

noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal Classical unitInterval
namespace NLS.ZakharovShabat

/-- Physical path and terminal-sheet data, specified without a source family. -/
structure PhysicalDirichletPathData (m : ℤ) (u : physicalRealSubmodule) where
  circle : PhysicalSpectralCircle u.val m
  terminal_mem : physicalBoundaryRoots .dirichlet u.val m ∈ ball (circle.center:ℂ) circle.radius
  root : ℂ → ℂ
  path : Path (physicalPeriodicLeft u.val m) (physicalBoundaryRoots .dirichlet u.val m)
  admissible : PhysicalAngularPathRootData u.val m (circle.center:ℂ) circle.radius root path
  smooth : ContDiffOn ℝ 1 path.extend (Icc 0 1)
  normalized : l2AntiDiscriminant u.val (physicalBoundaryRoots .dirichlet u.val m) ≠ 0 →
    root (physicalBoundaryRoots .dirichlet u.val m) =
      l2AntiDiscriminant u.val (physicalBoundaryRoots .dirichlet u.val m)

/-- The values of literal physical angular integrals with their endpoint integrability conditions. -/
def physicalAngularIntegralValues (n m : ℤ) (u : physicalRealSubmodule) : Set ℂ :=
  {v | ∃ P : PhysicalDirichletPathData m u,
    CurveIntegrable (holomorphicOneForm (physicalAngularIntegrand n u P.root)) P.path ∧
    (n = m → CurveIntegrable (holomorphicOneForm (physicalEtaModelIntegrand m u.val P.root)) P.path) ∧
    physicalAngularPathIntegral n u P.root P.path = v}

/-- Every real physical source has an isolating circle containing its Dirichlet terminal. -/
theorem exists_physicalSpectralCircle_dirichlet (u : physicalRealSubmodule) (m : ℤ) :
    ∃ C : PhysicalSpectralCircle u.val m,
      physicalBoundaryRoots .dirichlet u.val m ∈ ball (C.center:ℂ) C.radius := by
  let φ := sourcePhysicalL2Equiv.symm u.val
  obtain ⟨N,ε,_,_,V,_,_,hφV,c,hD⟩ :=
    exists_local_source_quantitative_isolating_discs (by simp) (by norm_num) φ u.property
  obtain ⟨a,r,hr,he⟩ := hD.discs m
  refine ⟨PhysicalSpectralCircle.ofSource (hD.periodCircle φ hφV m a r hr he),?_⟩
  rw [physicalBoundaryRoots_eq_source]
  exact SourceLemma12_12Data.original_dirichlet_mem_circle hD φ hφV m a r hr he

end NLS.ZakharovShabat
