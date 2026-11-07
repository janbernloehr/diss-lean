import NLS.KdV.SingularHillL2Domain

/-! # Full linear eigenspace comparison between the H2 and weak Hill domains

For every complex L2 potential, the already proved regularity recovery
gives a linear equivalence of entire eigenspaces. Existence of one nonzero
eigenfunction or equality of characteristic zero sets would not suffice.
-/
noncomputable section
open scoped ENNReal
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.SmoothPeriodicTest NLS.Fourier.PeriodicFourierLebesgue

def hillSobolevEigenspace (q : Coeff 2) (z : ℂ) : Submodule ℂ HillSobolevDomain :=
  LinearMap.ker (hillOperator q-z • hillDomainToL2).toLinearMap

theorem mem_hillSobolevEigenspace (q : Coeff 2) (z : ℂ) (f : HillSobolevDomain) :
    f ∈ hillSobolevEigenspace q z ↔ hillOperator q f = z • hillDomainToL2 f := by
  change hillOperator q f-z • hillDomainToL2 f=0 ↔ _
  exact sub_eq_zero

def hillL2EigenspaceToOriginal (q : WeightedCoeff SpectralWeight.one.toWeight 2) (z : ℂ) :
    hillSobolevEigenspace (SpectralWeight.one.toCoeff q) z →ₗ[ℂ]
      singularHillEigenspace (hillL2HminusOne q) z where
  toFun f := ⟨hillDomainOriginalH1 f.val,(mem_singularHillEigenspace_iff _ _ _).mpr
    ((hillDomainOriginalH1_eigen_iff q z f.val).mpr
      ((mem_hillSobolevEigenspace _ _ _).mp f.property))⟩
  map_add' f g := by
    apply Subtype.ext
    change hillDomainOriginalH1 (f.val+g.val) = hillDomainOriginalH1 f.val+hillDomainOriginalH1 g.val
    simp only [hillDomainOriginalH1,map_add]
  map_smul' c f := by
    apply Subtype.ext
    change hillDomainOriginalH1 (c • f.val) = c • hillDomainOriginalH1 f.val
    simp only [hillDomainOriginalH1,map_smul]

theorem hillL2EigenspaceToOriginal_bijective (q : WeightedCoeff SpectralWeight.one.toWeight 2) (z : ℂ) :
    Function.Bijective (hillL2EigenspaceToOriginal q z) := by
  constructor
  · intro f g he
    exact Subtype.ext (hillDomainOriginalH1_injective (congrArg Subtype.val he))
  · intro g
    have hg := (mem_singularHillEigenspace_iff _ _ _).mp g.property
    let f := singularHillL2EigenvectorLift q z g.val hg
    have hf : f ∈ hillSobolevEigenspace (SpectralWeight.one.toCoeff q) z := by
      apply (mem_hillSobolevEigenspace _ _ _).mpr
      apply (hillDomainOriginalH1_eigen_iff q z f).mp
      rw [hillDomainOriginalH1_singularHillL2EigenvectorLift]
      exact hg
    refine ⟨⟨f,hf⟩,?_⟩
    apply Subtype.ext
    exact hillDomainOriginalH1_singularHillL2EigenvectorLift q z g.val hg

def hillL2EigenspaceOriginalEquiv (q : WeightedCoeff SpectralWeight.one.toWeight 2) (z : ℂ) :
    hillSobolevEigenspace (SpectralWeight.one.toCoeff q) z ≃ₗ[ℂ]
      singularHillEigenspace (hillL2HminusOne q) z :=
  LinearEquiv.ofBijective (hillL2EigenspaceToOriginal q z) (hillL2EigenspaceToOriginal_bijective q z)

theorem finrank_hillSobolevEigenspace_eq_original (q : WeightedCoeff SpectralWeight.one.toWeight 2) (z : ℂ) :
    Module.finrank ℂ (hillSobolevEigenspace (SpectralWeight.one.toCoeff q) z) =
      Module.finrank ℂ (singularHillEigenspace (hillL2HminusOne q) z) :=
  (hillL2EigenspaceOriginalEquiv q z).finrank_eq

end NLS.KdV
