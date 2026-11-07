import NLS.KdV.HminusOneDirichletBranches
import NLS.SequenceSpaces.SquaredLatticeDisplacement

/-! The original complex L2 displacement of canonical auxiliary roots
gives the scalar Dirichlet n-times-L2 asymptotic at the SAME signed index. -/
noncomputable section
open Complex
namespace NLS.KdV

/-- At every complex L2 lift and complex energy shift, the full signed
scalar branch has inverse-bracket weighted L2 displacement from n²*pi².
The distant branches are actual simple Dirichlet zeros by the branch theorem;
this asymptotic does not assert a canonical ordering of the central energies. -/
theorem memlp_hillMiuraDirichletEnergy_inverseBracket_error (u : Coeff 2) (c : ℂ) :
    Memℓp (fun n : ℤ => inverseBracketCoefficients n*
      (hillMiuraDirichletEnergy u c n-((Real.pi:ℂ)*n)^2)) 2 := by
  have h := memlp_inverseBracket_squared_lattice_error (Real.pi:ℂ) c
    (hillMiuraDirichletDisplacement u)
  convert h using 1
  funext n
  rw [hillMiuraDirichletDisplacement_apply,hillMiuraDirichletEnergy]
  ring

end NLS.KdV
