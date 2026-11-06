import NLS.KdV.HillHminusTraceHamiltonianVector

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
namespace NLS.KdV

/-- The EXACT infinitesimal Gardner bracket evolution in the ACTUAL
indexed physical source direction. The trace energy on the right is
frozen at the original Dirichlet label of THIS basepoint. It is not the
derivative of the trace composed with the moving Dirichlet branch. -/
theorem hillIndexedSource_hminus_Gardner_derivative
    (q : RealPeriodOneHillPotential) (k : ℕ+)
    (F G : PeriodOneHminusOne → ℂ)
    (hF : AnalyticAt ℂ F (hillOriginalHminusSource q.val))
    (hG : AnalyticAt ℂ G (hillOriginalHminusSource q.val)) :
    (fderiv ℂ (NLS.Poisson.hminusGardnerBracket F G) (hillOriginalHminusSource q.val))
        (hillOriginalHminusSource (hillIndexedDiscriminantHamiltonianSource q k k.pos)) =
      (fderiv ℂ (NLS.Poisson.hminusGardnerBracket G
          (fun a => hillHminusDiscriminant a (hillDirichletEnergy q.val q.property.1 q.property.2 k k.pos)))
          (hillOriginalHminusSource q.val))
          (NLS.Poisson.gardnerHamiltonianVector F (hillOriginalHminusSource q.val)) -
        (fderiv ℂ (NLS.Poisson.hminusGardnerBracket F
          (fun a => hillHminusDiscriminant a (hillDirichletEnergy q.val q.property.1 q.property.2 k k.pos)))
          (hillOriginalHminusSource q.val))
          (NLS.Poisson.gardnerHamiltonianVector G (hillOriginalHminusSource q.val)) := by
  let E : ℂ := hillDirichletEnergy q.val q.property.1 q.property.2 k k.pos
  let D : PeriodOneHminusOne → ℂ := fun a => hillHminusDiscriminant a E
  have hD : AnalyticAt ℂ D (hillOriginalHminusSource q.val) :=
    analyticAt_hillHminusDiscriminant_source _ E
  have hj := NLS.Poisson.hminusGardnerBracket_hamiltonian_derivative F G D _ hF hG hD
  rw [hillHminusDiscriminant_HamiltonianVector_eq_neg_source q E,map_neg] at hj
  dsimp only [E,D,hillIndexedDiscriminantHamiltonianSource] at hj ⊢
  linear_combination -hj

end NLS.KdV
