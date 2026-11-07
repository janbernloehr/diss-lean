import NLS.Poisson.GardnerHamiltonianDirection
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! The literal scalar unit-period Gardner bracket satisfies Jacobi.
The proof uses its actual bounded Hamiltonian directions and symmetry
of the complete analytic Hessians on H-minus-one. -/
noncomputable section
open Complex
open scoped ENNReal
namespace NLS.Poisson

theorem fderiv_hminusGardnerBracket_apply (F G : WeightedCoeff (Weight.sobolev (-1)) 2 → ℂ)
    (q v : WeightedCoeff (Weight.sobolev (-1)) 2) (hF : AnalyticAt ℂ F q) (hG : AnalyticAt ℂ G q) :
    (fderiv ℂ (hminusGardnerBracket F G) q) v=
      (fderiv ℂ (fderiv ℂ F) q) v (gardnerHamiltonianVector G q)-
        (fderiv ℂ (fderiv ℂ G) q) v (gardnerHamiltonianVector F q) := by
  have hd := gardnerCotangentBivector.fderiv_of_bilinear
    hF.fderiv.differentiableAt hG.fderiv.differentiableAt
  change (fderiv ℂ (fun a => gardnerCotangentBivector (fderiv ℂ F a) (fderiv ℂ G a)) q) v=_
  rw [hd]
  simp only [add_apply,ContinuousLinearMap.precompR_apply,
    ContinuousLinearMap.precompL_apply,ContinuousLinearMap.compL_apply,ContinuousLinearMap.comp_apply]
  rw [gardnerCotangentBivector_antisymm (fderiv ℂ F q) ((fderiv ℂ (fderiv ℂ G) q) v)]
  simp only [← apply_gardnerHamiltonianDirection,gardnerHamiltonianVector]
  ring

theorem hminusGardnerBracket_jacobi (F G H : WeightedCoeff (Weight.sobolev (-1)) 2 → ℂ)
    (q : WeightedCoeff (Weight.sobolev (-1)) 2)
    (hF : AnalyticAt ℂ F q) (hG : AnalyticAt ℂ G q) (hH : AnalyticAt ℂ H q) :
    hminusGardnerBracket (hminusGardnerBracket F G) H q+
      hminusGardnerBracket (hminusGardnerBracket G H) F q+
      hminusGardnerBracket (hminusGardnerBracket H F) G q=0 := by
  rw [← fderiv_apply_gardnerHamiltonianVector,← fderiv_apply_gardnerHamiltonianVector,
    ← fderiv_apply_gardnerHamiltonianVector]
  rw [fderiv_hminusGardnerBracket_apply F G q _ hF hG,
    fderiv_hminusGardnerBracket_apply G H q _ hG hH,
    fderiv_hminusGardnerBracket_apply H F q _ hH hF]
  have hsF := (hF.contDiffAt (n := 2)).isSymmSndFDerivAt (by norm_num)
  have hsG := (hG.contDiffAt (n := 2)).isSymmSndFDerivAt (by norm_num)
  have hsH := (hH.contDiffAt (n := 2)).isSymmSndFDerivAt (by norm_num)
  rw [hsF.eq (gardnerHamiltonianVector H q) (gardnerHamiltonianVector G q),
    hsG.eq (gardnerHamiltonianVector H q) (gardnerHamiltonianVector F q),
    hsH.eq (gardnerHamiltonianVector F q) (gardnerHamiltonianVector G q)]
  ring

end NLS.Poisson
