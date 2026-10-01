import NLS.Poisson.SourceHamiltonianDirection
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! # Jacobi for the actual source Poisson bracket

The source bivector is constant and has its actual bounded Hamiltonian
direction in the source space. Differentiating the bilinear pairing
therefore gives two Hessian terms. Symmetry of the analytic Hessians
cancels all six terms of the Jacobi identity.
-/

noncomputable section
open Complex
open scoped ENNReal
namespace NLS.Poisson
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual bracket derivative is the difference of the two
Hessians evaluated on the actual Hamiltonian directions. -/
theorem fderiv_sourceBracket_apply
    (h2p : (2 : ℝ≥0∞) ≤ p) (F G : CoeffPair p → ℂ) (φ v : CoeffPair p)
    (hF : AnalyticAt ℂ F φ) (hG : AnalyticAt ℂ G φ) :
    (fderiv ℂ (sourceBracket h2p F G) φ) v =
      (fderiv ℂ (fderiv ℂ F) φ) v (sourceHamiltonianVector h2p G φ)-
        (fderiv ℂ (fderiv ℂ G) φ) v (sourceHamiltonianVector h2p F φ) := by
  have hd := (sourceBivector h2p).fderiv_of_bilinear
    hF.fderiv.differentiableAt hG.fderiv.differentiableAt
  change (fderiv ℂ (fun ψ => sourceBivector h2p (fderiv ℂ F ψ) (fderiv ℂ G ψ)) φ) v = _
  rw [hd]
  simp only [add_apply,ContinuousLinearMap.precompR_apply,
    ContinuousLinearMap.precompL_apply,ContinuousLinearMap.compL_apply,ContinuousLinearMap.comp_apply]
  rw [sourceBivector_antisymm h2p (fderiv ℂ F φ) ((fderiv ℂ (fderiv ℂ G) φ) v)]
  simp only [← apply_sourceHamiltonianDirection,sourceHamiltonianVector]
  ring

/-- Jacobi is derived for the literal source bracket of analytic
functionals at every source exponent at least two. -/
theorem sourceBracket_jacobi
    (h2p : (2 : ℝ≥0∞) ≤ p) (F G H : CoeffPair p → ℂ) (φ : CoeffPair p)
    (hF : AnalyticAt ℂ F φ) (hG : AnalyticAt ℂ G φ) (hH : AnalyticAt ℂ H φ) :
    sourceBracket h2p (sourceBracket h2p F G) H φ+
      sourceBracket h2p (sourceBracket h2p G H) F φ+
      sourceBracket h2p (sourceBracket h2p H F) G φ = 0 := by
  rw [← fderiv_apply_sourceHamiltonianVector,← fderiv_apply_sourceHamiltonianVector,
    ← fderiv_apply_sourceHamiltonianVector]
  rw [fderiv_sourceBracket_apply h2p F G φ _ hF hG,
    fderiv_sourceBracket_apply h2p G H φ _ hG hH,
    fderiv_sourceBracket_apply h2p H F φ _ hH hF]
  have hsF := (hF.contDiffAt (n := 2)).isSymmSndFDerivAt (by norm_num)
  have hsG := (hG.contDiffAt (n := 2)).isSymmSndFDerivAt (by norm_num)
  have hsH := (hH.contDiffAt (n := 2)).isSymmSndFDerivAt (by norm_num)
  rw [hsF.eq (sourceHamiltonianVector h2p H φ) (sourceHamiltonianVector h2p G φ),
    hsG.eq (sourceHamiltonianVector h2p H φ) (sourceHamiltonianVector h2p F φ),
    hsH.eq (sourceHamiltonianVector h2p F φ) (sourceHamiltonianVector h2p G φ)]
  ring

end NLS.Poisson
