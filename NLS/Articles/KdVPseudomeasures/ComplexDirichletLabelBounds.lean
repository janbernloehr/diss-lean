import NLS.Articles.KdVPseudomeasures.EndpointDirichletProjectionConvergence
import NLS.Articles.KdVPseudomeasures.SpectralLowerBound
import NLS.KdV.SingularDirichletSector

/-! Uniform bounds for the ENTIRE actual complex Dirichlet central block,
using original weak energy bounds and intrinsic original label ordering. -/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
open NLS.KdV NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue NLS.ComplexAnalysis

/-- The same explicit original norm-ball spectral sector applies to
EVERY native Dirichlet label, including all central repetitions. -/
theorem sourceComplexDirichletLabel_norm_le_on_ball (r : ℝ) (hr : AdmissiblePredualOrder r)
    (R : ℝ) (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) (hq : ‖q‖ ≤ R)
    (hp : IsPeriodicDistribution 1 q.val.toTempered) (n : ℕ+) :
    let a := sourceOriginalComplexPotential r hr q hp
    ‖originalComplexDirichletLabels a n‖ ≤
      2*(originalComplexDirichletLabels a n).re+4*sourceSpectralBound r hr R := by
  intro a
  obtain ⟨g,hg,hgn,_⟩ := exists_normalized_originalComplexDirichlet_eigenfunction a n
  have hg0 : g ≠ 0 := by intro he;rw [he,map_zero,norm_zero] at hgn;norm_num at hgn
  have hb := singularDirichlet_eigenvalue_norm_le a.val _ g hg0 hg
  have hC := singularHillLowerBoundConstant_mono (norm_nonneg (sourceComplexHminusOne r hr q))
    (sourceComplexHminusOne_norm_le_on_ball r hr R q hq)
  exact hb.trans (by dsimp [a,sourceOriginalComplexPotential,sourceSpectralBound];linarith)

/-- Any chosen sufficiently high valid source circle bounds ALL preceding
actual Dirichlet labels, with an explicit uniform bound in the original norm. -/
theorem sourceComplexDirichletLabel_low_norm_le (r : ℝ) (hr : AdmissiblePredualOrder r)
    (R : ℝ) (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) (hq : ‖q‖ ≤ R)
    (hp : IsPeriodicDistribution 1 q.val.toTempered) (N : ℕ+) (n : ℕ+) (hn : n ≤ N)
    (hN : originalComplexDirichletLabels (sourceOriginalComplexPotential r hr q hp) N ∈
      ball (((Real.pi:ℂ)*(N:ℕ))^2) (N:ℝ)) :
    ‖originalComplexDirichletLabels (sourceOriginalComplexPotential r hr q hp) n‖ ≤
      2*freeHillValue (N:ℕ)+2*(N:ℝ)+4*sourceSpectralBound r hr R := by
  let a := sourceOriginalComplexPotential r hr q hp
  have hnorm : ‖originalComplexDirichletLabels a N-(((Real.pi:ℂ)*(N:ℕ))^2)‖ < (N:ℝ) := by
    simpa only [mem_ball,dist_eq_norm] using hN
  have hre := (Complex.re_le_norm (originalComplexDirichletLabels a N-(((Real.pi:ℂ)*(N:ℕ))^2))).trans_lt hnorm
  rw [Complex.sub_re,← freeHillValue_natCast_complex,Complex.ofReal_re] at hre
  have hmono := re_le_of_complexLexLE (monotone_originalComplexDirichletLabels a hn)
  have hsector := sourceComplexDirichletLabel_norm_le_on_ball r hr R q hq hp n
  change ‖originalComplexDirichletLabels a n‖ ≤ _ at hsector ⊢
  linarith

end NLS.Articles.KdVPseudomeasures
