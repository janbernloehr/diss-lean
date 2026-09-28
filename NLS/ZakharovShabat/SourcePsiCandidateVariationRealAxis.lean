import NLS.ZakharovShabat.SourcePsiCandidateEntireVariation
import NLS.ZakharovShabat.SourcePsiContourConjugation
import NLS.ComplexAnalysis.LocalRealAxisDerivative

/-!
# Reality of the entire psi numerator variation

For real displaced roots and a real root-sequence direction, the
entire numerator variation is real on the real spectral axis. This is
the reality condition used with the real-gap mean-value argument in
Lemma 12.7.
-/

noncomputable section
open Complex ComplexConjugate Filter
open scoped ENNReal Topology
namespace NLS.ZakharovShabat

/-- A real affine direction preserves the real displaced-root locus. -/
theorem displacedRoots_add_real_direction_im_eq_zero
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (a h : Coeff p)
    (hroots : ∀ j : ℤ, (displacedRoots a j).im = 0)
    (hreal : ∀ j : ℤ, (h j).im = 0)
    (t : ℝ) (j : ℤ) :
    (displacedRoots (a+(t:ℂ) • h) j).im = 0 := by
  have ha : (a j).im = 0 := by
    simpa [displacedRoots] using hroots j
  have hsmul : (((t:ℂ) • h : Coeff p) j) = (t:ℂ) * h j := by
    simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  simp only [displacedRoots, lp.coeFn_add, Pi.add_apply, hsmul,
    Complex.add_im, Complex.mul_im]
  simp [ha, hreal j]

/-- The entire numerator variation is real on the real spectral axis
when both the base roots and the direction are real. -/
theorem sourcePsiCandidateVariation_im_eq_zero_of_real_data
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n : ℤ) (a h : Coeff p)
    (hroots : ∀ j : ℤ, (displacedRoots a j).im = 0)
    (hreal : ∀ j : ℤ, (h j).im = 0)
    (x : ℝ) :
    (sourcePsiCandidateVariation n a h (x:ℂ)).im = 0 := by
  let g : ℂ → ℂ := fun t =>
    sourcePsiCandidate n ((x:ℂ),a+t • h)
  have hg : DifferentiableAt ℂ g 0 := by
    have hline : AnalyticAt ℂ
        (fun t : ℂ => ((x:ℂ),a+t • h)) 0 :=
      analyticAt_const.prod
        (analyticAt_const.add (analyticAt_id.smul analyticAt_const))
    exact ((analyticOnNhd_sourcePsiCandidate hp hp1 n
      ((x:ℂ),a) (Set.mem_univ _)).comp_of_eq hline
        (by simp)).differentiableAt
  have hgreal (t : ℝ) : (g (t:ℂ)).im = 0 := by
    have hrootst (j : ℤ) :
        (displacedRoots (a+(t:ℂ) • h) j).im = 0 :=
      displacedRoots_add_real_direction_im_eq_zero
        a h hroots hreal t j
    have hconj := sourcePsiCandidate_conj_of_real_roots
      hp hp1 n (a+(t:ℂ) • h) hrootst (x:ℂ)
    have heq : conj (g (t:ℂ)) = g (t:ℂ) := by
      simpa [g] using hconj.symm
    exact Complex.conj_eq_iff_im.mp heq
  have hderiv : HasDerivAt g
      (sourcePsiCandidateVariation n a h (x:ℂ)) 0 := by
    rw [sourcePsiCandidateVariation_eq_line_deriv hp hp1]
    exact hg.hasDerivAt
  exact NLS.ComplexAnalysis.HasDerivAt.im_eq_zero_of_eventually_real
    g _ 0 hderiv (Filter.Eventually.of_forall hgreal)

end NLS.ZakharovShabat
