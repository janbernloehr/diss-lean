import NLS.ZakharovShabat.SourcePsiCandidateSimpleRoots
import NLS.ComplexAnalysis.MixedSpectralSourceDerivative

/-!
# Entire variation of the psi numerator

Lemma 12.7 differentiates the entire numerator in a deleted-root
direction. Joint analyticity makes this variation entire in the
spectral parameter. The definition below also agrees with the ordinary
derivative along the affine root-sequence line.
-/

noncomputable section
open Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The entire numerator variation `φₙ` in a root-sequence direction. -/
def sourcePsiCandidateVariation
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (n : ℤ) (a h : Coeff p) (z : ℂ) : ℂ :=
  (fderiv ℂ (fun b : Coeff p => sourcePsiCandidate n (z,b)) a) h

/-- The source partial derivative is the joint derivative applied in
the root-sequence direction. -/
theorem sourcePsiCandidateVariation_eq_joint
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n : ℤ) (a h : Coeff p) (z : ℂ) :
    sourcePsiCandidateVariation n a h z =
      (fderiv ℂ (sourcePsiCandidate (p := p) n) (z,a)) (0,h) := by
  unfold sourcePsiCandidateVariation
  rw [NLS.ComplexAnalysis.fderiv_source_section_eq_joint
    (sourcePsiCandidate (p := p) n) z a
    ((analyticOnNhd_sourcePsiCandidate hp hp1 n
      (z,a) (Set.mem_univ _)).differentiableAt)]
  simp

/-- For fixed root data and direction, the numerator variation is an
entire function of the spectral parameter. -/
theorem analyticOnNhd_sourcePsiCandidateVariation
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n : ℤ) (a h : Coeff p) :
    AnalyticOnNhd ℂ (sourcePsiCandidateVariation n a h) Set.univ := by
  let ev : ((ℂ × Coeff p) →L[ℂ] ℂ) →L[ℂ] ℂ :=
    ContinuousLinearMap.apply ℂ ℂ (0,h)
  have hjoint : AnalyticOnNhd ℂ
      (fun t : ℂ × Coeff p =>
        (fderiv ℂ (sourcePsiCandidate (p := p) n) t) (0,h)) Set.univ :=
    ev.comp_analyticOnNhd (analyticOnNhd_sourcePsiCandidate hp hp1 n).fderiv
  intro z _
  have hsection := (hjoint (z,a) (Set.mem_univ _)).comp
    (f := fun w : ℂ => (w,a))
    (analyticAt_id.prod analyticAt_const)
  convert hsection using 1
  funext w
  exact sourcePsiCandidateVariation_eq_joint hp hp1 n a h w

/-- The variation is the derivative obtained by moving the entire
root sequence along the chosen direction. -/
theorem sourcePsiCandidateVariation_eq_line_deriv
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n : ℤ) (a h : Coeff p) (z : ℂ) :
    sourcePsiCandidateVariation n a h z =
      deriv (fun t : ℂ => sourcePsiCandidate n (z,a+t • h)) 0 := by
  have hsection : DifferentiableAt ℂ
      (fun b : Coeff p => sourcePsiCandidate n (z,b)) a := by
    exact ((analyticOnNhd_sourcePsiCandidate hp hp1 n
      (z,a) (Set.mem_univ _)).comp
        (f := fun b : Coeff p => (z,b))
        (analyticAt_const.prod analyticAt_id)).differentiableAt
  have hline : HasDerivAt (fun t : ℂ => a+t • h) h 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const h).const_add a
  have hcomp := hsection.hasFDerivAt.comp_hasDerivAt_of_eq
    (0 : ℂ) hline (by simp)
  exact hcomp.deriv.symm

/-- At a retained zero, the entire variation records the motion of
that root times the spectral derivative of the numerator. -/
theorem sourcePsiCandidateVariation_at_retained_root
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n k : ℤ) (hkn : k ≠ n) (a h : Coeff p) :
    sourcePsiCandidateVariation n a h (displacedRoots a k) =
      - (h k * deriv (fun z : ℂ => sourcePsiCandidate n (z,a))
          (displacedRoots a k)) := by
  rw [sourcePsiCandidateVariation_eq_joint hp hp1]
  exact fderiv_sourcePsiCandidate_root_direction_eq_deriv
    hp hp1 n k hkn a h

/-- If the entire numerator variation vanishes, distinct retained
roots recover every coefficient of a deleted direction. -/
theorem sourcePsiCandidateVariation_zero_imp_deleted_direction_zero
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n : ℤ) (a h : Coeff p)
    (hsep : Function.Injective (displacedRoots a))
    (hdeleted : h n = 0)
    (hvariation : ∀ z : ℂ, sourcePsiCandidateVariation n a h z = 0) :
    h = 0 := by
  apply sourcePsiCandidate_direction_eq_zero_of_root_variation_zero
    hp hp1 n a h hsep hdeleted
  intro k hkn
  rw [← sourcePsiCandidateVariation_eq_joint hp hp1]
  exact hvariation (displacedRoots a k)

/-- The same uniqueness conclusion on the dissertation's deleted
`ℓᵖ` parameter space, under its isolating-disc root placement. -/
theorem sourcePsiCandidateVariation_zero_imp_deletedCoeff_zero
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (N : ℕ) (ε : ℝ) (n : ℤ)
    (a h : DeletedCoeff p n)
    (hroots : ∀ k : ℤ,
      displacedRoots (a : Coeff p) k ∈
        sourceIsolatingDisc hp hp1 φ N ε k)
    (hdisjoint : ∀ i j : ℤ, i ≠ j →
      Disjoint (sourceIsolatingDisc hp hp1 φ N ε i)
        (sourceIsolatingDisc hp hp1 φ N ε j))
    (hvariation : ∀ z : ℂ,
      sourcePsiCandidateVariation n (a : Coeff p) (h : Coeff p) z = 0) :
    h = 0 := by
  have hsep := displacedRoots_injective_of_isolatingDiscs
    hp hp1 φ N ε (a : Coeff p) hroots hdisjoint
  have hn : (h : Coeff p) n = 0 := h.property
  have hzero := sourcePsiCandidateVariation_zero_imp_deleted_direction_zero
    hp hp1 n (a : Coeff p) (h : Coeff p) hsep hn hvariation
  exact Subtype.ext hzero

end NLS.ZakharovShabat
