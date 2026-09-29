import NLS.ZakharovShabat.SourcePsiCandidateEntireVariation

/-!
# Entire variation of the full root product

The limit operator in Lemma 12.10 acts on the undeleted root space.
Its numerator is therefore the variation of the full single-root
product. Restoring any one factor relates this variation to the
deleted psi numerator, and its values at simple roots recover every
coefficient of the direction.
-/

noncomputable section
open Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Variation of the full entire root product in a root direction. -/
def sourcePsiFullProductVariation (a h : Coeff p) (z : ℂ) : ℂ :=
  (fderiv ℂ (fun b : Coeff p => jointSingleSpectralProduct (z,b)) a) h

/-- The root partial derivative agrees with the joint derivative. -/
theorem sourcePsiFullProductVariation_eq_joint
    (hp : p ≠ ⊤) (hp1 : 1 < p) (a h : Coeff p) (z : ℂ) :
    sourcePsiFullProductVariation a h z =
      (fderiv ℂ (jointSingleSpectralProduct (p := p)) (z,a)) (0,h) := by
  unfold sourcePsiFullProductVariation
  rw [NLS.ComplexAnalysis.fderiv_source_section_eq_joint
    (jointSingleSpectralProduct (p := p)) z a
    ((analyticOnNhd_jointSingleSpectralProduct hp hp1
      (z,a) (Set.mem_univ _)).differentiableAt)]
  simp

/-- The full product variation is entire in the spectral variable. -/
theorem analyticOnNhd_sourcePsiFullProductVariation
    (hp : p ≠ ⊤) (hp1 : 1 < p) (a h : Coeff p) :
    AnalyticOnNhd ℂ (sourcePsiFullProductVariation a h) Set.univ := by
  let ev : ((ℂ × Coeff p) →L[ℂ] ℂ) →L[ℂ] ℂ :=
    ContinuousLinearMap.apply ℂ ℂ (0,h)
  have hjoint : AnalyticOnNhd ℂ
      (fun t : ℂ × Coeff p =>
        (fderiv ℂ (jointSingleSpectralProduct (p := p)) t) (0,h)) Set.univ :=
    ev.comp_analyticOnNhd (analyticOnNhd_jointSingleSpectralProduct hp hp1).fderiv
  intro z _
  have hsection := (hjoint (z,a) (Set.mem_univ _)).comp
    (f := fun w : ℂ => (w,a)) (analyticAt_id.prod analyticAt_const)
  convert hsection using 1
  funext w
  exact sourcePsiFullProductVariation_eq_joint hp hp1 a h w

/-- Moving all roots along an affine line gives the same variation. -/
theorem sourcePsiFullProductVariation_eq_line_deriv
    (hp : p ≠ ⊤) (hp1 : 1 < p) (a h : Coeff p) (z : ℂ) :
    sourcePsiFullProductVariation a h z =
      deriv (fun t : ℂ => jointSingleSpectralProduct (z,a+t • h)) 0 := by
  have hsection : DifferentiableAt ℂ
      (fun b : Coeff p => jointSingleSpectralProduct (z,b)) a :=
    ((analyticOnNhd_jointSingleSpectralProduct hp hp1
      (z,a) (Set.mem_univ _)).comp
        (f := fun b : Coeff p => (z,b))
        (analyticAt_const.prod analyticAt_id)).differentiableAt
  have hline : HasDerivAt (fun t : ℂ => a+t • h) h 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const h).const_add a
  exact (hsection.hasFDerivAt.comp_hasDerivAt_of_eq
    (0 : ℂ) hline (by simp)).deriv.symm

/-- Restoring one factor separates its own root motion from the
variation of the deleted numerator. This holds even at collisions. -/
theorem sourcePsiFullProductVariation_eq_deleted_variation
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (k : ℤ) (a h : Coeff p) (z : ℂ) :
    sourcePsiFullProductVariation a h z =
      -(h k * sourcePsiCandidate k (z,a)) +
        (z-displacedRoots a k) * sourcePsiCandidateVariation k a h z := by
  have hsection : DifferentiableAt ℂ
      (fun b : Coeff p => sourcePsiCandidate k (z,b)) a :=
    ((analyticOnNhd_sourcePsiCandidate hp hp1 k
      (z,a) (Set.mem_univ _)).comp
        (f := fun b : Coeff p => (z,b))
        (analyticAt_const.prod analyticAt_id)).differentiableAt
  have hline : HasDerivAt (fun t : ℂ => a+t • h) h 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const h).const_add a
  have hpsi : HasDerivAt (fun t : ℂ => sourcePsiCandidate k (z,a+t • h))
      (sourcePsiCandidateVariation k a h z) 0 :=
    hsection.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℂ) hline (by simp)
  have hrootEq (t : ℂ) :
      z-displacedRoots (a+t • h) k = (z-displacedRoots a k)-t*h k := by
    simp only [displacedRoots, lp.coeFn_add, Pi.add_apply,
      lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
    ring
  have hroot : HasDerivAt (fun t : ℂ => z-displacedRoots (a+t • h) k)
      (-h k) 0 := by
    simp_rw [hrootEq]
    simpa only [Pi.sub_def, id_eq, one_mul, zero_sub] using
      (hasDerivAt_const (0 : ℂ) (z-displacedRoots a k)).sub
      ((hasDerivAt_id (0 : ℂ)).mul_const (h k))
  have heq : (fun t : ℂ => jointSingleSpectralProduct (z,a+t • h)) =
      (fun t : ℂ => (z-displacedRoots (a+t • h) k) *
        sourcePsiCandidate k (z,a+t • h)) := by
    funext t
    rw [jointSingleSpectralProduct_eq_deleted hp hp1 k]
    unfold sourcePsiCandidate
    ring
  rw [sourcePsiFullProductVariation_eq_line_deriv hp hp1, heq]
  simpa [Pi.mul_def] using (hroot.mul hpsi).deriv

/-- At each root, the full variation measures that root's motion. -/
theorem sourcePsiFullProductVariation_at_root
    (hp : p ≠ ⊤) (hp1 : 1 < p) (k : ℤ) (a h : Coeff p) :
    sourcePsiFullProductVariation a h (displacedRoots a k) =
      -(h k * deriv (fun z : ℂ => jointSingleSpectralProduct (z,a))
        (displacedRoots a k)) := by
  rw [sourcePsiFullProductVariation_eq_deleted_variation hp hp1 k]
  rw [deriv_jointSingleSpectralProduct_at_displacedRoot hp hp1 a k]
  simp [sourcePsiCandidate]

/-- A basis direction changes exactly its own factor in the product. -/
theorem sourcePsiFullProductVariation_single
    (hp : p ≠ ⊤) (hp1 : 1 < p) (k : ℤ) (a : Coeff p) (z : ℂ) :
    sourcePsiFullProductVariation a (lp.single p k 1) z =
      -sourcePsiCandidate k (z,a) := by
  have heq : (fun t : ℂ =>
      sourcePsiCandidate k (z,a+t • lp.single p k 1)) =
      (fun _ : ℂ => sourcePsiCandidate k (z,a)) := by
    funext t
    apply sourcePsiCandidate_eq_of_off_index hp hp1
    intro j hj
    simp only [lp.coeFn_add, Pi.add_apply, lp.coeFn_smul, Pi.smul_apply]
    simp [lp.single_apply, hj]
  have hzero : sourcePsiCandidateVariation k a (lp.single p k 1) z = 0 := by
    rw [sourcePsiCandidateVariation_eq_line_deriv hp hp1, heq]
    simp
  rw [sourcePsiFullProductVariation_eq_deleted_variation hp hp1 k, hzero]
  simp

/-- An identically zero full variation forces every coefficient to
vanish when the displaced roots are distinct. -/
theorem sourcePsiFullProductVariation_zero_imp_direction_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p) (a h : Coeff p)
    (hsep : Function.Injective (displacedRoots a))
    (hvariation : ∀ z : ℂ, sourcePsiFullProductVariation a h z = 0) :
    h = 0 := by
  ext k
  have hzero := hvariation (displacedRoots a k)
  rw [sourcePsiFullProductVariation_at_root hp hp1 k a h] at hzero
  have hsimple := deriv_jointSingleSpectralProduct_ne_zero_of_distinct
    hp hp1 a k (fun j hj h => hj (hsep h).symm)
  simpa using (mul_eq_zero.mp (neg_eq_zero.mp hzero)).resolve_right hsimple

end NLS.ZakharovShabat
