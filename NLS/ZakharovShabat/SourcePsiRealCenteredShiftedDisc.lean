import NLS.ZakharovShabat.SourcePsiRealCenteredOpenGap
import NLS.ZakharovShabat.SourcePsiShiftedDiscLatticeBound
import NLS.ZakharovShabat.SourcePsiNearFreeCollapsedGap

/-!
# Real psi coordinates on shifted selected discs

A sufficiently distant deleted lattice point lies outside a selected
head disc even when that disc is shifted away from its free center.
This gives analyticity of the weighted regular factor on the filled
disc and lets the real-centered mean-value theorem apply.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Shifted-disc lattice separation keeps the deleted free root out
of the entire selected closed disc. -/
theorem deletedFreeRoot_not_mem_shifted_disc
    (n m : ℤ) (hnm : n ≠ m) (c : ℂ) (R : ℝ)
    (hsep : 2*(‖c-(Real.pi : ℂ)*m‖+R) ≤
      Real.pi*|((n-m : ℤ) : ℝ)|) :
    (Real.pi : ℂ)*n ∉ closedBall c R := by
  intro hz
  have hdist := shifted_disc_free_lattice_distance_lower
    n m c R hsep ((Real.pi : ℂ)*n) hz
  have hd : 0 < |((n-m : ℤ) : ℝ)| := by
    have h := Int.one_le_abs (sub_ne_zero.mpr hnm)
    exact_mod_cast (lt_of_lt_of_le zero_lt_one h)
  simp only [sub_self,norm_zero] at hdist
  nlinarith [Real.pi_pos]

/-- The weighted regular psi factor is analytic on a shifted selected
disc when the omitted-root quotient is analytic there and the deleted
free root is separated from the disc. -/
theorem analyticOnNhd_deletedPsi_gapRegularFactor_of_shifted_disc
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n m : ℤ) (hnm : n ≠ m) (a : DeletedCoeff p n)
    (ψ : CoeffPair p) (W : Set (CoeffPair p)) (hψW : ψ ∈ W)
    (hQ : AnalyticOnNhd ℂ
      (sourceSingleRootQuotientJointProduct hp hp1 m)
      (sourceSingleRootQuotientJointDomain hp hp1 W m))
    (c : ℂ) (R : ℝ)
    (hsep : 2*(‖c-(Real.pi : ℂ)*m‖+R) ≤
      Real.pi*|((n-m : ℤ) : ℝ)|)
    (hdom : closedBall c R ⊆
      sourceStandardRootOmittedDomain hp hp1 ψ m) :
    AnalyticOnNhd ℂ
      (fun z => (((n-m : ℤ) : ℂ) *
        sourcePsiGapRegularFactor hp hp1 n m (a : Coeff p) ψ z))
      (closedBall c R) := by
  intro z hz
  have hquot : AnalyticAt ℂ
      (fun w => sourceSingleRootQuotientJointProduct hp hp1 m
        (w,((a : Coeff p),ψ))) z := by
    have hmap : AnalyticAt ℂ
        (fun w : ℂ => (w,((a : Coeff p),ψ))) z :=
      analyticAt_id.prod (analyticAt_const.prod analyticAt_const)
    exact (hQ (z,((a : Coeff p),ψ)) ⟨hψW,hdom hz⟩).comp
      (f := fun w => (w,((a : Coeff p),ψ))) hmap
  have ha : (a : Coeff p) n = 0 := a.property
  have hden : displacedRoots (a : Coeff p) n-z ≠ 0 := by
    rw [show displacedRoots (a : Coeff p) n = (Real.pi : ℂ)*n by
      simp [displacedRoots,ha]]
    apply sub_ne_zero.mpr
    intro he
    exact (deletedFreeRoot_not_mem_shifted_disc n m hnm c R hsep)
      (he ▸ hz)
  have hD : AnalyticAt ℂ
      (fun w => displacedRoots (a : Coeff p) n-w) z :=
    analyticAt_const.sub analyticAt_id
  change AnalyticAt ℂ (fun w =>
    (((n-m : ℤ) : ℂ) *
      (I * sourceSingleRootQuotientJointProduct hp hp1 m
        (w,((a : Coeff p),ψ)) /
        (displacedRoots (a : Coeff p) n-w)))) z
  exact analyticAt_const.mul ((analyticAt_const.mul hquot).div hD hden)

/-- An open real selected gap has a real psi coordinate on a shifted
real-centered disc whenever the deleted index is separated from it. -/
theorem sourcePsiEquationCoordinate_realCentered_im_eq_zero_of_shiftedOpenGap
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n m : ℤ) (hnm : n ≠ m) (a : DeletedCoeff p n)
    (hroots : ∀ k : ℤ, (displacedRoots (a : Coeff p) k).im = 0)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) m).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) m).re)
    (x R : ℝ) (hR : 0 < R)
    (hseg : sourcePeriodicSegment hp hp1 ψ m ⊆ ball (x:ℂ) R)
    (hdom : closedBall (x:ℂ) R ⊆
      sourceStandardRootOmittedDomain hp hp1 ψ m)
    (hcircle : sphere (x:ℂ) R ⊆
      sourceCanonicalRootDomain hp hp1 ψ)
    (hsep : 2*(‖(x:ℂ)-(Real.pi : ℂ)*m‖+R) ≤
      Real.pi*|((n-m : ℤ) : ℝ)|)
    (W : Set (CoeffPair p)) (hψW : ψ ∈ W)
    (hQ : AnalyticOnNhd ℂ
      (sourceSingleRootQuotientJointProduct hp hp1 m)
      (sourceSingleRootQuotientJointDomain hp hp1 W m)) :
    (sourcePsiEquationCoordinate hp hp1 n m (a : Coeff p) ψ (x:ℂ) R).im = 0 := by
  have hreg := analyticOnNhd_deletedPsi_gapRegularFactor_of_shifted_disc
    hp hp1 n m hnm a ψ W hψW hQ (x:ℂ) R hsep hdom
  have havoid : ∀ z ∈ sphere (x:ℂ) R,
      z ≠ displacedRoots (a : Coeff p) n := by
    intro z hz he
    have ha : (a : Coeff p) n = 0 := a.property
    have hroot : displacedRoots (a : Coeff p) n =
        (Real.pi : ℂ)*n := by simp [displacedRoots,ha]
    rw [hroot] at he
    exact (deletedFreeRoot_not_mem_shifted_disc n m hnm (x:ℂ) R hsep)
      (he ▸ sphere_subset_closedBall hz)
  exact sourcePsiEquationCoordinate_realCentered_im_eq_zero_of_openRealGap
    hp hp1 ψ hreal n m (a : Coeff p) hroots hopen x R hR
      hseg hdom hcircle havoid hreg

/-- A collapsed real selected gap has a real psi coordinate on a
shifted selected circle separated from the deleted free root. -/
theorem sourcePsiEquationCoordinate_realCentered_im_eq_zero_of_shiftedCollapsedGap
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n m : ℤ) (hnm : n ≠ m) (a : DeletedCoeff p n)
    (hroots : ∀ k : ℤ, (displacedRoots (a : Coeff p) k).im = 0)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) m = 0)
    (x R : ℝ) (hR : 0 < R)
    (hseg : sourcePeriodicSegment hp hp1 ψ m ⊆ ball (x:ℂ) R)
    (hdom : closedBall (x:ℂ) R ⊆
      sourceStandardRootOmittedDomain hp hp1 ψ m)
    (hcircle : sphere (x:ℂ) R ⊆
      sourceCanonicalRootDomain hp hp1 ψ)
    (hsep : 2*(‖(x:ℂ)-(Real.pi : ℂ)*m‖+R) ≤
      Real.pi*|((n-m : ℤ) : ℝ)|)
    (W : Set (CoeffPair p)) (hψW : ψ ∈ W)
    (hQ : AnalyticOnNhd ℂ
      (sourceSingleRootQuotientJointProduct hp hp1 m)
      (sourceSingleRootQuotientJointDomain hp hp1 W m)) :
    (sourcePsiEquationCoordinate hp hp1 n m
      (a : Coeff p) ψ (x:ℂ) R).im = 0 := by
  let c : ℂ := (x:ℂ)
  let τ : ℂ := sourceStandardRootMidpoint hp hp1 ψ m
  let f : ℂ → ℂ := fun z => (((n-m : ℤ) : ℂ) *
    sourcePsiGapRegularFactor hp hp1 n m (a : Coeff p) ψ z)
  have hτBall : τ ∈ ball c R :=
    hseg (sourcePeriodicMidpoint_mem_segment hp hp1 ψ m)
  have hτdom : τ ∈ sourceStandardRootOmittedDomain hp hp1 ψ m :=
    hdom (ball_subset_closedBall hτBall)
  have hτIm : τ.im = 0 :=
    sourcePeriodicSegment_im_eq_zero_of_realType hp hp1 ψ hreal m τ
      (sourcePeriodicMidpoint_mem_segment hp hp1 ψ m)
  have hτReal : (τ.re:ℂ) = τ := by
    apply Complex.ext
    · rfl
    · simpa using hτIm.symm
  have hfRe : (f τ).re = 0 := by
    have h := sourcePsiGapRegularFactor_weighted_re_eq_zero_of_real_roots
      hp hp1 ψ hreal (a : Coeff p) hroots n m τ.re
        (hτReal ▸ hτdom)
    simpa only [f,hτReal] using h
  have hσIm : (displacedRoots (a : Coeff p) m).im = 0 := hroots m
  have hδIm : (τ-displacedRoots (a : Coeff p) m).im = 0 := by
    simp [Complex.sub_im,hτIm,hσIm]
  have hreg : AnalyticOnNhd ℂ f (closedBall c R) :=
    analyticOnNhd_deletedPsi_gapRegularFactor_of_shifted_disc
      hp hp1 n m hnm a ψ W hψW hQ c R hsep hdom
  have havoid : ∀ z ∈ sphere c R,
      z ≠ displacedRoots (a : Coeff p) n := by
    intro z hz he
    have ha : (a : Coeff p) n = 0 := a.property
    have hroot : displacedRoots (a : Coeff p) n =
        (Real.pi : ℂ)*n := by simp [displacedRoots,ha]
    rw [hroot] at he
    exact (deletedFreeRoot_not_mem_shifted_disc n m hnm c R hsep)
      (he ▸ sphere_subset_closedBall hz)
  have hres := sourcePsiEquationCoordinate_collapsedGap_residue
    hp hp1 n m a ψ hgap c R hR hτBall hcircle havoid hreg
  rw [hres]
  have hprodRe : ((τ-displacedRoots (a : Coeff p) m)*f τ).re = 0 := by
    rw [Complex.mul_re,hδIm,hfRe]
    ring
  have hIprodIm : (I*((τ-displacedRoots (a : Coeff p) m)*f τ)).im = 0 := by
    rw [Complex.mul_im,hprodRe]
    simp
  have heq : (2*(Real.pi:ℂ)*I) *
      (τ-displacedRoots (a : Coeff p) m) * f τ =
      (2*(Real.pi:ℂ)) *
        (I*((τ-displacedRoots (a : Coeff p) m)*f τ)) := by ring
  rw [heq]
  simp [Complex.mul_im,hIprodIm]

/-- The open-gap and collapsed-gap arguments cover every real selected
gap on a sufficiently separated real-centered disc. -/
theorem sourcePsiEquationCoordinate_realCentered_im_eq_zero_of_shiftedRealGap
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n m : ℤ) (hnm : n ≠ m) (a : DeletedCoeff p n)
    (hroots : ∀ k : ℤ, (displacedRoots (a : Coeff p) k).im = 0)
    (x R : ℝ) (hR : 0 < R)
    (hseg : sourcePeriodicSegment hp hp1 ψ m ⊆ ball (x:ℂ) R)
    (hdom : closedBall (x:ℂ) R ⊆
      sourceStandardRootOmittedDomain hp hp1 ψ m)
    (hcircle : sphere (x:ℂ) R ⊆
      sourceCanonicalRootDomain hp hp1 ψ)
    (hsep : 2*(‖(x:ℂ)-(Real.pi : ℂ)*m‖+R) ≤
      Real.pi*|((n-m : ℤ) : ℝ)|)
    (W : Set (CoeffPair p)) (hψW : ψ ∈ W)
    (hQ : AnalyticOnNhd ℂ
      (sourceSingleRootQuotientJointProduct hp hp1 m)
      (sourceSingleRootQuotientJointDomain hp hp1 W m)) :
    (sourcePsiEquationCoordinate hp hp1 n m
      (a : Coeff p) ψ (x:ℂ) R).im = 0 := by
  by_cases hopen :
      (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) m).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) m).re
  · exact sourcePsiEquationCoordinate_realCentered_im_eq_zero_of_shiftedOpenGap
      hp hp1 ψ hreal n m hnm a hroots hopen x R hR hseg hdom
        hcircle hsep W hψW hQ
  · have hgap := sourcePeriodicGap_eq_zero_of_real_not_open
      hp hp1 ψ hreal m hopen
    exact sourcePsiEquationCoordinate_realCentered_im_eq_zero_of_shiftedCollapsedGap
      hp hp1 ψ hreal n m hnm a hroots hgap x R hR hseg hdom
        hcircle hsep W hψW hQ

end NLS.ZakharovShabat
