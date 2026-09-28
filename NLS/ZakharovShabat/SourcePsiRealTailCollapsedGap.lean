import NLS.ZakharovShabat.SourcePsiGlobalTailQuarterDisc
import NLS.ZakharovShabat.SourcePsiNearFreeCollapsedGap

/-!
# Reality of collapsed-gap psi tail coordinates

At a collapsed real gap, the selected standard root is linear. Its
contour equation is a Cauchy residue; the regular factor is imaginary
and the midpoint-to-root displacement is real, so the coordinate is
real on the free eighth-π circle.
-/

noncomputable section
open Set Metric Complex
open NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- A collapsed real gap with a free-centered analytic disc has a real
psi equation coordinate on its free eighth-π circle. -/
theorem sourcePsiEquationCoordinate_freeEighth_im_eq_zero_of_collapsedRealGap
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n m : ℤ) (hnm : n ≠ m) (a : DeletedCoeff p n)
    (hroots : ∀ k : ℤ, (displacedRoots (a : Coeff p) k).im = 0)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) m = 0)
    (W : Set (CoeffPair p)) (hψW : ψ ∈ W)
    (hQ : AnalyticOnNhd ℂ
      (sourceSingleRootQuotientJointProduct hp hp1 m)
      (sourceSingleRootQuotientJointDomain hp hp1 W m))
    (hdom : closedBall ((Real.pi : ℂ)*m) (Real.pi/8) ⊆
      sourceStandardRootOmittedDomain hp hp1 ψ m)
    (hcircle : sphere ((Real.pi : ℂ)*m) (Real.pi/8) ⊆
      sourceCanonicalRootDomain hp hp1 ψ)
    (hmid : ‖sourceStandardRootMidpoint hp hp1 ψ m -
      (Real.pi : ℂ)*m‖ ≤ Real.pi/64) :
    (sourcePsiEquationCoordinate hp hp1 n m (a : Coeff p) ψ
      ((Real.pi : ℂ)*m) (Real.pi/8)).im = 0 := by
  let c : ℂ := (Real.pi : ℂ)*m
  let τ : ℂ := sourceStandardRootMidpoint hp hp1 ψ m
  let f : ℂ → ℂ := fun z => (((n-m : ℤ) : ℂ) *
    sourcePsiGapRegularFactor hp hp1 n m (a : Coeff p) ψ z)
  have hτBall : τ ∈ ball c (Real.pi/8) := by
    rw [mem_ball,dist_eq_norm]
    have hτnorm : ‖τ-c‖ ≤ Real.pi/64 := hmid
    exact hτnorm.trans_lt (by nlinarith [Real.pi_pos])
  have hτdom : τ ∈ sourceStandardRootOmittedDomain hp hp1 ψ m :=
    hdom (ball_subset_closedBall hτBall)
  have hτseg : τ ∈ sourcePeriodicSegment hp hp1 ψ m :=
    sourcePeriodicMidpoint_mem_segment hp hp1 ψ m
  have hτIm : τ.im = 0 :=
    sourcePeriodicSegment_im_eq_zero_of_realType hp hp1 ψ hreal m τ hτseg
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
  have hreg : AnalyticOnNhd ℂ f (closedBall c (Real.pi/8)) :=
    analyticOnNhd_deletedPsi_gapRegularFactor_of_omitted_disc
      hp hp1 n m hnm a ψ W hψW hQ (Real.pi/8)
        (by nlinarith [Real.pi_pos]) hdom
  have havoid : ∀ z ∈ sphere c (Real.pi/8),
      z ≠ displacedRoots (a : Coeff p) n := by
    intro z hz
    have ha : (a : Coeff p) n = 0 := a.property
    rw [show displacedRoots (a : Coeff p) n =
      (Real.pi : ℂ)*n by simp [displacedRoots,ha]]
    exact freeCircle_point_ne_freeCenter m n (Real.pi/8)
      (by positivity) (by nlinarith [Real.pi_pos]) z hz
  have hres := sourcePsiEquationCoordinate_collapsedGap_residue
    hp hp1 n m a ψ hgap c (Real.pi/8) (by positivity)
      hτBall hcircle havoid hreg
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

/-- On one source neighborhood, every sufficiently distant collapsed
real gap has a real psi equation coordinate for every real root input. -/
theorem exists_local_sourcePsi_realTailCollapsedGap_coordinates
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ K : ℕ, ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∀ ψ ∈ V, IsRealType (CoeffPair.toMax p ψ) →
        ∀ n : ℤ, ∀ a : DeletedCoeff p n,
          (∀ k : ℤ, (displacedRoots (a : Coeff p) k).im = 0) →
            ∀ m : ℤ, K ≤ m.natAbs →
              canonicalPeriodicGap hp hp1 (periodOnePotential ψ)
                (periodOnePotential_mem ψ) m = 0 →
                (sourcePsiEquationCoordinate hp hp1 n m
                  (a : Coeff p) ψ ((Real.pi : ℂ)*m) (Real.pi/8)).im = 0 := by
  obtain ⟨Kdom,Vdom,hVdomOpen,hφVdom,hdom⟩ :=
    exists_local_sourcePsi_tailQuarterDisc_omittedDomain hp hp1 φ hφ
  obtain ⟨Ksmall,Vsmall,hVsmallOpen,hφVsmall,hsmall⟩ :=
    exists_local_sourcePeriodicMidpointGap_tiny_tail hp hp1 φ
  obtain ⟨W,hWopen,_,hrealW,hQ⟩ :=
    exists_global_source_analytic_singleRootQuotient hp hp1
  let K : ℕ := max Kdom Ksmall
  let V : Set (CoeffPair p) := Vdom ∩ Vsmall ∩ W
  have hVopen : IsOpen V :=
    (hVdomOpen.inter hVsmallOpen).inter hWopen
  have hφV : φ ∈ V := ⟨⟨hφVdom,hφVsmall⟩,hrealW hφ⟩
  refine ⟨K,V,hVopen,hφV,?_⟩
  intro ψ hψ hreal n a hroots m hm hgap
  have hmDom : Kdom ≤ m.natAbs := by dsimp [K] at hm; omega
  have hmSmall : Ksmall ≤ m.natAbs := by dsimp [K] at hm; omega
  have hdomQuarter := hdom ψ hψ.1.1 m hmDom
  obtain ⟨hmid,hgapsmall⟩ := hsmall ψ hψ.1.2 m hmSmall
  have hseg : sourcePeriodicSegment hp hp1 ψ m ⊆
      ball ((Real.pi : ℂ)*m) (Real.pi/8) :=
    sourcePeriodicSegment_subset_free_eighth_ball hp hp1 ψ m hmid hgapsmall
  have hdomEighth : closedBall ((Real.pi : ℂ)*m) (Real.pi/8) ⊆
      sourceStandardRootOmittedDomain hp hp1 ψ m :=
    (closedBall_subset_closedBall
      (by nlinarith [Real.pi_pos])).trans hdomQuarter
  have hcircle : sphere ((Real.pi : ℂ)*m) (Real.pi/8) ⊆
      sourceCanonicalRootDomain hp hp1 ψ :=
    sourceCanonicalRootDomain_of_enclosingCircle hp hp1 ψ m
      ((Real.pi : ℂ)*m) (Real.pi/8) hseg hdomEighth
  by_cases hmn : m = n
  · subst m
    simp [sourcePsiEquationCoordinate]
  · exact sourcePsiEquationCoordinate_freeEighth_im_eq_zero_of_collapsedRealGap
      hp hp1 ψ hreal n m (Ne.symm hmn) a hroots hgap
        W hψ.2 (hQ m).2 hdomEighth hcircle hmid

/-- Every sufficiently distant psi equation coordinate is real on
the real source and real root-input locus, whether its selected gap
is open or collapsed. -/
theorem exists_local_sourcePsi_realTail_coordinates
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ K : ℕ, ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∀ ψ ∈ V, IsRealType (CoeffPair.toMax p ψ) →
        ∀ n : ℤ, ∀ a : DeletedCoeff p n,
          (∀ k : ℤ, (displacedRoots (a : Coeff p) k).im = 0) →
            ∀ m : ℤ, K ≤ m.natAbs →
              (sourcePsiEquationCoordinate hp hp1 n m
                (a : Coeff p) ψ ((Real.pi : ℂ)*m) (Real.pi/8)).im = 0 := by
  obtain ⟨Ko,Vo,hVoOpen,hφVo,ho⟩ :=
    exists_local_sourcePsi_realTailOpenGap_coordinates hp hp1 φ hφ
  obtain ⟨Kc,Vc,hVcOpen,hφVc,hc⟩ :=
    exists_local_sourcePsi_realTailCollapsedGap_coordinates hp hp1 φ hφ
  let K : ℕ := max Ko Kc
  let V : Set (CoeffPair p) := Vo ∩ Vc
  have hVopen : IsOpen V := hVoOpen.inter hVcOpen
  have hφV : φ ∈ V := ⟨hφVo,hφVc⟩
  refine ⟨K,V,hVopen,hφV,?_⟩
  intro ψ hψ hreal n a hroots m hm
  have hmO : Ko ≤ m.natAbs := by dsimp [K] at hm; omega
  have hmC : Kc ≤ m.natAbs := by dsimp [K] at hm; omega
  by_cases hopen :
      (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) m).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) m).re
  · exact ho ψ hψ.1 hreal n a hroots m hmO hopen
  · have hle :
        (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
          (periodOnePotential_mem ψ) m).re ≤
        (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
          (periodOnePotential_mem ψ) m).re :=
      re_le_of_complexLexLE
        ((canonicalPeriodicEndpoints_spec hp hp1
          (periodOnePotential ψ) (periodOnePotential_mem ψ)).2.1 m)
    have hre :
        (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
          (periodOnePotential_mem ψ) m).re =
        (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
          (periodOnePotential_mem ψ) m).re :=
      le_antisymm hle (le_of_not_gt hopen)
    have him := canonicalPeriodicEndpoints_im_eq_zero_of_realType
      hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ)
        (isRealType_periodOnePotential ψ hreal) m
    have hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) m = 0 := by
      dsimp [canonicalPeriodicGap]
      apply sub_eq_zero.mpr
      apply Complex.ext
      · exact hre.symm
      · exact him.2.trans him.1.symm
    exact hc ψ hψ.2 hreal n a hroots m hmC hgap

end NLS.ZakharovShabat
