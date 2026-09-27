import NLS.ZakharovShabat.SourcePsiNearFreeRegularAnalytic
import NLS.ZakharovShabat.SourceStandardRootWeightedLocalContourHomotopy

/-!
# Applying the selected-gap estimate to the psi contour equation

The factorization (2.27) presents a psi-equation coordinate as a
selected-root integral. Lemma 12.3 then bounds that coordinate by
the numerator on the selected real gap, under explicit local contour
geometry and analyticity hypotheses.
-/

noncomputable section
open Set Metric Complex
open NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The normalized psi-equation coordinate is bounded by its
factorized numerator on the selected real gap. This is the exact
interface between (2.27) and the local form of Lemma 12.3. -/
theorem norm_sourcePsiEquationCoordinate_le_gapNumerator_of_local_circle
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n m : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) m).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) m).re)
    (a : Coeff p) (U : Set ℂ) (hUopen : IsOpen U)
    (hgapU : standardRootGapSegment
      (sourceStandardRootMidpoint hp hp1 ψ m)
      (sourceStandardRootHalfGap hp hp1 ψ m) ⊆ U)
    (hg : AnalyticOnNhd ℂ
      (fun z => (displacedRoots a m-z) *
        (((n-m : ℤ) : ℂ) *
          sourcePsiGapRegularFactor hp hp1 n m a ψ z)) U)
    (c₀ : ℂ) (r₀ R : ℝ) (hr₀ : 0 < r₀)
    (hseg₀ : sourcePeriodicSegment hp hp1 ψ m ⊆ ball c₀ r₀)
    (hcircle : sphere c₀ r₀ ⊆ sourceCanonicalRootDomain hp hp1 ψ)
    (havoid : ∀ z ∈ sphere c₀ r₀, z ≠ displacedRoots a n) :
    let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) m
    let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) m
    let c : ℂ := (((l.re+r.re)/2 : ℝ) : ℂ)
    let d : ℝ := (r.re-l.re)/2
    d < R → closedBall c R ⊆ U →
      closedBall c₀ r₀ ⊆ closedBall c R →
      ∀ M : ℝ,
        (∀ z ∈ standardRootGapSegment
          (sourceStandardRootMidpoint hp hp1 ψ m)
          (sourceStandardRootHalfGap hp hp1 ψ m),
          ‖(displacedRoots a m-z) *
            (((n-m : ℤ) : ℂ) *
              sourcePsiGapRegularFactor hp hp1 n m a ψ z)‖ ≤ M) →
      ‖(2 * (Real.pi : ℂ))⁻¹ *
        sourcePsiEquationCoordinate hp hp1 n m a ψ c₀ r₀‖ ≤ M := by
  let g : ℂ → ℂ := fun z => (displacedRoots a m-z) *
    (((n-m : ℤ) : ℂ) * sourcePsiGapRegularFactor hp hp1 n m a ψ z)
  dsimp only
  intro hR hUdisc hnest M hM
  have heq : sourcePsiEquationCoordinate hp hp1 n m a ψ c₀ r₀ =
      ∮ z in C(c₀,r₀), g z / sourceStandardRoot hp hp1 ψ m z := by
    rw [sourcePsiEquationCoordinate_eq_gap_factor_circleIntegral
      hp hp1 n m a ψ c₀ r₀ hr₀.le hcircle havoid]
    rw [← circleIntegral.integral_const_mul]
    apply circleIntegral.integral_congr hr₀.le
    intro z _
    dsimp [g]
    ring
  obtain ⟨z,hz,_,hbound⟩ :=
    weighted_sourceStandardRoot_circle_max_bound_of_local_nested_midpoint
      hp hp1 ψ hreal m hopen g U hUopen hgapU hg
        c₀ r₀ R hr₀ hseg₀ hR hUdisc hnest
  rw [heq]
  exact hbound.trans (hM z hz)

/-- A small real gap admits a fixed free-centered eighth-π circle
nested inside a three-sixteenths-π midpoint disc; the latter stays
inside the free quarter-π disc where the omitted quotient is analytic. -/
theorem nearFree_realGap_nested_circle_geometry
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (m : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) m).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) m).re)
    (hmid : ‖sourceStandardRootMidpoint hp hp1 ψ m -
      (Real.pi : ℂ)*m‖ ≤ Real.pi/64)
    (hgap : ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖ ≤ Real.pi/32) :
    let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) m
    let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) m
    let c : ℂ := (((l.re+r.re)/2 : ℝ) : ℂ)
    let d : ℝ := (r.re-l.re)/2
    d < 3*Real.pi/16 ∧
      closedBall c (3*Real.pi/16) ⊆
        ball ((Real.pi : ℂ)*m) (Real.pi/4) ∧
      closedBall ((Real.pi : ℂ)*m) (Real.pi/8) ⊆
        closedBall c (3*Real.pi/16) := by
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) m
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) m
  let c : ℂ := (((l.re+r.re)/2 : ℝ) : ℂ)
  let d : ℝ := (r.re-l.re)/2
  dsimp only
  have him := canonicalPeriodicEndpoints_im_eq_zero_of_realType
    hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ)
      (isRealType_periodOnePotential ψ hreal) m
  have hl : l.im = 0 := him.1
  have hr : r.im = 0 := him.2
  have hc : c = sourceStandardRootMidpoint hp hp1 ψ m := by
    change c = (l+r)/2
    apply Complex.ext
    · simp [c,Complex.add_re]
    · simp [c,hl,hr]
  have hdpos : 0 < d := by
    change 0 < (r.re-l.re)/2
    exact div_pos (sub_pos.mpr hopen) (by norm_num)
  have hδ : sourceStandardRootHalfGap hp hp1 ψ m = (d:ℂ) :=
    sourceStandardRootHalfGap_eq_ofReal_affineJacobian
      hp hp1 ψ hreal m
  have hdnorm : d = ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖/2 := by
    calc
      d = ‖sourceStandardRootHalfGap hp hp1 ψ m‖ := by
        rw [hδ,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hdpos]
      _ = ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖/2 := by
        simp only [sourceStandardRootHalfGap,
          sourcePeriodicGapDisplacement_apply]
        rw [norm_div]
        norm_num
  have hdsmall : d ≤ Real.pi/64 := by
    rw [hdnorm]
    nlinarith [hgap]
  have hcenter : dist c ((Real.pi:ℂ)*m) ≤ Real.pi/64 := by
    rw [dist_eq_norm,hc]
    exact hmid
  have hcenter' : dist ((Real.pi:ℂ)*m) c ≤ Real.pi/64 := by
    rw [dist_comm]
    exact hcenter
  constructor
  · change d < 3*Real.pi/16
    nlinarith [Real.pi_pos]
  constructor
  · exact Metric.closedBall_subset_ball'
      (by nlinarith [hcenter,Real.pi_pos])
  · exact Metric.closedBall_subset_closedBall'
      (by nlinarith [hcenter',Real.pi_pos])

/-- On one near-free neighborhood, every open real gap has the
Lemma 12.4 coordinate bound on the fixed free eighth-π contour. The
right side is an `ℓᵖ` displacement scale times the quotient majorant,
uniformly in the deleted index. -/
theorem exists_nearFree_deletedPsi_openGap_coordinate_bound
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ (0 : CoeffPair p) ∈ V ∧
      ∀ ψ ∈ V, IsRealType (CoeffPair.toMax p ψ) →
        ∀ n : ℤ, ∀ a : DeletedCoeff p n,
          ∃ B : Coeff p, ∀ m : ℤ, m ≠ n →
            (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
              (periodOnePotential_mem ψ) m).re <
              (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
                (periodOnePotential_mem ψ) m).re →
            ‖(2 * (Real.pi : ℂ))⁻¹ *
              sourcePsiEquationCoordinate hp hp1 n m (a : Coeff p) ψ
                ((Real.pi : ℂ)*m) (Real.pi/8)‖ ≤
              (‖(a : Coeff p) m‖ +
                ‖sourcePeriodicMidpointDisplacement hp hp1 ψ m‖ +
                ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖/2) *
                  ((2/Real.pi)*(1+‖B m‖)) := by
  obtain ⟨Vnum,hVnumOpen,hzeroNum,hnum⟩ :=
    exists_nearFree_deletedPsi_gapNumerator_analytic_bound hp hp1
  obtain ⟨Vsmall,hVsmallOpen,hzeroSmall,hsmall⟩ :=
    exists_nearFree_allPeriodicMidpointGap_small hp hp1
  obtain ⟨Vgeom,hVgeomOpen,hzeroGeom,hgeom⟩ :=
    exists_nearFree_freeQuarterDisc_subset_omittedDomain hp hp1
  obtain ⟨Vcircle,hVcircleOpen,hzeroCircle,hcircle⟩ :=
    exists_nearFree_freeEighthCircle_subset_rootDomain hp hp1
  obtain ⟨Vseg,hVsegOpen,hzeroSeg,hseg⟩ :=
    exists_nearFree_allPeriodicSegments_in_eighth_ball hp hp1
  obtain ⟨W,hWopen,_,hrealW,hdata⟩ :=
    exists_global_source_analytic_singleRootQuotient hp hp1
  have hzeroW : (0 : CoeffPair p) ∈ W :=
    hrealW (by simp [realTypeSourceLocus])
  let V := Vnum ∩ Vsmall ∩ Vgeom ∩ Vcircle ∩ Vseg ∩ W
  refine ⟨V,((((hVnumOpen.inter hVsmallOpen).inter hVgeomOpen).inter
    hVcircleOpen).inter hVsegOpen).inter hWopen,
    ⟨⟨⟨⟨⟨hzeroNum,hzeroSmall⟩,hzeroGeom⟩,hzeroCircle⟩,hzeroSeg⟩,hzeroW⟩,?_⟩
  intro ψ hψ hreal n a
  obtain ⟨B,hB⟩ := hnum ψ hψ.1.1.1.1.1 n a
  refine ⟨B,?_⟩
  intro m hmn hopen
  let cf : ℂ := (Real.pi : ℂ)*m
  let U : Set ℂ := ball cf (Real.pi/4)
  let g : ℂ → ℂ := fun z =>
    (displacedRoots (a : Coeff p) m-z) *
      (((n-m : ℤ) : ℂ) *
        sourcePsiGapRegularFactor hp hp1 n m (a : Coeff p) ψ z)
  obtain ⟨hnumAnalytic,hnumBound⟩ := hB m hmn
  obtain ⟨hR,hUdisc,hnest⟩ := nearFree_realGap_nested_circle_geometry
    hp hp1 ψ hreal m hopen
      (hsmall ψ hψ.1.1.1.1.2 m).1
      (hsmall ψ hψ.1.1.1.1.2 m).2
  have hseg₀ : sourcePeriodicSegment hp hp1 ψ m ⊆
      ball cf (Real.pi/8) := hseg ψ hψ.1.2 m
  have hgapU : standardRootGapSegment
      (sourceStandardRootMidpoint hp hp1 ψ m)
      (sourceStandardRootHalfGap hp hp1 ψ m) ⊆ U := by
    exact (sourceStandardRoot_gapSegment_subset_periodicSegment hp hp1 ψ m).trans
      (hseg₀.trans (ball_subset_ball (by nlinarith [Real.pi_pos])))
  have hreg : AnalyticOnNhd ℂ
      (fun z => (((n-m : ℤ) : ℂ) *
        sourcePsiGapRegularFactor hp hp1 n m (a : Coeff p) ψ z))
      (closedBall cf (Real.pi/4)) := by
    apply analyticOnNhd_deletedPsi_gapRegularFactor_of_omitted_disc
      hp hp1 n m (Ne.symm hmn) a ψ W hψ.2 (hdata m).2
        (Real.pi/4) (by nlinarith [Real.pi_pos])
    exact hgeom ψ hψ.1.1.1.2 m
  have hg : AnalyticOnNhd ℂ g U := by
    intro z hz
    have hz' : z ∈ closedBall cf (Real.pi/4) := ball_subset_closedBall hz
    exact (analyticAt_const.sub analyticAt_id).mul (hreg z hz')
  have hrootCircle : sphere cf (Real.pi/8) ⊆
      sourceCanonicalRootDomain hp hp1 ψ :=
    hcircle ψ hψ.1.1.2 m
  have havoid : ∀ z ∈ sphere cf (Real.pi/8),
      z ≠ displacedRoots (a : Coeff p) n := by
    intro z hz
    have ha : (a : Coeff p) n = 0 := a.property
    rw [show displacedRoots (a : Coeff p) n =
      (Real.pi : ℂ)*n by simp [displacedRoots,ha]]
    exact freeCircle_point_ne_freeCenter m n (Real.pi/8)
      (by positivity) (by nlinarith [Real.pi_pos]) z hz
  exact norm_sourcePsiEquationCoordinate_le_gapNumerator_of_local_circle
    hp hp1 ψ hreal n m hopen (a : Coeff p) U isOpen_ball hgapU hg
      cf (Real.pi/8) (3*Real.pi/16) (by positivity) hseg₀
      hrootCircle havoid hR hUdisc hnest _ hnumBound

/-- For a real-type source near zero, the open-gap coordinates of the
psi contour equation form an `ℓᵖ` sequence on the fixed free circles.
Collapsed-gap coordinates are left for the residue argument. -/
theorem exists_nearFree_deletedPsi_openGap_coordinates_memℓp
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ (0 : CoeffPair p) ∈ V ∧
      ∀ ψ ∈ V, IsRealType (CoeffPair.toMax p ψ) →
        ∀ n : ℤ, ∀ a : DeletedCoeff p n,
          Memℓp (fun m : ℤ =>
            if (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
                (periodOnePotential_mem ψ) m).re <
                (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
                  (periodOnePotential_mem ψ) m).re then
              sourcePsiEquationCoordinate hp hp1 n m (a : Coeff p) ψ
                ((Real.pi : ℂ)*m) (Real.pi/8)
            else 0) p := by
  obtain ⟨V,hVopen,hzero,hbound⟩ :=
    exists_nearFree_deletedPsi_openGap_coordinate_bound hp hp1
  refine ⟨V,hVopen,hzero,?_⟩
  intro ψ hψ hreal n a
  obtain ⟨B,hB⟩ := hbound ψ hψ hreal n a
  let M := sourcePeriodicMidpointDisplacement hp hp1 ψ
  let G := sourcePeriodicGapDisplacement hp hp1 ψ
  let A : Coeff p := Coeff.magnitude (a : Coeff p) +
    Coeff.magnitude M + Coeff.magnitude G
  have hA (m : ℤ) : ‖A m‖ =
      ‖(a : Coeff p) m‖ + ‖M m‖ + ‖G m‖ := by
    simp only [A,lp.coeFn_add,Pi.add_apply,Coeff.magnitude_apply,
      ← Complex.ofReal_add,Complex.norm_real]
    exact Real.norm_of_nonneg (by positivity)
  let C : ℝ := (2*Real.pi)*((2/Real.pi)*(1+‖B‖))
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hπ : (2*(Real.pi:ℂ)) ≠ 0 := by simp [Real.pi_ne_zero]
  have hnormalize (X : ℂ) : ‖X‖ =
      (2*Real.pi)*‖(2*(Real.pi:ℂ))⁻¹ * X‖ := by
    have heq : (2*(Real.pi:ℂ)) *
        ((2*(Real.pi:ℂ))⁻¹ * X) = X := by
      rw [← mul_assoc, mul_inv_cancel₀ hπ, one_mul]
    calc
      ‖X‖ = ‖(2*(Real.pi:ℂ)) *
          ((2*(Real.pi:ℂ))⁻¹ * X)‖ := congrArg norm heq.symm
      _ = (2*Real.pi)*‖(2*(Real.pi:ℂ))⁻¹ * X‖ := by
        rw [norm_mul]
        simp [Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos Real.pi_pos]
  have hmajor : Memℓp (fun m : ℤ => C*‖A m‖) p :=
    (lp.memℓp A).norm.const_mul C
  apply hmajor.mono
  intro m
  by_cases hmn : m = n
  · subst m
    simp [sourcePsiEquationCoordinate]
    exact mul_nonneg hC (norm_nonneg _)
  by_cases hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) m).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) m).re
  · simp only [if_pos hopen]
    let F : ℂ := sourcePsiEquationCoordinate hp hp1 n m (a : Coeff p) ψ
      ((Real.pi : ℂ)*m) (Real.pi/8)
    have hF := hB m hmn hopen
    have hscale : ‖(a : Coeff p) m‖ + ‖M m‖ + ‖G m‖/2 ≤ ‖A m‖ := by
      rw [hA]
      have hG : 0 ≤ ‖G m‖ := norm_nonneg _
      linarith
    have hBcoord : ‖B m‖ ≤ ‖B‖ :=
      lp.norm_apply_le_norm (ne_of_gt (zero_lt_one.trans_le Fact.out)) B m
    have hfactor : (2/Real.pi)*(1+‖B m‖) ≤
        (2/Real.pi)*(1+‖B‖) := by
      exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    change ‖F‖ ≤ C*‖A m‖
    rw [hnormalize]
    calc
      (2*Real.pi)*‖(2*(Real.pi:ℂ))⁻¹ * F‖ ≤
          (2*Real.pi)*((‖(a : Coeff p) m‖+‖M m‖+‖G m‖/2) *
            ((2/Real.pi)*(1+‖B m‖))) :=
        mul_le_mul_of_nonneg_left hF (by positivity)
      _ ≤ (2*Real.pi)*(‖A m‖*((2/Real.pi)*(1+‖B m‖))) := by
        gcongr
      _ ≤ (2*Real.pi)*(‖A m‖*((2/Real.pi)*(1+‖B‖))) := by
        gcongr
      _ = C*‖A m‖ := by dsimp [C]; ring
  · simp only [if_neg hopen, norm_zero]
    exact mul_nonneg hC (norm_nonneg _)

end NLS.ZakharovShabat
