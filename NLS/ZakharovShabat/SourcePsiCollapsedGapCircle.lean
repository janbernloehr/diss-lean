import NLS.ZakharovShabat.SourcePsiFreeLatticeBound
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# The psi contour kernel at a collapsed standard gap

When the standard gap is a point `c`, the selected-root ratio
`(σ-z)/(c-z)` has a single Cauchy pole. Its contour integral against
an analytic regular factor is determined exactly by the displacement
`σ-c`. This is the collapsed-gap case of the integral estimate used
in Section 12.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The selected-root ratio at a collapsed standard gap integrates to
its displacement times the regular factor at the gap center. -/
theorem circleIntegral_collapsedGap_ratio
    (c σ : ℂ) (R : ℝ) (hR : 0 < R) (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) :
    (∮ z in C(c,R), ((σ-z)/(c-z))*f z) =
      (2*(Real.pi:ℂ)*I)*(c-σ)*f c := by
  let K : ℂ → ℂ := fun z => (z-c)⁻¹ * f z
  have hcsphere : ∀ z ∈ sphere c R, z ≠ c := by
    intro z hz he
    have hdist := mem_sphere.mp hz
    rw [he, dist_self] at hdist
    exact (ne_of_gt hR) hdist.symm
  have hKcont : ContinuousOn K (sphere c R) := by
    have hinv : ContinuousOn (fun z : ℂ => (z-c)⁻¹) (sphere c R) := by
      apply ContinuousOn.inv₀
      · exact continuousOn_id.sub continuousOn_const
      · intro z hz
        exact sub_ne_zero.mpr (hcsphere z hz)
    exact hinv.mul (hf.continuousOn.mono sphere_subset_closedBall)
  have hKint : CircleIntegrable K c R := hKcont.circleIntegrable hR.le
  have hfint : CircleIntegrable f c R :=
    (hf.continuousOn.mono sphere_subset_closedBall).circleIntegrable hR.le
  have hCauchy : (∮ z in C(c,R), K z) =
      2*(Real.pi:ℂ)*I*f c := by
    simpa only [K, smul_eq_mul] using
      (hf.differentiableOn.circleIntegral_sub_inv_smul (mem_ball_self hR))
  have hzero : (∮ z in C(c,R), f z) = 0 :=
    (hf.differentiableOn.diffContOnCl_ball subset_rfl).circleIntegral_eq_zero hR.le
  have hsame : (∮ z in C(c,R), ((σ-z)/(c-z))*f z) =
      ∮ z in C(c,R), f z + (c-σ)*K z := by
    apply circleIntegral.integral_congr hR.le
    intro z hz
    have hzc : z-c ≠ 0 := sub_ne_zero.mpr (hcsphere z hz)
    have hcz : c-z ≠ 0 := sub_ne_zero.mpr (Ne.symm (hcsphere z hz))
    dsimp [K]
    field_simp [hzc, hcz]
    ring
  rw [hsame, circleIntegral.integral_add]
  · rw [circleIntegral.integral_const_mul, hzero, hCauchy]
    ring
  · exact hfint
  · have hs := hKint.const_smul (a := c-σ)
    change CircleIntegrable (fun z => (c-σ)*K z) c R at hs
    exact hs

/-- The collapsed-gap contour also obeys a pointwise majorant, with
the displacement of the selected root as its small factor. -/
theorem norm_circleIntegral_collapsedGap_ratio_le
    (c σ : ℂ) (R : ℝ) (hR : 0 < R) (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (M : ℝ) (hM : ‖f c‖ ≤ M) :
    ‖∮ z in C(c,R), ((σ-z)/(c-z))*f z‖ ≤
      2*Real.pi*‖c-σ‖*M := by
  rw [circleIntegral_collapsedGap_ratio c σ R hR f hf]
  simp only [norm_mul, Complex.norm_I, mul_one, norm_ofNat, Complex.norm_real]
  rw [Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  exact mul_le_mul_of_nonneg_left hM (by positivity)

/-- For a deleted root sequence, the free-source psi contour is the
Cauchy residue of its regular factor. The only analytic hypothesis
left is the regularity of that factor on the selected free disc. -/
theorem sourcePsiEquationCoordinate_freeCircle_residue
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n m : ℤ) (a : DeletedCoeff p n)
    (R : ℝ) (hR : 0 < R) (hRπ : R < Real.pi)
    (hreg : AnalyticOnNhd ℂ
      (fun z => (((n-m : ℤ) : ℂ) *
        sourcePsiGapRegularFactor hp hp1 n m (a : Coeff p)
          (0 : CoeffPair p) z))
      (closedBall ((Real.pi : ℂ)*m) R)) :
    sourcePsiEquationCoordinate hp hp1 n m (a : Coeff p)
      (0 : CoeffPair p) ((Real.pi : ℂ)*m) R =
      -(2*(Real.pi:ℂ)*I) * (a : Coeff p) m *
        (((n-m : ℤ) : ℂ) *
          sourcePsiGapRegularFactor hp hp1 n m (a : Coeff p)
            (0 : CoeffPair p) ((Real.pi : ℂ)*m)) := by
  let c : ℂ := (Real.pi : ℂ)*m
  let σ : ℂ := displacedRoots (a : Coeff p) m
  let f : ℂ → ℂ := fun z => (((n-m : ℤ) : ℂ) *
    sourcePsiGapRegularFactor hp hp1 n m (a : Coeff p)
      (0 : CoeffPair p) z)
  have hcircle := freeCircle_subset_sourceCanonicalRootDomain
    hp hp1 m R hR hRπ
  have ha : (a : Coeff p) n = 0 := a.property
  have hn : displacedRoots (a : Coeff p) n = (Real.pi : ℂ)*n := by
    simp [displacedRoots, ha]
  have havoid : ∀ z ∈ sphere c R, z ≠ displacedRoots (a : Coeff p) n := by
    intro z hz
    rw [hn]
    exact freeCircle_point_ne_freeCenter m n R hR hRπ z hz
  rw [sourcePsiEquationCoordinate_eq_gap_factor_circleIntegral
    hp hp1 n m (a : Coeff p) (0 : CoeffPair p) c R hR.le hcircle havoid]
  rw [← circleIntegral.integral_const_mul]
  have heq : (∮ z in C(c,R),
      (((n-m : ℤ) : ℂ) *
        (((displacedRoots (a : Coeff p) m-z) /
          sourceStandardRoot hp hp1 (0 : CoeffPair p) m z) *
          sourcePsiGapRegularFactor hp hp1 n m (a : Coeff p)
            (0 : CoeffPair p) z))) =
      ∮ z in C(c,R), ((σ-z)/(c-z))*f z := by
    apply circleIntegral.integral_congr hR.le
    intro z _
    dsimp only
    rw [sourceStandardRoot_zero_source hp hp1 m z]
    dsimp [c,σ,f]
    ring
  rw [heq, circleIntegral_collapsedGap_ratio c σ R hR f hreg]
  have hcσ : c-σ = -(a : Coeff p) m := by
    dsimp [c,σ,displacedRoots]
    ring
  rw [hcσ]
  dsimp [f]
  ring

/-- On a free disc isolating index `m`, the deleted-coordinate psi
regular factor is analytic whenever the omitted index is different.
This discharges the analytic premise of the collapsed-gap residue. -/
theorem analyticOnNhd_deletedPsi_gapRegularFactor_freeCircle
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n m : ℤ) (hnm : n ≠ m) (a : DeletedCoeff p n)
    (R : ℝ) (hRπ : R < Real.pi) :
    AnalyticOnNhd ℂ
      (fun z => (((n-m : ℤ) : ℂ) *
        sourcePsiGapRegularFactor hp hp1 n m (a : Coeff p)
          (0 : CoeffPair p) z))
      (closedBall ((Real.pi : ℂ)*m) R) := by
  obtain ⟨W,_,_,hreal,hdata⟩ :=
    exists_global_source_analytic_singleRootQuotient hp hp1
  have hzero : (0 : CoeffPair p) ∈ W :=
    hreal (by simp [realTypeSourceLocus])
  intro z hz
  have hdomain : z ∈ sourceStandardRootOmittedDomain hp hp1
      (0 : CoeffPair p) m := by
    intro k hkm
    rw [sourcePeriodicSegment_zero_source hp hp1 k]
    intro he
    exact (freeCenter_not_mem_closedBall_other m k (Ne.symm hkm) R hRπ)
      (he ▸ hz)
  have hQ : AnalyticAt ℂ
      (fun w => sourceSingleRootQuotientJointProduct hp hp1 m
        (w,((a : Coeff p),(0 : CoeffPair p)))) z := by
    have hmap : AnalyticAt ℂ
        (fun w : ℂ => (w,((a : Coeff p),(0 : CoeffPair p)))) z :=
      analyticAt_id.prod (analyticAt_const.prod analyticAt_const)
    exact ((hdata m).2 (z,((a : Coeff p),(0 : CoeffPair p)))
      ⟨hzero,hdomain⟩).comp
        (f := fun w => (w,((a : Coeff p),(0 : CoeffPair p)))) hmap
  have ha : (a : Coeff p) n = 0 := a.property
  have hden : displacedRoots (a : Coeff p) n-z ≠ 0 := by
    rw [show displacedRoots (a : Coeff p) n = (Real.pi : ℂ)*n by
      simp [displacedRoots,ha]]
    apply sub_ne_zero.mpr
    intro he
    exact (freeCenter_not_mem_closedBall_other m n (Ne.symm hnm) R hRπ)
      (he ▸ hz)
  have hD : AnalyticAt ℂ
      (fun w => displacedRoots (a : Coeff p) n-w) z :=
    analyticAt_const.sub analyticAt_id
  change AnalyticAt ℂ (fun w =>
    (((n-m : ℤ) : ℂ) *
      (I * sourceSingleRootQuotientJointProduct hp hp1 m
        (w,((a : Coeff p),(0 : CoeffPair p))) /
        (displacedRoots (a : Coeff p) n-w)))) z
  exact analyticAt_const.mul ((analyticAt_const.mul hQ).div hD hden)

/-- The free-source psi equation at any selected index distinct from
the deleted one is exactly a residue proportional to that root's
ℓᵖ displacement. -/
theorem sourcePsiEquationCoordinate_freeCircle_residue_of_deleted
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n m : ℤ) (hnm : n ≠ m) (a : DeletedCoeff p n)
    (R : ℝ) (hR : 0 < R) (hRπ : R < Real.pi) :
    sourcePsiEquationCoordinate hp hp1 n m (a : Coeff p)
      (0 : CoeffPair p) ((Real.pi : ℂ)*m) R =
      -(2*(Real.pi:ℂ)*I) * (a : Coeff p) m *
        (((n-m : ℤ) : ℂ) *
          sourcePsiGapRegularFactor hp hp1 n m (a : Coeff p)
            (0 : CoeffPair p) ((Real.pi : ℂ)*m)) :=
  sourcePsiEquationCoordinate_freeCircle_residue hp hp1 n m a R hR hRπ
    (analyticOnNhd_deletedPsi_gapRegularFactor_freeCircle
      hp hp1 n m hnm a R hRπ)

/-- A quotient majorant at the free center gives a coordinatewise
psi-contour bound with one factor of the root displacement. -/
theorem norm_sourcePsiEquationCoordinate_freeCircle_le
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n m : ℤ) (hnm : n ≠ m) (a : DeletedCoeff p n)
    (B : Coeff p) (R : ℝ) (hR : 0 < R)
    (hRquarter : R ≤ Real.pi/4)
    (hquot : ‖sourceSingleRootQuotientJointProduct hp hp1 m
      (((Real.pi : ℂ)*m),((a : Coeff p),(0 : CoeffPair p)))-1‖ ≤ ‖B m‖) :
    ‖sourcePsiEquationCoordinate hp hp1 n m (a : Coeff p)
      (0 : CoeffPair p) ((Real.pi : ℂ)*m) R‖ ≤
        4*‖(a : Coeff p) m‖*(1+‖B m‖) := by
  have hRπ : R < Real.pi := by nlinarith [Real.pi_pos]
  have hcenter : (Real.pi : ℂ)*m ∈
      closedBall ((Real.pi : ℂ)*m) R := mem_closedBall_self hR.le
  have hweight := norm_deletedPsi_gapRegularFactor_weighted_le
    hp hp1 n m hnm a (0 : CoeffPair p) B R hRquarter
      ((Real.pi : ℂ)*m) hcenter hquot
  rw [sourcePsiEquationCoordinate_freeCircle_residue_of_deleted
    hp hp1 n m hnm a R hR hRπ]
  have hnorm : ‖-(2*(Real.pi:ℂ)*I) * (a : Coeff p) m *
        (((n-m : ℤ) : ℂ) *
          sourcePsiGapRegularFactor hp hp1 n m (a : Coeff p)
            (0 : CoeffPair p) ((Real.pi : ℂ)*m))‖ =
      (2*Real.pi)*‖(a : Coeff p) m‖*‖(((n-m : ℤ) : ℂ) *
          sourcePsiGapRegularFactor hp hp1 n m (a : Coeff p)
            (0 : CoeffPair p) ((Real.pi : ℂ)*m))‖ := by
    simp only [norm_mul, norm_neg, Complex.norm_I, mul_one,
      norm_ofNat, Complex.norm_real]
    rw [Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [hnorm]
  calc
    (2*Real.pi)*‖(a : Coeff p) m‖*‖(((n-m : ℤ) : ℂ) *
        sourcePsiGapRegularFactor hp hp1 n m (a : Coeff p)
          (0 : CoeffPair p) ((Real.pi : ℂ)*m))‖ ≤
        (2*Real.pi)*‖(a : Coeff p) m‖*
          ((2/Real.pi)*(1+‖B m‖)) :=
      mul_le_mul_of_nonneg_left hweight (by positivity)
    _ = 4*‖(a : Coeff p) m‖*(1+‖B m‖) := by
      field_simp
      ring

/-- A single `ℓᵖ` quotient majorant at all free centers makes the
whole free-source psi equation an `ℓᵖ` sequence. This is the
collapsed-gap mechanism behind Lemma 12.4. -/
theorem memℓp_sourcePsiEquationCoordinate_freeCircle
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n : ℤ) (a : DeletedCoeff p n) (B : Coeff p)
    (R : ℝ) (hR : 0 < R) (hRquarter : R ≤ Real.pi/4)
    (hquot : ∀ m : ℤ, m ≠ n →
      ‖sourceSingleRootQuotientJointProduct hp hp1 m
        (((Real.pi : ℂ)*m),((a : Coeff p),(0 : CoeffPair p)))-1‖ ≤ ‖B m‖) :
    Memℓp (fun m : ℤ =>
      sourcePsiEquationCoordinate hp hp1 n m (a : Coeff p)
        (0 : CoeffPair p) ((Real.pi : ℂ)*m) R) p := by
  have hmajor : Memℓp (fun m : ℤ =>
      (4*(1+‖B‖))*‖(a : Coeff p) m‖) p :=
    (lp.memℓp (a : Coeff p)).norm.const_mul (4*(1+‖B‖))
  apply hmajor.mono
  intro m
  by_cases hmn : m = n
  · subst m
    simp [sourcePsiEquationCoordinate]
    positivity
  · have hcoord : ‖B m‖ ≤ ‖B‖ :=
      lp.norm_apply_le_norm (ne_of_gt (zero_lt_one.trans_le Fact.out)) B m
    calc
      ‖sourcePsiEquationCoordinate hp hp1 n m (a : Coeff p)
        (0 : CoeffPair p) ((Real.pi : ℂ)*m) R‖ ≤
          4*‖(a : Coeff p) m‖*(1+‖B m‖) :=
        norm_sourcePsiEquationCoordinate_freeCircle_le hp hp1 n m
          (Ne.symm hmn) a B R hR hRquarter (hquot m hmn)
      _ ≤ 4*‖(a : Coeff p) m‖*(1+‖B‖) := by gcongr
      _ = (4*(1+‖B‖))*‖(a : Coeff p) m‖ := by ring

/-- Under the same quotient majorant, the free-source psi equation
actually takes values in the deleted-coordinate Banach space. -/
theorem exists_deletedCoeff_sourcePsiEquation_freeCircle
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n : ℤ) (a : DeletedCoeff p n) (B : Coeff p)
    (R : ℝ) (hR : 0 < R) (hRquarter : R ≤ Real.pi/4)
    (hquot : ∀ m : ℤ, m ≠ n →
      ‖sourceSingleRootQuotientJointProduct hp hp1 m
        (((Real.pi : ℂ)*m),((a : Coeff p),(0 : CoeffPair p)))-1‖ ≤ ‖B m‖) :
    ∃ F : DeletedCoeff p n, ∀ m : ℤ,
      (F : Coeff p) m =
        sourcePsiEquationCoordinate hp hp1 n m (a : Coeff p)
          (0 : CoeffPair p) ((Real.pi : ℂ)*m) R := by
  let F : Coeff p := ⟨fun m =>
    sourcePsiEquationCoordinate hp hp1 n m (a : Coeff p)
      (0 : CoeffPair p) ((Real.pi : ℂ)*m) R,
    memℓp_sourcePsiEquationCoordinate_freeCircle hp hp1 n a B R
      hR hRquarter hquot⟩
  have hFn : F n = 0 := by
    simp [F,sourcePsiEquationCoordinate]
  refine ⟨⟨F, ?_⟩, ?_⟩
  · change F n = 0
    exact hFn
  · intro m
    rfl

end NLS.ZakharovShabat
