import NLS.ZakharovShabat.SourcePsiSelectedGapContourBound
import NLS.ZakharovShabat.SourcePsiCollapsedGapCircle

/-!
# Psi contour coordinates at collapsed near-free gaps

A collapsed selected standard root is linear, so its contour is a
Cauchy residue at the moving midpoint. The fixed free-centered
eighth-π circle need not be centered at that pole.
-/

noncomputable section
open Set Metric Complex
open NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The collapsed-gap ratio has the same residue on any circle whose
filled disc contains the pole, even when the pole is off center. -/
theorem circleIntegral_collapsedGap_ratio_of_mem_ball
    (c₀ c σ : ℂ) (R : ℝ) (hR : 0 < R)
    (hc : c ∈ ball c₀ R) (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (closedBall c₀ R)) :
    (∮ z in C(c₀,R), ((σ-z)/(c-z))*f z) =
      (2*(Real.pi:ℂ)*I)*(c-σ)*f c := by
  let K : ℂ → ℂ := fun z => (z-c)⁻¹ * f z
  have hcsphere : ∀ z ∈ sphere c₀ R, z ≠ c := by
    intro z hz he
    have hs := mem_sphere.mp hz
    rw [he] at hs
    exact (ne_of_lt (mem_ball.mp hc)) hs
  have hKcont : ContinuousOn K (sphere c₀ R) := by
    have hinv : ContinuousOn (fun z : ℂ => (z-c)⁻¹) (sphere c₀ R) := by
      apply ContinuousOn.inv₀
      · exact continuousOn_id.sub continuousOn_const
      · intro z hz
        exact sub_ne_zero.mpr (hcsphere z hz)
    exact hinv.mul (hf.continuousOn.mono sphere_subset_closedBall)
  have hKint : CircleIntegrable K c₀ R := hKcont.circleIntegrable hR.le
  have hfint : CircleIntegrable f c₀ R :=
    (hf.continuousOn.mono sphere_subset_closedBall).circleIntegrable hR.le
  have hCauchy : (∮ z in C(c₀,R), K z) =
      2*(Real.pi:ℂ)*I*f c := by
    simpa only [K, smul_eq_mul] using
      (hf.differentiableOn.circleIntegral_sub_inv_smul hc)
  have hzero : (∮ z in C(c₀,R), f z) = 0 :=
    (hf.differentiableOn.diffContOnCl_ball subset_rfl).circleIntegral_eq_zero hR.le
  have hsame : (∮ z in C(c₀,R), ((σ-z)/(c-z))*f z) =
      ∮ z in C(c₀,R), f z + (c-σ)*K z := by
    apply circleIntegral.integral_congr hR.le
    intro z hz
    have hzc : z-c ≠ 0 := sub_ne_zero.mpr (hcsphere z hz)
    have hcz : c-z ≠ 0 := sub_ne_zero.mpr (Ne.symm (hcsphere z hz))
    dsimp [K]
    field_simp [hzc,hcz]
    ring
  rw [hsame,circleIntegral.integral_add]
  · rw [circleIntegral.integral_const_mul,hzero,hCauchy]
    ring
  · exact hfint
  · have hs := hKint.const_smul (a := c-σ)
    change CircleIntegrable (fun z => (c-σ)*K z) c₀ R at hs
    exact hs

/-- At a collapsed selected gap, the psi equation on any enclosing
circle is the Cauchy residue of its analytic regular factor at the
moving midpoint. -/
theorem sourcePsiEquationCoordinate_collapsedGap_residue
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n m : ℤ) (a : DeletedCoeff p n) (ψ : CoeffPair p)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) m = 0)
    (c₀ : ℂ) (R : ℝ) (hR : 0 < R)
    (hmid : sourceStandardRootMidpoint hp hp1 ψ m ∈ ball c₀ R)
    (hcircle : sphere c₀ R ⊆ sourceCanonicalRootDomain hp hp1 ψ)
    (havoid : ∀ z ∈ sphere c₀ R,
      z ≠ displacedRoots (a : Coeff p) n)
    (hreg : AnalyticOnNhd ℂ
      (fun z => (((n-m : ℤ) : ℂ) *
        sourcePsiGapRegularFactor hp hp1 n m (a : Coeff p) ψ z))
      (closedBall c₀ R)) :
    sourcePsiEquationCoordinate hp hp1 n m (a : Coeff p) ψ c₀ R =
      (2*(Real.pi:ℂ)*I) *
        (sourceStandardRootMidpoint hp hp1 ψ m -
          displacedRoots (a : Coeff p) m) *
        (((n-m : ℤ) : ℂ) *
          sourcePsiGapRegularFactor hp hp1 n m (a : Coeff p) ψ
            (sourceStandardRootMidpoint hp hp1 ψ m)) := by
  let τ := sourceStandardRootMidpoint hp hp1 ψ m
  let σ := displacedRoots (a : Coeff p) m
  let f : ℂ → ℂ := fun z => (((n-m : ℤ) : ℂ) *
    sourcePsiGapRegularFactor hp hp1 n m (a : Coeff p) ψ z)
  rw [sourcePsiEquationCoordinate_eq_gap_factor_circleIntegral
    hp hp1 n m (a : Coeff p) ψ c₀ R hR.le hcircle havoid]
  rw [← circleIntegral.integral_const_mul]
  have heq : (∮ z in C(c₀,R),
      (((n-m : ℤ) : ℂ) *
        (((displacedRoots (a : Coeff p) m-z) /
          sourceStandardRoot hp hp1 ψ m z) *
          sourcePsiGapRegularFactor hp hp1 n m (a : Coeff p) ψ z))) =
      ∮ z in C(c₀,R), ((σ-z)/(τ-z))*f z := by
    apply circleIntegral.integral_congr hR.le
    intro z _
    dsimp only
    rw [sourceStandardRoot_of_zeroGap hp hp1 ψ m z hgap]
    change (((n-m : ℤ) : ℂ) *
        (((σ-z)/(τ-z)) *
          sourcePsiGapRegularFactor hp hp1 n m (a : Coeff p) ψ z)) =
      ((σ-z)/(τ-z)) *
        ((((n-m : ℤ) : ℂ) *
          sourcePsiGapRegularFactor hp hp1 n m (a : Coeff p) ψ z))
    ring
  rw [heq,circleIntegral_collapsedGap_ratio_of_mem_ball
    c₀ τ σ R hR hmid f hreg]

/-- On one near-free source neighborhood, every collapsed selected
gap satisfies the same `ℓᵖ`-scale coordinate estimate as an open gap.
The bound is uniform in the deleted index. -/
theorem exists_nearFree_deletedPsi_collapsedGap_coordinate_bound
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ (0 : CoeffPair p) ∈ V ∧
      ∀ ψ ∈ V, ∀ n : ℤ, ∀ a : DeletedCoeff p n,
        ∃ B : Coeff p, ∀ m : ℤ, m ≠ n →
          (canonicalPeriodicGap hp hp1 (periodOnePotential ψ)
            (periodOnePotential_mem ψ) m = 0) →
            ‖(2 * (Real.pi : ℂ))⁻¹ *
              sourcePsiEquationCoordinate hp hp1 n m (a : Coeff p) ψ
                ((Real.pi : ℂ)*m) (Real.pi/8)‖ ≤
              (‖(a : Coeff p) m‖ +
                ‖sourcePeriodicMidpointDisplacement hp hp1 ψ m‖) *
                  ((2/Real.pi)*(1+‖B m‖)) := by
  obtain ⟨Vreg,hVregOpen,hzeroReg,hreg⟩ :=
    exists_nearFree_deletedPsi_gapRegularFactor_analytic_majorant hp hp1
  obtain ⟨Vsmall,hVsmallOpen,hzeroSmall,hsmall⟩ :=
    exists_nearFree_allPeriodicMidpointGap_small hp hp1
  obtain ⟨Vcircle,hVcircleOpen,hzeroCircle,hcircle⟩ :=
    exists_nearFree_freeEighthCircle_subset_rootDomain hp hp1
  let V := Vreg ∩ Vsmall ∩ Vcircle
  refine ⟨V,(hVregOpen.inter hVsmallOpen).inter hVcircleOpen,
    ⟨⟨hzeroReg,hzeroSmall⟩,hzeroCircle⟩,?_⟩
  intro ψ hψ n a
  obtain ⟨B,hB⟩ := hreg ψ hψ.1.1 n a
  refine ⟨B,?_⟩
  intro m hmn hgap
  let cf : ℂ := (Real.pi : ℂ)*m
  let τ := sourceStandardRootMidpoint hp hp1 ψ m
  let σ := displacedRoots (a : Coeff p) m
  let f : ℂ → ℂ := fun z => (((n-m : ℤ) : ℂ) *
    sourcePsiGapRegularFactor hp hp1 n m (a : Coeff p) ψ z)
  obtain ⟨hregAnalytic,hregBound⟩ := hB m hmn
  have hτball : τ ∈ ball cf (Real.pi/8) := by
    rw [mem_ball,dist_eq_norm]
    exact (hsmall ψ hψ.1.2 m).1.trans_lt
      (by nlinarith [Real.pi_pos])
  have hrootCircle : sphere cf (Real.pi/8) ⊆
      sourceCanonicalRootDomain hp hp1 ψ :=
    hcircle ψ hψ.2 m
  have havoid : ∀ z ∈ sphere cf (Real.pi/8),
      z ≠ displacedRoots (a : Coeff p) n := by
    intro z hz
    have ha : (a : Coeff p) n = 0 := a.property
    rw [show displacedRoots (a : Coeff p) n =
      (Real.pi : ℂ)*n by simp [displacedRoots,ha]]
    exact freeCircle_point_ne_freeCenter m n (Real.pi/8)
      (by positivity) (by nlinarith [Real.pi_pos]) z hz
  have hres := sourcePsiEquationCoordinate_collapsedGap_residue
    hp hp1 n m a ψ hgap cf (Real.pi/8) (by positivity)
      hτball hrootCircle havoid hregAnalytic
  have hπ : (2 * (Real.pi : ℂ)) ≠ 0 := by simp [Real.pi_ne_zero]
  have hnorm : ‖(2 * (Real.pi : ℂ))⁻¹ *
      sourcePsiEquationCoordinate hp hp1 n m (a : Coeff p) ψ cf
        (Real.pi/8)‖ = ‖τ-σ‖ * ‖f τ‖ := by
    rw [hres]
    have heq : (2 * (Real.pi : ℂ))⁻¹ *
        ((2 * (Real.pi : ℂ) * I) * (τ-σ) * f τ) =
        I * (τ-σ) * f τ := by
      field_simp [hπ]
    rw [heq]
    simp
  have hroot : ‖τ-σ‖ ≤ ‖(a : Coeff p) m‖ +
      ‖sourcePeriodicMidpointDisplacement hp hp1 ψ m‖ := by
    have hoff := sourcePsi_midpoint_offset_apply
      hp hp1 (a : Coeff p) ψ m
    change σ-τ =
      ((a : Coeff p)-sourcePeriodicMidpointDisplacement hp hp1 ψ) m at hoff
    rw [show τ-σ = -(σ-τ) by ring, norm_neg, hoff]
    simpa only [lp.coeFn_sub,Pi.sub_apply] using
      norm_sub_le ((a : Coeff p) m)
        (sourcePeriodicMidpointDisplacement hp hp1 ψ m)
  have hfactor := hregBound τ (ball_subset_closedBall hτball)
  rw [hnorm]
  calc
    ‖τ-σ‖ * ‖f τ‖ ≤
      (‖(a : Coeff p) m‖ +
        ‖sourcePeriodicMidpointDisplacement hp hp1 ψ m‖) * ‖f τ‖ :=
      mul_le_mul_of_nonneg_right hroot (norm_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_left hfactor (by positivity)

/-- For a real-type source, failure of a strict endpoint gap means
the canonical gap is collapsed as a complex number. -/
theorem sourcePeriodicGap_eq_zero_of_real_not_open
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (m : ℤ)
    (hnot : ¬(canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) m).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) m).re) :
    canonicalPeriodicGap hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) m = 0 := by
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) m
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) m
  have hle : l.re ≤ r.re :=
    re_le_of_complexLexLE
      ((canonicalPeriodicEndpoints_spec hp hp1
        (periodOnePotential ψ) (periodOnePotential_mem ψ)).2.1 m)
  have hre : l.re = r.re := le_antisymm hle (le_of_not_gt hnot)
  have him := canonicalPeriodicEndpoints_im_eq_zero_of_realType
    hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ)
      (isRealType_periodOnePotential ψ hreal) m
  have heq : l = r := Complex.ext hre (him.1.trans him.2.symm)
  change r-l = 0
  rw [heq]
  ring

/-- A uniform normalized coordinate bound by one `ℓᵖ` scale and one
`ℓᵖ` regular-factor majorant yields an `ℓᵖ` contour sequence. -/
private theorem memℓp_of_normalized_gap_coordinate_bound
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (A B : Coeff p) (F : ℤ → ℂ)
    (hF : ∀ m : ℤ,
      ‖(2 * (Real.pi : ℂ))⁻¹ * F m‖ ≤
        ‖A m‖ * ((2/Real.pi)*(1+‖B m‖))) :
    Memℓp F p := by
  let K : ℂ := 2 * (Real.pi : ℂ)
  have hK : K ≠ 0 := by dsimp [K]; simp [Real.pi_ne_zero]
  let C : ℝ := (2/Real.pi)*(1+‖B‖)
  have hmajor : Memℓp (fun m : ℤ => C*‖A m‖) p :=
    (lp.memℓp A).norm.const_mul C
  have hnorm : Memℓp (fun m : ℤ => K⁻¹ * F m) p := by
    apply hmajor.mono
    intro m
    have hcoord : ‖B m‖ ≤ ‖B‖ :=
      lp.norm_apply_le_norm (ne_of_gt (zero_lt_one.trans_le Fact.out)) B m
    calc
      ‖K⁻¹ * F m‖ ≤ ‖A m‖ * ((2/Real.pi)*(1+‖B m‖)) := hF m
      _ ≤ ‖A m‖ * C := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        dsimp [C]
        exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = C*‖A m‖ := by ring
  have hraw := hnorm.const_mul K
  have heq : (fun m : ℤ => K * (K⁻¹ * F m)) = F := by
    funext m
    rw [← mul_assoc, mul_inv_cancel₀ hK, one_mul]
  simpa only [heq] using hraw

/-- On the same fixed free circles, the collapsed-gap coordinates of
the real-type psi equation form an `ℓᵖ` sequence near zero. -/
theorem exists_nearFree_deletedPsi_collapsedGap_coordinates_memℓp
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
              0
            else sourcePsiEquationCoordinate hp hp1 n m (a : Coeff p) ψ
              ((Real.pi : ℂ)*m) (Real.pi/8)) p := by
  obtain ⟨V,hVopen,hzero,hbound⟩ :=
    exists_nearFree_deletedPsi_collapsedGap_coordinate_bound hp hp1
  refine ⟨V,hVopen,hzero,?_⟩
  intro ψ hψ hreal n a
  obtain ⟨B,hB⟩ := hbound ψ hψ n a
  let M := sourcePeriodicMidpointDisplacement hp hp1 ψ
  let A : Coeff p := Coeff.magnitude (a : Coeff p) + Coeff.magnitude M
  have hA (m : ℤ) : ‖A m‖ = ‖(a : Coeff p) m‖ + ‖M m‖ := by
    simp only [A,lp.coeFn_add,Pi.add_apply,Coeff.magnitude_apply,
      ← Complex.ofReal_add,Complex.norm_real]
    exact Real.norm_of_nonneg (by positivity)
  apply memℓp_of_normalized_gap_coordinate_bound A B
  intro m
  by_cases hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) m).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) m).re
  · simp only [if_pos hopen,mul_zero,norm_zero]
    positivity
  have hgap := sourcePeriodicGap_eq_zero_of_real_not_open
    hp hp1 ψ hreal m hopen
  by_cases hmn : m = n
  · subst m
    simp [sourcePsiEquationCoordinate]
    positivity
  · simp only [if_neg hopen]
    have hvalue := hB m hmn hgap
    rw [hA]
    exact hvalue

/-- Near the free source, the complete fixed-circle psi equation for
every real-type potential and deleted root input is an `ℓᵖ`
sequence. Both open and collapsed gaps are included. -/
theorem exists_nearFree_real_deletedPsi_equation_memℓp
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ (0 : CoeffPair p) ∈ V ∧
      ∀ ψ ∈ V, IsRealType (CoeffPair.toMax p ψ) →
        ∀ n : ℤ, ∀ a : DeletedCoeff p n,
          Memℓp (fun m : ℤ =>
            sourcePsiEquationCoordinate hp hp1 n m (a : Coeff p) ψ
              ((Real.pi : ℂ)*m) (Real.pi/8)) p := by
  obtain ⟨Vopen,hVopen,hzeroOpen,hopen⟩ :=
    exists_nearFree_deletedPsi_openGap_coordinates_memℓp hp hp1
  obtain ⟨Vcollapsed,hVcollapsed,hzeroCollapsed,hcollapsed⟩ :=
    exists_nearFree_deletedPsi_collapsedGap_coordinates_memℓp hp hp1
  let V := Vopen ∩ Vcollapsed
  refine ⟨V,hVopen.inter hVcollapsed,⟨hzeroOpen,hzeroCollapsed⟩,?_⟩
  intro ψ hψ hreal n a
  have hsum := (hopen ψ hψ.1 hreal n a).add
    (hcollapsed ψ hψ.2 hreal n a)
  have heq :
      ((fun m : ℤ =>
        if (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
            (periodOnePotential_mem ψ) m).re <
            (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
              (periodOnePotential_mem ψ) m).re then
          sourcePsiEquationCoordinate hp hp1 n m (a : Coeff p) ψ
            ((Real.pi : ℂ)*m) (Real.pi/8)
        else 0) +
      (fun m : ℤ =>
        if (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
            (periodOnePotential_mem ψ) m).re <
            (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
              (periodOnePotential_mem ψ) m).re then
          0
        else sourcePsiEquationCoordinate hp hp1 n m (a : Coeff p) ψ
          ((Real.pi : ℂ)*m) (Real.pi/8))) =
      (fun m : ℤ => sourcePsiEquationCoordinate hp hp1 n m
        (a : Coeff p) ψ ((Real.pi : ℂ)*m) (Real.pi/8)) := by
    funext m
    simp only [Pi.add_apply]
    by_cases hgap : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) m).re <
        (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
          (periodOnePotential_mem ψ) m).re
    · simp only [if_pos hgap, add_zero]
    · simp only [if_neg hgap, zero_add]
  simpa only [heq] using hsum

/-- Each near-free real-type source and deleted root input therefore
defines an actual element of the deleted-coordinate Banach space via
the complete fixed-circle psi equation. -/
theorem exists_nearFree_real_deletedPsi_equation_sequence
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ (0 : CoeffPair p) ∈ V ∧
      ∀ ψ ∈ V, IsRealType (CoeffPair.toMax p ψ) →
        ∀ n : ℤ, ∀ a : DeletedCoeff p n,
          ∃ F : DeletedCoeff p n, ∀ m : ℤ,
            (F : Coeff p) m =
              sourcePsiEquationCoordinate hp hp1 n m (a : Coeff p) ψ
                ((Real.pi : ℂ)*m) (Real.pi/8) := by
  obtain ⟨V,hVopen,hzero,hmem⟩ :=
    exists_nearFree_real_deletedPsi_equation_memℓp hp hp1
  refine ⟨V,hVopen,hzero,?_⟩
  intro ψ hψ hreal n a
  let F : Coeff p := ⟨fun m =>
    sourcePsiEquationCoordinate hp hp1 n m (a : Coeff p) ψ
      ((Real.pi : ℂ)*m) (Real.pi/8),hmem ψ hψ hreal n a⟩
  have hFn : F n = 0 := by
    simp [F,sourcePsiEquationCoordinate]
  exact ⟨⟨F,hFn⟩,fun _ => rfl⟩

end NLS.ZakharovShabat
