import NLS.ZakharovShabat.SourcePsiNearFreeCollapsedGap
import NLS.ZakharovShabat.SourcePsiQuotientUniformHeadDisc

/-!
# A locally uniform bound for the real-type psi equation

The same regular-factor majorant controls both open and collapsed
selected gaps. Its locally uniform norm bound therefore controls the
whole deleted-coordinate psi equation near the free source.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- A supplied all-disc regular-factor majorant bounds every
normalized psi contour coordinate, with open and collapsed gaps
treated by their respective contour formulas. -/
theorem nearFree_real_deletedPsi_normalizedCoordinate_bound
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ) (a : DeletedCoeff p n)
    (W : Set (CoeffPair p)) (hψW : ψ ∈ W)
    (hQ : ∀ m : ℤ,
      AnalyticOnNhd ℂ (sourceSingleRootQuotientJointProduct hp hp1 m)
        (sourceSingleRootQuotientJointDomain hp hp1 W m))
    (hsmall : ∀ m : ℤ,
      ‖sourceStandardRootMidpoint hp hp1 ψ m - (Real.pi : ℂ)*m‖ ≤
        Real.pi/64 ∧
      ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖ ≤ Real.pi/32)
    (hgeom : ∀ m : ℤ,
      closedBall ((Real.pi : ℂ)*m) (Real.pi/4) ⊆
        sourceStandardRootOmittedDomain hp hp1 ψ m)
    (hcircle : ∀ m : ℤ,
      sphere ((Real.pi : ℂ)*m) (Real.pi/8) ⊆
        sourceCanonicalRootDomain hp hp1 ψ)
    (hseg : ∀ m : ℤ,
      sourcePeriodicSegment hp hp1 ψ m ⊆
        ball ((Real.pi : ℂ)*m) (Real.pi/8))
    (B : Coeff p)
    (hB : ∀ m : ℤ, m ≠ n →
      ∀ z ∈ closedBall ((Real.pi : ℂ)*m) (Real.pi/8),
        ‖(((n-m : ℤ) : ℂ) *
          sourcePsiGapRegularFactor hp hp1 n m
            (a : Coeff p) ψ z)‖ ≤
          (2/Real.pi)*(1+‖B m‖))
    (m : ℤ) :
    ‖(2*(Real.pi:ℂ))⁻¹ *
      sourcePsiEquationCoordinate hp hp1 n m (a : Coeff p) ψ
        ((Real.pi : ℂ)*m) (Real.pi/8)‖ ≤
      (‖(a : Coeff p) m‖ +
        ‖sourcePeriodicMidpointDisplacement hp hp1 ψ m‖ +
        ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖) *
          ((2/Real.pi)*(1+‖B m‖)) := by
  by_cases hmn : m = n
  · subst m
    simp [sourcePsiEquationCoordinate]
    positivity
  let cf : ℂ := (Real.pi : ℂ)*m
  let f : ℂ → ℂ := fun z => (((n-m : ℤ) : ℂ) *
    sourcePsiGapRegularFactor hp hp1 n m (a : Coeff p) ψ z)
  have hreg : AnalyticOnNhd ℂ f (closedBall cf (Real.pi/4)) := by
    apply analyticOnNhd_deletedPsi_gapRegularFactor_of_omitted_disc
      hp hp1 n m (Ne.symm hmn) a ψ W hψW (hQ m)
        (Real.pi/4) (by nlinarith [Real.pi_pos])
    exact hgeom m
  have havoid : ∀ z ∈ sphere cf (Real.pi/8),
      z ≠ displacedRoots (a : Coeff p) n := by
    intro z hz
    have ha : (a : Coeff p) n = 0 := a.property
    rw [show displacedRoots (a : Coeff p) n =
      (Real.pi : ℂ)*n by simp [displacedRoots,ha]]
    exact freeCircle_point_ne_freeCenter m n (Real.pi/8)
      (by positivity) (by nlinarith [Real.pi_pos]) z hz
  by_cases hopen :
      (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) m).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) m).re
  · let U : Set ℂ := ball cf (Real.pi/4)
    let g : ℂ → ℂ := fun z =>
      (displacedRoots (a : Coeff p) m-z) * f z
    obtain ⟨hR,hUdisc,hnest⟩ :=
      nearFree_realGap_nested_circle_geometry hp hp1 ψ hreal m hopen
        (hsmall m).1 (hsmall m).2
    have hseg₀ : sourcePeriodicSegment hp hp1 ψ m ⊆
        ball cf (Real.pi/8) := hseg m
    have hgapU : standardRootGapSegment
        (sourceStandardRootMidpoint hp hp1 ψ m)
        (sourceStandardRootHalfGap hp hp1 ψ m) ⊆ U := by
      exact (sourceStandardRoot_gapSegment_subset_periodicSegment
        hp hp1 ψ m).trans
          (hseg₀.trans (ball_subset_ball (by nlinarith [Real.pi_pos])))
    have hg : AnalyticOnNhd ℂ g U := by
      intro z hz
      have hz' : z ∈ closedBall cf (Real.pi/4) :=
        ball_subset_closedBall hz
      exact (analyticAt_const.sub analyticAt_id).mul (hreg z hz')
    have hnum (z : ℂ) (hz : z ∈ standardRootGapSegment
        (sourceStandardRootMidpoint hp hp1 ψ m)
        (sourceStandardRootHalfGap hp hp1 ψ m)) :
        ‖g z‖ ≤
          (‖(a : Coeff p) m‖ +
            ‖sourcePeriodicMidpointDisplacement hp hp1 ψ m‖ +
            ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖/2) *
              ((2/Real.pi)*(1+‖B m‖)) := by
      have hzseg : z ∈ sourcePeriodicSegment hp hp1 ψ m :=
        sourceStandardRoot_gapSegment_subset_periodicSegment
          hp hp1 ψ m hz
      have hzdisc : z ∈ closedBall cf (Real.pi/8) :=
        ball_subset_closedBall (hseg₀ hzseg)
      have hroot := norm_displacedRoot_sub_le_on_standardGap
        hp hp1 (a : Coeff p) ψ m z hz
      have hfactor := hB m hmn z hzdisc
      change ‖(displacedRoots (a : Coeff p) m-z) * f z‖ ≤ _
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_right hroot (norm_nonneg _)).trans
        (mul_le_mul_of_nonneg_left hfactor (by positivity))
    have hcoord :=
      norm_sourcePsiEquationCoordinate_le_gapNumerator_of_local_circle
        hp hp1 ψ hreal n m hopen (a : Coeff p) U isOpen_ball
        hgapU hg cf (Real.pi/8) (3*Real.pi/16) (by positivity)
        hseg₀ (hcircle m) havoid hR hUdisc hnest _ hnum
    exact hcoord.trans (by
      have hg0 : 0 ≤ ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖ :=
        norm_nonneg _
      have hf0 : 0 ≤ (2/Real.pi)*(1+‖B m‖) := by positivity
      apply mul_le_mul_of_nonneg_right _ hf0
      linarith)
  · have hgap := sourcePeriodicGap_eq_zero_of_real_not_open
      hp hp1 ψ hreal m hopen
    let τ := sourceStandardRootMidpoint hp hp1 ψ m
    let σ := displacedRoots (a : Coeff p) m
    have hτball : τ ∈ ball cf (Real.pi/8) := by
      rw [mem_ball,dist_eq_norm]
      exact (hsmall m).1.trans_lt (by nlinarith [Real.pi_pos])
    have hres := sourcePsiEquationCoordinate_collapsedGap_residue
      hp hp1 n m a ψ hgap cf (Real.pi/8) (by positivity)
        hτball (hcircle m) havoid
        (hreg.mono (Metric.closedBall_subset_closedBall
          (by nlinarith [Real.pi_pos])))
    have hπ : (2*(Real.pi:ℂ)) ≠ 0 := by simp [Real.pi_ne_zero]
    have hnorm : ‖(2*(Real.pi:ℂ))⁻¹ *
        sourcePsiEquationCoordinate hp hp1 n m (a : Coeff p) ψ
          cf (Real.pi/8)‖ = ‖τ-σ‖ * ‖f τ‖ := by
      rw [hres]
      have heq : (2*(Real.pi:ℂ))⁻¹ *
          ((2*(Real.pi:ℂ)*I)*(τ-σ)*f τ) = I*(τ-σ)*f τ := by
        field_simp [hπ]
      rw [heq]
      simp
    have hroot : ‖τ-σ‖ ≤ ‖(a : Coeff p) m‖ +
        ‖sourcePeriodicMidpointDisplacement hp hp1 ψ m‖ := by
      have hoff := sourcePsi_midpoint_offset_apply
        hp hp1 (a : Coeff p) ψ m
      change σ-τ =
        ((a : Coeff p)-sourcePeriodicMidpointDisplacement hp hp1 ψ) m
          at hoff
      rw [show τ-σ = -(σ-τ) by ring,norm_neg,hoff]
      simpa only [lp.coeFn_sub,Pi.sub_apply] using
        norm_sub_le ((a : Coeff p) m)
          (sourcePeriodicMidpointDisplacement hp hp1 ψ m)
    have hfactor := hB m hmn τ (ball_subset_closedBall hτball)
    rw [hnorm]
    calc
      ‖τ-σ‖ * ‖f τ‖ ≤
          (‖(a : Coeff p) m‖ +
            ‖sourcePeriodicMidpointDisplacement hp hp1 ψ m‖) * ‖f τ‖ :=
        mul_le_mul_of_nonneg_right hroot (norm_nonneg _)
      _ ≤ (‖(a : Coeff p) m‖ +
            ‖sourcePeriodicMidpointDisplacement hp hp1 ψ m‖) *
              ((2/Real.pi)*(1+‖B m‖)) :=
        mul_le_mul_of_nonneg_left hfactor (by positivity)
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        have hg0 : 0 ≤ ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖ :=
          norm_nonneg _
        linarith

/-- The midpoint and gap displacement sequences have uniformly
bounded norms on a small complex source neighborhood of zero. -/
theorem exists_nearFree_sourcePeriodicDisplacement_norms_le_one
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧
      (0 : CoeffPair p) ∈ V ∧
      ∀ ψ ∈ V,
        ‖sourcePeriodicMidpointDisplacement hp hp1 ψ‖ ≤ 1 ∧
        ‖sourcePeriodicGapDisplacement hp hp1 ψ‖ ≤ 1 := by
  have hmidCont := continuousAt_sourcePeriodicMidpointDisplacement_of_realType
    hp hp1 (0 : CoeffPair p) (by simp)
  have hgapCont := continuousAt_sourcePeriodicGapDisplacement_of_realType
    hp hp1 (0 : CoeffPair p) (by simp)
  obtain ⟨δm,hδm,hmid⟩ := Metric.continuousAt_iff.mp hmidCont
    1 (by norm_num)
  obtain ⟨δg,hδg,hgap⟩ := Metric.continuousAt_iff.mp hgapCont
    1 (by norm_num)
  let δ := min δm δg
  have hδ : 0 < δ := lt_min hδm hδg
  refine ⟨ball 0 δ,isOpen_ball,mem_ball_self hδ,?_⟩
  intro ψ hψ
  have hψm : dist ψ (0 : CoeffPair p) < δm :=
    (mem_ball.mp hψ).trans_le (min_le_left _ _)
  have hψg : dist ψ (0 : CoeffPair p) < δg :=
    (mem_ball.mp hψ).trans_le (min_le_right _ _)
  constructor
  · have h := hmid hψm
    rw [sourcePeriodicMidpointDisplacement_zero_source hp hp1,
      dist_zero_right] at h
    exact h.le
  · have h := hgap hψg
    rw [sourcePeriodicGapDisplacement_zero_source hp hp1,
      dist_zero_right] at h
    exact h.le

/-- Near every root input over the free source, the complete real-type
psi contour equation is a deleted `ℓᵖ` sequence with a locally uniform
norm bound, independent of the deleted index. -/
theorem exists_nearFree_real_deletedPsi_equation_uniformNorm
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (a₀ : Coeff p) :
    ∃ U : Set (Coeff p × CoeffPair p), IsOpen U ∧
      (a₀,(0 : CoeffPair p)) ∈ U ∧
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ n : ℤ, ∀ a : DeletedCoeff p n, ∀ ψ : CoeffPair p,
          IsRealType (CoeffPair.toMax p ψ) →
          ((a : Coeff p),ψ) ∈ U →
            ∃ F : DeletedCoeff p n,
              (∀ m : ℤ, (F : Coeff p) m =
                sourcePsiEquationCoordinate hp hp1 n m
                  (a : Coeff p) ψ ((Real.pi : ℂ)*m) (Real.pi/8)) ∧
              ‖F‖ ≤ C := by
  obtain ⟨Ureg,hUregOpen,hbaseReg,M,hM,hreg⟩ :=
    exists_nearFree_deletedPsi_uniformRegularFactorMajorant hp hp1 a₀
  obtain ⟨Vsmall,hVsmallOpen,hzeroSmall,hsmall⟩ :=
    exists_nearFree_allPeriodicMidpointGap_small hp hp1
  obtain ⟨Vgeom,hVgeomOpen,hzeroGeom,hgeom⟩ :=
    exists_nearFree_freeQuarterDisc_subset_omittedDomain hp hp1
  obtain ⟨Vcircle,hVcircleOpen,hzeroCircle,hcircle⟩ :=
    exists_nearFree_freeEighthCircle_subset_rootDomain hp hp1
  obtain ⟨Vseg,hVsegOpen,hzeroSeg,hseg⟩ :=
    exists_nearFree_allPeriodicSegments_in_eighth_ball hp hp1
  obtain ⟨Vnorm,hVnormOpen,hzeroNorm,hnorm⟩ :=
    exists_nearFree_sourcePeriodicDisplacement_norms_le_one hp hp1
  obtain ⟨W,hWopen,_,hrealW,hQ⟩ :=
    exists_global_source_analytic_singleRootQuotient hp hp1
  have hzeroW : (0 : CoeffPair p) ∈ W :=
    hrealW (by simp [realTypeSourceLocus])
  let V := Vsmall ∩ Vgeom ∩ Vcircle ∩ Vseg ∩ Vnorm ∩ W
  have hVopen : IsOpen V :=
    (((hVsmallOpen.inter hVgeomOpen).inter hVcircleOpen).inter
      hVsegOpen).inter hVnormOpen |>.inter hWopen
  have hzeroV : (0 : CoeffPair p) ∈ V :=
    ⟨⟨⟨⟨⟨hzeroSmall,hzeroGeom⟩,hzeroCircle⟩,hzeroSeg⟩,
      hzeroNorm⟩,hzeroW⟩
  let U : Set (Coeff p × CoeffPair p) :=
    Ureg ∩ (ball a₀ 1 ×ˢ V)
  have hUopen : IsOpen U := hUregOpen.inter (isOpen_ball.prod hVopen)
  have hbase : (a₀,(0 : CoeffPair p)) ∈ U :=
    ⟨hbaseReg,mem_ball_self (by norm_num),hzeroV⟩
  let T : ℝ := ‖a₀‖+1
  let C₀ : ℝ := 4*(1+M)
  let C : ℝ := C₀*(T+2)
  have hC₀ : 0 ≤ C₀ := by dsimp [C₀]; positivity
  have hC : 0 ≤ C := by dsimp [C,T]; positivity
  refine ⟨U,hUopen,hbase,C,hC,?_⟩
  intro n a ψ hreal hpair
  obtain ⟨hpairReg,haBall,hψV⟩ := hpair
  obtain ⟨⟨⟨⟨⟨hψsmall,hψgeom⟩,hψcircle⟩,hψseg⟩,
    hψnorm⟩,hψW⟩ := hψV
  obtain ⟨B,hBnorm,hB⟩ := hreg n a ψ hpairReg
  let P := sourcePeriodicMidpointDisplacement hp hp1 ψ
  let G := sourcePeriodicGapDisplacement hp hp1 ψ
  let A : Coeff p := Coeff.magnitude (a : Coeff p) +
    Coeff.magnitude P + Coeff.magnitude G
  have hAcoord (m : ℤ) : ‖A m‖ =
      ‖(a : Coeff p) m‖+‖P m‖+‖G m‖ := by
    simp only [A,lp.coeFn_add,Pi.add_apply,Coeff.magnitude_apply,
      ← Complex.ofReal_add,Complex.norm_real]
    exact Real.norm_of_nonneg (by positivity)
  have hAnorm : ‖A‖ ≤ ‖(a : Coeff p)‖+‖P‖+‖G‖ := by
    calc
      ‖A‖ ≤ ‖Coeff.magnitude (a : Coeff p)‖+
          ‖Coeff.magnitude P‖+‖Coeff.magnitude G‖ := by
        dsimp [A]
        exact (norm_add_le _ _).trans
          (add_le_add (norm_add_le _ _) le_rfl)
      _ = _ := by simp only [Coeff.norm_magnitude]
  have ha : ‖(a : Coeff p)‖ ≤ T := by
    have hdist : ‖(a : Coeff p)-a₀‖ < 1 := by
      simpa only [mem_ball,dist_eq_norm] using haBall
    have hsum : ‖(a : Coeff p)‖ ≤ ‖a₀‖+‖(a : Coeff p)-a₀‖ := by
      have heq : (a : Coeff p) = a₀+((a : Coeff p)-a₀) := by abel
      calc
        ‖(a : Coeff p)‖ = ‖a₀+((a : Coeff p)-a₀)‖ :=
          congrArg norm heq
        _ ≤ _ := norm_add_le _ _
    dsimp [T]
    linarith
  have hAglobal : ‖A‖ ≤ T+2 := by
    have hPN := (hnorm ψ hψnorm).1
    have hGN := (hnorm ψ hψnorm).2
    linarith
  let Fraw : ℤ → ℂ := fun m =>
    sourcePsiEquationCoordinate hp hp1 n m (a : Coeff p) ψ
      ((Real.pi : ℂ)*m) (Real.pi/8)
  have hπ : (2*(Real.pi:ℂ)) ≠ 0 := by simp [Real.pi_ne_zero]
  have hnormalize (X : ℂ) : ‖X‖ =
      (2*Real.pi)*‖(2*(Real.pi:ℂ))⁻¹ * X‖ := by
    have heq : (2*(Real.pi:ℂ)) *
        ((2*(Real.pi:ℂ))⁻¹*X) = X := by
      rw [← mul_assoc,mul_inv_cancel₀ hπ,one_mul]
    calc
      ‖X‖ = ‖(2*(Real.pi:ℂ)) *
          ((2*(Real.pi:ℂ))⁻¹*X)‖ := congrArg norm heq.symm
      _ = _ := by
        rw [norm_mul]
        simp [Complex.norm_real,Real.norm_eq_abs,
          abs_of_pos Real.pi_pos]
  have hpoint (m : ℤ) : ‖Fraw m‖ ≤ C₀*‖A m‖ := by
    have hcoord := nearFree_real_deletedPsi_normalizedCoordinate_bound
      hp hp1 ψ hreal n a W hψW (fun k => (hQ k).2)
        (hsmall ψ hψsmall) (hgeom ψ hψgeom)
        (hcircle ψ hψcircle) (hseg ψ hψseg) B hB m
    have hBcoord : ‖B m‖ ≤ M :=
      (lp.norm_apply_le_norm
        (ne_of_gt (zero_lt_one.trans_le Fact.out)) B m).trans hBnorm
    calc
      ‖Fraw m‖ = (2*Real.pi)*
          ‖(2*(Real.pi:ℂ))⁻¹ * Fraw m‖ := hnormalize _
      _ ≤ (2*Real.pi)*(‖A m‖*((2/Real.pi)*(1+‖B m‖))) := by
        gcongr
        simpa only [Fraw,hAcoord] using hcoord
      _ ≤ (2*Real.pi)*(‖A m‖*((2/Real.pi)*(1+M))) := by
        gcongr
      _ = C₀*‖A m‖ := by
        dsimp [C₀]
        field_simp [Real.pi_ne_zero]
        ring
  let D : Coeff p := (C₀ : ℂ) • A
  have hDcoord (m : ℤ) : ‖D m‖ = C₀*‖A m‖ := by
    simp only [D,lp.coeFn_smul,Pi.smul_apply,norm_smul,
      Complex.norm_real,Real.norm_of_nonneg hC₀]
  have hmajor : Memℓp (fun m : ℤ => C₀*‖A m‖) p :=
    (lp.memℓp A).norm.const_mul C₀
  have hmem : Memℓp Fraw p := by
    apply hmajor.mono
    intro m
    exact hpoint m
  let Fcoeff : Coeff p := ⟨Fraw,hmem⟩
  have hFn : Fcoeff n = 0 := by
    simp [Fcoeff,Fraw,sourcePsiEquationCoordinate]
  let F : DeletedCoeff p n := ⟨Fcoeff,hFn⟩
  refine ⟨F,fun _ => rfl,?_⟩
  have hFle : ‖Fcoeff‖ ≤ ‖D‖ := by
    apply lp.norm_mono (zero_lt_one.trans hp1).ne'
    intro m
    rw [hDcoord]
    exact hpoint m
  have hDnorm : ‖D‖ = C₀*‖A‖ := by
    simp only [D,norm_smul,Complex.norm_real,Real.norm_of_nonneg hC₀]
  change ‖Fcoeff‖ ≤ C
  calc
    ‖Fcoeff‖ ≤ ‖D‖ := hFle
    _ = C₀*‖A‖ := hDnorm
    _ ≤ C₀*(T+2) := mul_le_mul_of_nonneg_left hAglobal hC₀
    _ = C := rfl

end NLS.ZakharovShabat
