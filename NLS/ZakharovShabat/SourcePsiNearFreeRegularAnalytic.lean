import NLS.ZakharovShabat.SourcePsiNearFreeDiscMajorant

/-!
# Analyticity and uniform bounds for the near-free psi gap factor

The factor multiplying the selected inverse standard root in (2.27)
must extend through that selected gap. The omitted-root quotient is
analytic there, and the deleted root is fixed at the distant free
lattice center. This file combines that analyticity with the all-disc
majorant from Lemma 10.8 on one source neighborhood.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The affine cosine gap used in the standard-root boundary integral
lies on the actual straight segment between the periodic endpoints. -/
theorem sourceStandardRoot_gapSegment_subset_periodicSegment
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (m : ℤ) :
    standardRootGapSegment
      (sourceStandardRootMidpoint hp hp1 ψ m)
      (sourceStandardRootHalfGap hp hp1 ψ m) ⊆
        sourcePeriodicSegment hp hp1 ψ m := by
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) m
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) m
  rintro z ⟨t,ht,rfl⟩
  obtain ⟨htlo,hthi⟩ := ht
  change sourceStandardRootMidpoint hp hp1 ψ m +
    sourceStandardRootHalfGap hp hp1 ψ m * (t : ℂ) ∈ segment ℝ l r
  refine ⟨(1-t)/2,(1+t)/2,by linarith,
    by linarith,by ring,?_⟩
  simp only [Complex.real_smul]
  change (((1-t)/2 : ℝ) : ℂ) * l +
    (((1+t)/2 : ℝ) : ℂ) * r =
      (l+r)/2 + ((r-l)/2) * (t : ℂ)
  push_cast
  ring

/-- On the selected gap, the psi numerator root differs from the
spectral point by the root, midpoint, and half-gap displacements.
These three coordinate sequences belong to `ℓᵖ`. -/
theorem norm_displacedRoot_sub_le_on_standardGap
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (a : Coeff p) (ψ : CoeffPair p) (m : ℤ)
    (z : ℂ)
    (hz : z ∈ standardRootGapSegment
      (sourceStandardRootMidpoint hp hp1 ψ m)
      (sourceStandardRootHalfGap hp hp1 ψ m)) :
    ‖displacedRoots a m-z‖ ≤
      ‖a m‖ + ‖sourcePeriodicMidpointDisplacement hp hp1 ψ m‖ +
        ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖/2 := by
  obtain ⟨t,ht,rfl⟩ := hz
  let τ := sourceStandardRootMidpoint hp hp1 ψ m
  let δ := sourceStandardRootHalfGap hp hp1 ψ m
  let M := sourcePeriodicMidpointDisplacement hp hp1 ψ
  let G := sourcePeriodicGapDisplacement hp hp1 ψ
  have hoff : displacedRoots a m-τ = (a-M) m := by
    exact sourcePsi_midpoint_offset_apply hp hp1 a ψ m
  have hsplit : displacedRoots a m-(τ+δ*(t:ℂ)) =
      (displacedRoots a m-τ)-δ*(t:ℂ) := by ring
  have hmid : ‖(a-M) m‖ ≤ ‖a m‖+‖M m‖ := by
    simpa only [lp.coeFn_sub,Pi.sub_apply] using norm_sub_le (a m) (M m)
  have htabs : |t| ≤ 1 := abs_le.mpr ht
  have hδ : ‖δ‖ = ‖G m‖/2 := by
    dsimp [δ,G]
    rw [sourcePeriodicGapDisplacement_apply]
    simp
  rw [hsplit,hoff]
  calc
    ‖(a-M) m-δ*(t:ℂ)‖ ≤ ‖(a-M) m‖+‖δ*(t:ℂ)‖ := norm_sub_le _ _
    _ ≤ (‖a m‖+‖M m‖)+‖δ‖*|t| := by
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
      exact add_le_add_left hmid _
    _ ≤ (‖a m‖+‖M m‖)+‖δ‖ := by
      have hmul : ‖δ‖*|t| ≤ ‖δ‖ := by
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_left htabs (norm_nonneg δ)
      linarith
    _ = ‖a m‖+‖M m‖+‖G m‖/2 := by rw [hδ]

/-- The weighted regular psi gap factor is analytic throughout a
selected free-centered disc when the other standard roots avoid it.
The deleted numerator root is fixed at its free center. -/
theorem analyticOnNhd_deletedPsi_gapRegularFactor_of_omitted_disc
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n m : ℤ) (hnm : n ≠ m) (a : DeletedCoeff p n)
    (ψ : CoeffPair p) (W : Set (CoeffPair p)) (hψW : ψ ∈ W)
    (hQ : AnalyticOnNhd ℂ
      (sourceSingleRootQuotientJointProduct hp hp1 m)
      (sourceSingleRootQuotientJointDomain hp hp1 W m))
    (R : ℝ) (hRπ : R < Real.pi)
    (hdom : closedBall ((Real.pi : ℂ)*m) R ⊆
      sourceStandardRootOmittedDomain hp hp1 ψ m) :
    AnalyticOnNhd ℂ
      (fun z => (((n-m : ℤ) : ℂ) *
        sourcePsiGapRegularFactor hp hp1 n m (a : Coeff p) ψ z))
      (closedBall ((Real.pi : ℂ)*m) R) := by
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
    exact (freeCenter_not_mem_closedBall_other m n (Ne.symm hnm) R hRπ)
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

/-- Near the free source, every periodic midpoint and gap is small
relative to its free lattice center, with one source neighborhood for
all indices. -/
theorem exists_nearFree_allPeriodicMidpointGap_small
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ (0 : CoeffPair p) ∈ V ∧
      ∀ ψ ∈ V, ∀ m : ℤ,
        ‖sourceStandardRootMidpoint hp hp1 ψ m - (Real.pi : ℂ)*m‖ ≤
          Real.pi/64 ∧
        ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖ ≤ Real.pi/32 := by
  have hmidCont := continuousAt_sourcePeriodicMidpointDisplacement_of_realType
    hp hp1 (0 : CoeffPair p) (by simp)
  have hgapCont := continuousAt_sourcePeriodicGapDisplacement_of_realType
    hp hp1 (0 : CoeffPair p) (by simp)
  obtain ⟨δm,hδm,hmid⟩ := Metric.continuousAt_iff.mp hmidCont
    (Real.pi/64) (by positivity)
  obtain ⟨δg,hδg,hgap⟩ := Metric.continuousAt_iff.mp hgapCont
    (Real.pi/32) (by positivity)
  let δ := min δm δg
  have hδ : 0 < δ := lt_min hδm hδg
  refine ⟨ball 0 δ,isOpen_ball,mem_ball_self hδ,?_⟩
  intro ψ hψ m
  have hψm : dist ψ (0 : CoeffPair p) < δm :=
    (mem_ball.mp hψ).trans_le (min_le_left _ _)
  have hψg : dist ψ (0 : CoeffPair p) < δg :=
    (mem_ball.mp hψ).trans_le (min_le_right _ _)
  have hmnorm : ‖sourcePeriodicMidpointDisplacement hp hp1 ψ‖ <
      Real.pi/64 := by
    have h := hmid hψm
    rw [sourcePeriodicMidpointDisplacement_zero_source hp hp1,
      dist_zero_right] at h
    exact h
  have hgnorm : ‖sourcePeriodicGapDisplacement hp hp1 ψ‖ <
      Real.pi/32 := by
    have h := hgap hψg
    rw [sourcePeriodicGapDisplacement_zero_source hp hp1,
      dist_zero_right] at h
    exact h
  constructor
  · have hcoord := lp.norm_apply_le_norm
      (ne_of_gt (zero_lt_one.trans_le Fact.out))
      (sourcePeriodicMidpointDisplacement hp hp1 ψ) m
    have hc : ‖sourceStandardRootMidpoint hp hp1 ψ m -
        (Real.pi : ℂ)*m‖ ≤
        ‖sourcePeriodicMidpointDisplacement hp hp1 ψ‖ := by
      simpa only [sourcePeriodicMidpointDisplacement_apply,
        sourceStandardRootMidpoint] using hcoord
    exact (hc.trans_lt hmnorm).le
  · exact (lp.norm_apply_le_norm
      (ne_of_gt (zero_lt_one.trans_le Fact.out))
      (sourcePeriodicGapDisplacement hp hp1 ψ) m).trans hgnorm.le

/-- One near-free source neighborhood supplies both analyticity and
an `ℓᵖ` majorant for the weighted regular factor on every selected
eighth-π disc, uniformly in the deleted index. -/
theorem exists_nearFree_deletedPsi_gapRegularFactor_analytic_majorant
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ (0 : CoeffPair p) ∈ V ∧
      ∀ ψ ∈ V, ∀ n : ℤ, ∀ a : DeletedCoeff p n,
        ∃ B : Coeff p, ∀ m : ℤ, m ≠ n →
          AnalyticOnNhd ℂ
            (fun z => (((n-m : ℤ) : ℂ) *
              sourcePsiGapRegularFactor hp hp1 n m
                (a : Coeff p) ψ z))
            (closedBall ((Real.pi : ℂ)*m) (Real.pi/8)) ∧
          (∀ z ∈ closedBall ((Real.pi : ℂ)*m) (Real.pi/8),
            ‖(((n-m : ℤ) : ℂ) *
              sourcePsiGapRegularFactor hp hp1 n m
                (a : Coeff p) ψ z)‖ ≤
              (2/Real.pi)*(1+‖B m‖)) := by
  obtain ⟨Vmajor,hVmajorOpen,hzeroMajor,hmajor⟩ :=
    exists_nearFree_deletedPsi_gapRegularFactor_allDiscMajorant hp hp1
  obtain ⟨Vgeom,hVgeomOpen,hzeroGeom,hgeom⟩ :=
    exists_nearFree_freeQuarterDisc_subset_omittedDomain hp hp1
  obtain ⟨W,hWopen,_,hreal,hdata⟩ :=
    exists_global_source_analytic_singleRootQuotient hp hp1
  have hzeroW : (0 : CoeffPair p) ∈ W :=
    hreal (by simp [realTypeSourceLocus])
  let V := Vmajor ∩ Vgeom ∩ W
  refine ⟨V,(hVmajorOpen.inter hVgeomOpen).inter hWopen,
    ⟨⟨hzeroMajor,hzeroGeom⟩,hzeroW⟩,?_⟩
  intro ψ hψ n a
  obtain ⟨B,hB⟩ := hmajor ψ hψ.1.1 n a
  refine ⟨B,?_⟩
  intro m hmn
  constructor
  · apply analyticOnNhd_deletedPsi_gapRegularFactor_of_omitted_disc
      hp hp1 n m (Ne.symm hmn) a ψ W hψ.2 (hdata m).2
        (Real.pi/8) (by nlinarith [Real.pi_pos])
    exact (Metric.closedBall_subset_closedBall
      (by nlinarith [Real.pi_pos])).trans (hgeom ψ hψ.1.2 m)
  · exact hB m hmn

/-- Near the free source, the complete numerator in the selected-gap
form of the psi equation is analytic on every selected disc. On the
gap its norm is controlled by an `ℓᵖ` displacement scale times the
uniform regular-factor bound. -/
theorem exists_nearFree_deletedPsi_gapNumerator_analytic_bound
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ (0 : CoeffPair p) ∈ V ∧
      ∀ ψ ∈ V, ∀ n : ℤ, ∀ a : DeletedCoeff p n,
        ∃ B : Coeff p, ∀ m : ℤ, m ≠ n →
          AnalyticOnNhd ℂ
            (fun z => (displacedRoots (a : Coeff p) m-z) *
              (((n-m : ℤ) : ℂ) *
                sourcePsiGapRegularFactor hp hp1 n m
                  (a : Coeff p) ψ z))
            (closedBall ((Real.pi : ℂ)*m) (Real.pi/8)) ∧
          (∀ z ∈ standardRootGapSegment
              (sourceStandardRootMidpoint hp hp1 ψ m)
              (sourceStandardRootHalfGap hp hp1 ψ m),
            ‖(displacedRoots (a : Coeff p) m-z) *
              (((n-m : ℤ) : ℂ) *
                sourcePsiGapRegularFactor hp hp1 n m
                  (a : Coeff p) ψ z)‖ ≤
              (‖(a : Coeff p) m‖ +
                ‖sourcePeriodicMidpointDisplacement hp hp1 ψ m‖ +
                ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖/2) *
                  ((2/Real.pi)*(1+‖B m‖))) := by
  obtain ⟨Vreg,hVregOpen,hzeroReg,hreg⟩ :=
    exists_nearFree_deletedPsi_gapRegularFactor_analytic_majorant hp hp1
  obtain ⟨Vseg,hVsegOpen,hzeroSeg,hseg⟩ :=
    exists_nearFree_allPeriodicSegments_in_eighth_ball hp hp1
  let V := Vreg ∩ Vseg
  refine ⟨V,hVregOpen.inter hVsegOpen,⟨hzeroReg,hzeroSeg⟩,?_⟩
  intro ψ hψ n a
  obtain ⟨B,hB⟩ := hreg ψ hψ.1 n a
  refine ⟨B,?_⟩
  intro m hmn
  obtain ⟨hanalytic,hbound⟩ := hB m hmn
  constructor
  · intro z hz
    exact (analyticAt_const.sub analyticAt_id).mul (hanalytic z hz)
  · intro z hz
    have hzseg : z ∈ sourcePeriodicSegment hp hp1 ψ m :=
      sourceStandardRoot_gapSegment_subset_periodicSegment hp hp1 ψ m hz
    have hzdisc : z ∈ closedBall ((Real.pi : ℂ)*m) (Real.pi/8) :=
      ball_subset_closedBall (hseg ψ hψ.2 m hzseg)
    have hroot := norm_displacedRoot_sub_le_on_standardGap
      hp hp1 (a : Coeff p) ψ m z hz
    have hfactor := hbound z hzdisc
    rw [norm_mul]
    calc
      ‖displacedRoots (a : Coeff p) m-z‖ *
          ‖(((n-m : ℤ) : ℂ) *
            sourcePsiGapRegularFactor hp hp1 n m (a : Coeff p) ψ z)‖ ≤
        (‖(a : Coeff p) m‖ +
          ‖sourcePeriodicMidpointDisplacement hp hp1 ψ m‖ +
          ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖/2) *
          ‖(((n-m : ℤ) : ℂ) *
            sourcePsiGapRegularFactor hp hp1 n m (a : Coeff p) ψ z)‖ :=
        mul_le_mul_of_nonneg_right hroot (norm_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_left hfactor (by positivity)

end NLS.ZakharovShabat
