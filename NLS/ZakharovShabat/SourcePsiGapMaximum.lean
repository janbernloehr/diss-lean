import NLS.ZakharovShabat.SourcePsiOriginalCoordinateBound

/-!
# The exact gap maximum in the proof of Lemma 12.4

The raw contour coordinate is bounded by 2*pi*c*C times the attained
root-distance maximum. The midpoint maximum equals half the gap norm,
including complex and collapsed gaps.
-/

noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem SourceCorollary10_6Data.original_coordinate_bound_of_gap_bound
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    (H : SourceCorollary10_6Data hp hp1 W)
    {D : ℤ → Set ℂ} {c : ℝ} (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (ψ : CoeffPair p) (hψW : ψ ∈ W) (hψV : ψ ∈ V)
    (n m : ℤ) (hmn : m ≠ n) (a : DeletedCoeff p n) (ξ : ℂ) (hξ : ξ ∈ D n)
    (d r : ℝ) (hr : 0 < r) (he : D m = ball (d:ℂ) r)
    (C B : ℝ)
    (hB : ∀ z ∈ sourcePeriodicSegment hp hp1 ψ m, ‖displacedRoots (a:Coeff p) m-z‖ ≤ B)
    (hquot : ∀ z ∈ D m, ‖sourceSingleRootQuotientJointProduct hp hp1 m
      (z,(sourcePsiFillDeletedRoot n a ξ,ψ))‖ ≤ C) :
    ‖(2*(Real.pi:ℂ))⁻¹*sourcePsiEquationCoordinate hp hp1 n m (a:Coeff p) ψ (d:ℂ) r‖ ≤
      B*(c*C) := by
  let b := sourcePsiFillDeletedRoot n a ξ
  let P := hD.periodCircle ψ hψV m d r hr he
  let R : ℂ → ℂ := fun z => ((n-m:ℤ):ℂ)*sourcePsiGapRegularFactor hp hp1 n m b ψ z
  let f : ℂ → ℂ := fun z => (displacedRoots (a:Coeff p) m-z)*R z
  have hcl : closedBall (d:ℂ) r = closure (D m) := by rw [he,closure_ball _ hr.ne']
  have hsep (z : ℂ) (hz : z ∈ closedBall (d:ℂ) r) :=
    hD.weighted_separation_closure n m hmn ξ hξ z (hcl ▸ hz)
  have hRanalytic : AnalyticOnNhd ℂ R (closedBall (d:ℂ) r) := by
    intro z hz
    have hQ := H.spectral ψ hψW b m z (P.closedBall_subset_omittedDomain hz)
    simp only [R,sourcePsiGapRegularFactor,
      show displacedRoots b n = ξ from displacedRoots_sourcePsiFillDeletedRoot_same n a ξ]
    exact analyticAt_const.mul ((analyticAt_const.mul hQ).div
      (analyticAt_const.sub analyticAt_id) (sub_ne_zero.mpr (hsep z hz).1.symm))
  have hf : AnalyticOnNhd ℂ f (closedBall (d:ℂ) r) := by
    intro z hz
    exact (analyticAt_const.sub analyticAt_id).mul (hRanalytic z hz)
  have hRbound (z : ℂ) (hz : z ∈ D m) : ‖R z‖ ≤ c*C := by
    have hs := hD.weighted_separation_closure n m hmn ξ hξ z (subset_closure hz)
    simp only [R,sourcePsiGapRegularFactor,b,displacedRoots_sourcePsiFillDeletedRoot_same,
      norm_mul,norm_div,norm_I,one_mul]
    rw [← mul_div_assoc,mul_div_right_comm]
    exact mul_le_mul hs.2 (hquot z hz) (norm_nonneg _) (zero_le_one.trans hD.one_le)
  have heq : sourcePsiEquationCoordinate hp hp1 n m (a:Coeff p) ψ (d:ℂ) r =
      ∮ z in C((d:ℂ),r), f z/sourceStandardRoot hp hp1 ψ m z := by
    have hfill := sourcePsiEquationCoordinate_fillDeletedRoot hp hp1 n m a ξ ψ (d:ℂ) r hr.le
    change sourcePsiEquationCoordinate hp hp1 n m b ψ (d:ℂ) r =
      sourcePsiEquationCoordinate hp hp1 n m (a:Coeff p) ψ (d:ℂ) r at hfill
    rw [← hfill,sourcePsiEquationCoordinate_eq_gap_factor_circleIntegral hp hp1 n m b ψ
      (d:ℂ) r hr.le P.sphere_subset_rootDomain (by
        intro z hz
        simpa only [b,displacedRoots_sourcePsiFillDeletedRoot_same] using (hsep z (sphere_subset_closedBall hz)).1),
      ← circleIntegral.integral_const_mul]
    apply circleIntegral.integral_congr hr.le
    intro z _
    dsimp only [f,R]
    rw [show displacedRoots b m = displacedRoots (a:Coeff p) m from
      displacedRoots_sourcePsiFillDeletedRoot_other n m hmn a ξ]
    ring
  obtain ⟨z,hz,_,hb,_⟩ := P.lemma12_3_circle f hf
  rw [PiecewiseC1Loop.integral_circle] at hb
  rw [heq]
  apply hb.trans
  rw [show ‖f z‖ = ‖displacedRoots (a:Coeff p) m-z‖*‖R z‖ from norm_mul _ _]
  exact mul_le_mul (hB z hz)
    (hRbound z (hD.gap ψ hψV m hz)) (norm_nonneg _)
    ((norm_nonneg _).trans (hB z hz))


/-- The displayed gap maximum in the proof of Lemma 12.4 is attained. -/
theorem SourceCorollary10_6Data.original_coordinate_gap_maximum
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    (H : SourceCorollary10_6Data hp hp1 W)
    {D : ℤ → Set ℂ} {c : ℝ} (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (ψ : CoeffPair p) (hψW : ψ ∈ W) (hψV : ψ ∈ V)
    (n m : ℤ) (hmn : m ≠ n) (a : DeletedCoeff p n) (ξ : ℂ) (hξ : ξ ∈ D n)
    (d r : ℝ) (hr : 0 < r) (he : D m = ball (d:ℂ) r) (C : ℝ)
    (hquot : ∀ z ∈ D m, ‖sourceSingleRootQuotientJointProduct hp hp1 m
      (z,(sourcePsiFillDeletedRoot n a ξ,ψ))‖ ≤ C) :
    ∃ z ∈ sourcePeriodicSegment hp hp1 ψ m,
      IsMaxOn (fun z => ‖displacedRoots (a:Coeff p) m-z‖)
        (sourcePeriodicSegment hp hp1 ψ m) z ∧
      ‖sourcePsiEquationCoordinate hp hp1 n m (a:Coeff p) ψ (d:ℂ) r‖ ≤
        (2*Real.pi*(c*C))*‖displacedRoots (a:Coeff p) m-z‖ := by
  have hcompact : IsCompact (sourcePeriodicSegment hp hp1 ψ m) := by
    rw [← sourceStandardRoot_gapSegment_eq_periodicSegment]
    exact standardRootGapSegment_compact _ _
  have hne : (sourcePeriodicSegment hp hp1 ψ m).Nonempty :=
    ⟨_, sourcePeriodicMidpoint_mem_segment hp hp1 ψ m⟩
  obtain ⟨z,hz,hmax⟩ := hcompact.exists_isMaxOn hne
    ((continuous_const.sub continuous_id).norm.continuousOn)
  refine ⟨z,hz,hmax,?_⟩
  have hb := H.original_coordinate_bound_of_gap_bound hD ψ hψW hψV n m hmn a ξ hξ
    d r hr he C ‖displacedRoots (a:Coeff p) m-z‖ (fun w hw => hmax hw) hquot
  let f := sourcePsiEquationCoordinate hp hp1 n m (a:Coeff p) ψ (d:ℂ) r
  have hscale : ‖f‖ = (2*Real.pi)*‖(2*(Real.pi:ℂ))⁻¹*f‖ := by
    rw [norm_mul,norm_inv,norm_mul]
    simp only [Complex.norm_ofNat,Complex.norm_real,Real.norm_of_nonneg Real.pi_pos.le]
    field_simp
  change ‖f‖ ≤ _
  rw [hscale]
  exact (mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ 2*Real.pi)).trans_eq (by ring)

/-- The maximum distance from the gap midpoint is exactly one half of the gap length. -/
theorem sourcePeriodicSegment_midpoint_maximum
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (m : ℤ) :
    ∃ z ∈ sourcePeriodicSegment hp hp1 ψ m,
      IsMaxOn (fun w => ‖sourceStandardRootMidpoint hp hp1 ψ m-w‖)
        (sourcePeriodicSegment hp hp1 ψ m) z ∧
      ‖sourceStandardRootMidpoint hp hp1 ψ m-z‖ =
        ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖/2 := by
  let τ := sourceStandardRootMidpoint hp hp1 ψ m
  let δ := sourceStandardRootHalfGap hp hp1 ψ m
  have hz : τ+δ ∈ sourcePeriodicSegment hp hp1 ψ m := by
    rw [← sourceStandardRoot_gapSegment_eq_periodicSegment]
    exact ⟨1,by norm_num,by simp [τ,δ]⟩
  have hnorm : ‖τ-(τ+δ)‖ = ‖δ‖ := by
    rw [show τ-(τ+δ) = -δ by ring,norm_neg]
  refine ⟨τ+δ,hz,?_,?_⟩
  · intro w hw
    rw [← sourceStandardRoot_gapSegment_eq_periodicSegment] at hw
    obtain ⟨t,ht,rfl⟩ := hw
    change ‖τ-(τ+δ*(t:ℂ))‖ ≤ ‖τ-(τ+δ)‖
    rw [hnorm,show τ-(τ+δ*(t:ℂ)) = -δ*(t:ℂ) by ring,norm_mul,norm_neg]
    have ht1 : ‖(t:ℂ)‖ ≤ 1 := by
      simpa only [Complex.norm_real,Real.norm_eq_abs] using abs_le.mpr ht
    exact (mul_le_mul_of_nonneg_left ht1 (norm_nonneg δ)).trans_eq (mul_one _)
  · change ‖τ-(τ+δ)‖ = _
    rw [hnorm]
    simp only [δ,sourceStandardRootHalfGap,sourcePeriodicGapDisplacement_apply,norm_div,norm_ofNat]

end NLS.ZakharovShabat
