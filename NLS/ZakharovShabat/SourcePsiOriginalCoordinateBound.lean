import NLS.ZakharovShabat.SourcePsiOriginalQuotientBound
import NLS.ZakharovShabat.SourceLemma12_3
import NLS.ZakharovShabat.SourcePsiFilledRegularFactor

/-!
# Psi coordinate bounds on original disks at complex sources

Fill the unused numerator root with any point in its original disk.
Quantitative disk separation and Lemma 12.3 bound the literal coordinate
by the root, midpoint, and gap displacement magnitudes.
-/

noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Original separation extends to the closure of the selected disk. -/
theorem SourceIsolatingNeighborhoods.weighted_separation_closure
    {hp : p ≠ ⊤} {hp1 : 1 < p} {V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (n m : ℤ) (hmn : m ≠ n) (ξ : ℂ) (hξ : ξ ∈ D n)
    (z : ℂ) (hz : z ∈ closure (D m)) :
    z ≠ ξ ∧ ‖((n-m:ℤ):ℂ)‖ / ‖ξ-z‖ ≤ c := by
  have hc : 0 < c := zero_lt_one.trans_le hD.one_le
  have hclosed : IsClosed {w : ℂ | |((m-n:ℤ):ℝ)| ≤ c*‖ξ-w‖} :=
    isClosed_le continuous_const (continuous_const.mul ((continuous_const.sub continuous_id).norm))
  have hsep : |((m-n:ℤ):ℝ)| ≤ c*‖ξ-z‖ := by
    apply closure_minimal (t := {w : ℂ | |((m-n:ℤ):ℝ)| ≤ c*‖ξ-w‖}) ?_ hclosed hz
    intro w hw
    change |((m-n:ℤ):ℝ)| ≤ c*‖ξ-w‖
    have hd := (hD.pointwise_distance m n hmn w hw ξ hξ).1
    have hmul := mul_le_mul_of_nonneg_left hd hc.le
    simpa only [← mul_assoc,mul_inv_cancel₀ hc.ne',one_mul,dist_eq_norm,norm_sub_rev] using hmul
  have habs : 0 < |((m-n:ℤ):ℝ)| := by
    exact_mod_cast abs_pos.mpr (sub_ne_zero.mpr hmn)
  have hn : 0 < ‖ξ-z‖ := by nlinarith
  refine ⟨(sub_ne_zero.mp (norm_pos_iff.mp hn)).symm,?_⟩
  rw [Complex.norm_intCast,Int.cast_sub,abs_sub_comm]
  apply (div_le_iff₀ hn).mpr
  simpa only [Int.cast_sub] using hsep

/-- Distance from any point of a complex gap to an arbitrary numerator root. -/
theorem norm_displacedRoot_sub_gap_le (hp : p ≠ ⊤) (hp1 : 1 < p)
    (a : Coeff p) (ψ : CoeffPair p) (m : ℤ) (z : ℂ)
    (hz : z ∈ sourcePeriodicSegment hp hp1 ψ m) :
    ‖displacedRoots a m-z‖ ≤ ‖a m‖+
      ‖sourcePeriodicMidpointDisplacement hp hp1 ψ m‖+
      ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖ := by
  rw [← sourceStandardRoot_gapSegment_eq_periodicSegment] at hz
  obtain ⟨t,ht,rfl⟩ := hz
  have ht1 : ‖(t:ℂ)‖ ≤ 1 := by
    simpa only [Complex.norm_real,Real.norm_eq_abs] using abs_le.mpr ht
  have hhalf : ‖sourceStandardRootHalfGap hp hp1 ψ m‖ ≤
      ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖ := by
    simp only [sourceStandardRootHalfGap,sourcePeriodicGapDisplacement_apply,norm_div,Complex.norm_ofNat]
    linarith [norm_nonneg (canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m)]
  have hmid : displacedRoots a m-sourceStandardRootMidpoint hp hp1 ψ m =
      a m-sourcePeriodicMidpointDisplacement hp hp1 ψ m := by
    simp only [displacedRoots,sourceStandardRootMidpoint,sourcePeriodicMidpointDisplacement_apply]
    ring
  rw [← sub_sub,hmid]
  exact (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _)
    (by
      rw [norm_mul]
      calc
        _ ≤ ‖sourceStandardRootHalfGap hp hp1 ψ m‖*1 :=
          mul_le_mul_of_nonneg_left ht1 (norm_nonneg _)
        _ = ‖sourceStandardRootHalfGap hp hp1 ψ m‖ := mul_one _
        _ ≤ _ := hhalf))

/-- The normalized literal psi coordinate on an original circle is
bounded by a common quotient bound times the three lp displacements. -/
theorem SourceCorollary10_6Data.original_coordinate_bound
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    (H : SourceCorollary10_6Data hp hp1 W)
    {D : ℤ → Set ℂ} {c : ℝ} (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (ψ : CoeffPair p) (hψW : ψ ∈ W) (hψV : ψ ∈ V)
    (n m : ℤ) (hmn : m ≠ n) (a : DeletedCoeff p n) (ξ : ℂ) (hξ : ξ ∈ D n)
    (d r : ℝ) (hr : 0 < r) (he : D m = ball (d:ℂ) r)
    (C : ℝ)
    (hquot : ∀ z ∈ D m, ‖sourceSingleRootQuotientJointProduct hp hp1 m
      (z,(sourcePsiFillDeletedRoot n a ξ,ψ))‖ ≤ C) :
    ‖(2*(Real.pi:ℂ))⁻¹*sourcePsiEquationCoordinate hp hp1 n m (a:Coeff p) ψ (d:ℂ) r‖ ≤
      (‖(a:Coeff p) m‖+‖sourcePeriodicMidpointDisplacement hp hp1 ψ m‖+
        ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖)*(c*C) := by
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
  exact mul_le_mul (norm_displacedRoot_sub_gap_le hp hp1 (a:Coeff p) ψ m z hz)
    (hRbound z (hD.gap ψ hψV m hz)) (norm_nonneg _) (by positivity)

end NLS.ZakharovShabat
