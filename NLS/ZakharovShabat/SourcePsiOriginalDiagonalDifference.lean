import NLS.ZakharovShabat.SourcePsiOriginalIndexRatio
import NLS.ZakharovShabat.SourcePsiOriginalJacobianOffDiagonal

import NLS.ZakharovShabat.SourcePsiOriginalNormLimit

/-!
# The actual original diagonal contour error

The retained diagonal difference is exactly the original contour integral
of the index-multiplier error. Original disk separation and Lemma 12.3
give the explicit factor 2*c*L for its two displacement terms, including
complex placed roots and collapsed gaps. One joint neighborhood provides
a common quotient bound for all row and omitted indices.
-/

noncomputable section
open Set Complex Metric NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- On the actual row gap, the multiplier error is controlled separately
by the omitted root displacement and the row's midpoint and gap displacements.
The supplied original separation constant is retained. -/
theorem SourceIsolatingNeighborhoods.original_indexRatio_gap_error_bound
    {hp : p ≠ ⊤} {hp1 : 1 < p} {V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (φ : CoeffPair p) (hφV : φ ∈ V)
    (a : Coeff p) (ha : a ∈ sourcePsiOriginalRootPlacement D)
    (n m : ℤ) (hmn : m ≠ n)
    (z : ℂ) (hz : z ∈ sourcePeriodicSegment hp hp1 φ m) :
    ‖sourcePsiOriginalIndexRatio n m a z-1‖ ≤
      c*‖a n‖/‖((n-m:ℤ):ℂ)‖ +
      c*(‖sourcePeriodicMidpointDisplacement hp hp1 φ m‖+
        ‖sourcePeriodicGapDisplacement hp hp1 φ m‖)/‖((n-m:ℤ):ℂ)‖ := by
  have hzD := hD.gap φ hφV m hz
  have hsep := hD.weighted_separation_closure n m hmn
    (displacedRoots a n) (ha n) z (subset_closure hzD)
  have hzbound : ‖z-(Real.pi:ℂ)*m‖ ≤
      ‖sourcePeriodicMidpointDisplacement hp hp1 φ m‖+
        ‖sourcePeriodicGapDisplacement hp hp1 φ m‖ := by
    have h := norm_displacedRoot_sub_gap_le hp hp1 (0:Coeff p) φ m z hz
    simpa [displacedRoots,norm_sub_rev] using h
  have habound : ‖displacedRoots a n-(Real.pi:ℂ)*n‖ ≤ ‖a n‖ := by
    simp [displacedRoots]
  have hb := sourcePsi_indexRatio_error_bound n m hmn (displacedRoots a n) z hsep.1.symm
    (‖sourcePeriodicMidpointDisplacement hp hp1 φ m‖+
      ‖sourcePeriodicGapDisplacement hp hp1 φ m‖) ‖a n‖ c hzbound habound hsep.2
  have he : sourcePsiOriginalIndexRatio n m a z-1 =
      (Real.pi:ℂ)*(((n-m:ℤ):ℂ)/(displacedRoots a n-z)-(Real.pi:ℂ)⁻¹) := by
    unfold sourcePsiOriginalIndexRatio
    have hpi : (Real.pi:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    field_simp [hpi]
  rw [he,norm_mul,Complex.norm_real,Real.norm_of_nonneg Real.pi_pos.le]
  apply (mul_le_mul_of_nonneg_left hb Real.pi_pos.le).trans_eq
  field_simp
  ring

/-- An analytic numerator over the standard root is integrable on its
original enclosing circle, including when the gap is collapsed. -/
theorem SourceCriticalRootPeriodCircle.standardRoot_quotient_circleIntegrable
    {hp : p ≠ ⊤} {hp1 : 1 < p} {φ : CoeffPair p} {m : ℤ}
    (P : SourceCriticalRootPeriodCircle hp hp1 φ m) (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (closedBall (P.center:ℂ) P.radius)) :
    CircleIntegrable (fun z => f z/sourceStandardRoot hp hp1 φ m z)
      (P.center:ℂ) P.radius := by
  have hinv : ContinuousOn (fun z => (sourceStandardRoot hp hp1 φ m z)⁻¹)
      (sphere (P.center:ℂ) P.radius) := by
    intro z hz
    exact (sourceStandardRoot_inv_analyticAt hp hp1 φ m z
      (P.sphere_subset_rootDomain hz m)).continuousAt.continuousWithinAt
  have hcont : ContinuousOn (fun z => f z*(sourceStandardRoot hp hp1 φ m z)⁻¹)
      (sphere (P.center:ℂ) P.radius) := (hf.continuousOn.mono sphere_subset_closedBall).mul hinv
  simpa only [div_eq_mul_inv] using hcont.circleIntegrable P.radius_pos.le

/-- The original index multiplier is analytic near the filled row disk. -/
theorem SourceIsolatingNeighborhoods.original_indexRatio_analyticOnNhd
    {hp : p ≠ ⊤} {hp1 : 1 < p} {V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (a : Coeff p) (ha : a ∈ sourcePsiOriginalRootPlacement D)
    (n m : ℤ) (hmn : m ≠ n) (d r : ℝ) (hr : 0 < r) (he : D m = ball (d:ℂ) r) :
    AnalyticOnNhd ℂ (sourcePsiOriginalIndexRatio n m a) (closedBall (d:ℂ) r) := by
  intro z hz
  exact analyticAt_const.div (analyticAt_const.sub analyticAt_id)
    (sub_ne_zero.mpr (hD.originalRootPlacement_avoids_closedBall a ha m n hmn.symm d r hr he z hz).symm)

/-- The retained diagonal error is exactly the contour of the multiplier
error, with the same normalization as both original Jacobians. -/
theorem SourceLemma12_4Data.originalJacobian_diagonalDifference_contour
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (H : SourceLemma12_4Data hp hp1 W)
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (φ : CoeffPair p) (hφW : φ ∈ W) (hφV : φ ∈ V)
    (hφ : IsRealType (CoeffPair.toMax p φ))
    (a : Coeff p) (ha : a ∈ sourcePsiOriginalRootPlacement D)
    (n m : ℤ) (hmn : m ≠ n) (d r : ℝ) (hr : 0 < r) (he : D m = ball (d:ℂ) r) :
    sourcePsiOriginalJacobianEntry hp hp1 n m m a φ-
      (sourcePsiOriginalLimitOperator hp hp1 a φ (lp.single p m 1)) m =
      (I/(Real.pi:ℂ))*(∮ z in C((d:ℂ),r),
        (sourcePsiOriginalIndexRatio n m a z-1)*
          sourceSingleRootQuotientJointProduct hp hp1 m (z,(a,φ))/sourceStandardRoot hp hp1 φ m z) := by
  let P := hD.periodCircle φ hφV m d r hr he
  let q : ℂ → ℂ := fun z => sourceSingleRootQuotientJointProduct hp hp1 m (z,(a,φ))
  have hqa : AnalyticOnNhd ℂ q (closedBall (P.center:ℂ) P.radius) :=
    fun z hz => H.previous.quotients.spectral φ hφW a m z (P.closedBall_subset_omittedDomain hz)
  have hratio := hD.original_indexRatio_analyticOnNhd a ha n m hmn d r hr he
  have hFa : AnalyticOnNhd ℂ (fun z => sourcePsiOriginalIndexRatio n m a z*q z)
      (closedBall (P.center:ℂ) P.radius) := fun z hz => (hratio z hz).mul (hqa z hz)
  have hJn : sourcePsiOriginalJacobianEntry hp hp1 n m m a φ =
      (I/(Real.pi:ℂ))*(∮ z in C((d:ℂ),r),
        sourcePsiOriginalIndexRatio n m a z*q z/sourceStandardRoot hp hp1 φ m z) := by
    rw [H.originalJacobianEntry_diagonal_contour hD φ hφW hφV hφ n m hmn a ha d r hr he,
      ← circleIntegral.integral_const_mul]
    apply circleIntegral.integral_congr hr.le
    intro z hz
    dsimp only
    rw [← sourcePsiGapRegularFactor_eq_zeta hp hp1 n m hmn a φ z
      (P.closedBall_subset_omittedDomain (sphere_subset_closedBall hz))
      (hD.originalRootPlacement_avoids_sphere a ha m n d r hr he z hz)]
    dsimp only [sourcePsiGapRegularFactor,sourcePsiOriginalIndexRatio,q]
    have hpi : (Real.pi:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    field_simp [hpi]
  rw [hJn,H.originalLimitOperator_entry hD φ hφW hφV hφ a ha m m d r hr he,
    hD.originalLimitMatrixEntry_diagonal_contour φ a ha m d r hr he,← mul_sub]
  congr 1
  have hsub := circleIntegral.integral_sub
    (P.standardRoot_quotient_circleIntegrable _ hFa) (P.standardRoot_quotient_circleIntegrable q hqa)
  dsimp only [P,SourceIsolatingNeighborhoods.periodCircle,q] at hsub
  dsimp only [q]
  rw [← hsub]
  apply circleIntegral.integral_congr hr.le
  intro z _
  dsimp only [q]
  ring

/-- The diagonal error has an explicit bound by the omitted root displacement
and the row's midpoint/gap displacements. Roots may be complex within the
original disks. The constant is twice the original separation constant
times the single-quotient bound. -/
theorem SourceLemma12_4Data.originalJacobian_diagonalDifference_bound
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (H : SourceLemma12_4Data hp hp1 W)
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (φ : CoeffPair p) (hφW : φ ∈ W) (hφV : φ ∈ V)
    (hφ : IsRealType (CoeffPair.toMax p φ))
    (a : Coeff p) (ha : a ∈ sourcePsiOriginalRootPlacement D)
    (n m : ℤ) (hmn : m ≠ n) (L : ℝ)
    (hq : ∀ z ∈ D m, ‖sourceSingleRootQuotientJointProduct hp hp1 m (z,(a,φ))‖ ≤ L) :
    ‖sourcePsiOriginalJacobianEntry hp hp1 n m m a φ-
      (sourcePsiOriginalLimitOperator hp hp1 a φ (lp.single p m 1)) m‖ ≤
      (2*c*L)*(‖a n‖+‖sourcePeriodicMidpointDisplacement hp hp1 φ m‖+
        ‖sourcePeriodicGapDisplacement hp hp1 φ m‖)/‖((n-m:ℤ):ℂ)‖ := by
  obtain ⟨d,r,hr,he⟩ := hD.discs m
  let P := hD.periodCircle φ hφV m d r hr he
  let f : ℂ → ℂ := fun z => (sourcePsiOriginalIndexRatio n m a z-1)*
    sourceSingleRootQuotientJointProduct hp hp1 m (z,(a,φ))
  have hf : AnalyticOnNhd ℂ f (closedBall (P.center:ℂ) P.radius) := by
    intro z hz
    exact ((hD.original_indexRatio_analyticOnNhd a ha n m hmn d r hr he z hz).sub
      analyticAt_const).mul (H.previous.quotients.spectral φ hφW a m z
        (P.closedBall_subset_omittedDomain hz))
  obtain ⟨z,hz,_,hb,_⟩ := P.lemma12_3_circle f hf
  let J := ∮ z in C((d:ℂ),r), f z/sourceStandardRoot hp hp1 φ m z
  have hscaled : ‖(I/(Real.pi:ℂ))*J‖ ≤ 2*‖f z‖ := by
    have he : ‖(I/(Real.pi:ℂ))*J‖ = 2*‖(2*(Real.pi:ℂ))⁻¹*J‖ := by
      simp only [norm_mul,norm_div,norm_inv,Complex.norm_I,Complex.norm_ofNat,
        Complex.norm_real,Real.norm_of_nonneg Real.pi_pos.le]
      field_simp
    rw [he]
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 2)
    simpa only [PiecewiseC1Loop.integral_circle,P,SourceIsolatingNeighborhoods.periodCircle,J] using hb
  have hc : 0 ≤ c := zero_le_one.trans hD.one_le
  have hpoint := mul_le_mul
    (hD.original_indexRatio_gap_error_bound φ hφV a ha n m hmn z hz)
    (hq z (hD.gap φ hφV m hz)) (norm_nonneg _) (by positivity)
  have hfbound : ‖f z‖ ≤
      (c*‖a n‖/‖((n-m:ℤ):ℂ)‖+
        c*(‖sourcePeriodicMidpointDisplacement hp hp1 φ m‖+
          ‖sourcePeriodicGapDisplacement hp hp1 φ m‖)/‖((n-m:ℤ):ℂ)‖)*L := by
    simpa only [f,norm_mul] using hpoint
  rw [H.originalJacobian_diagonalDifference_contour hD φ hφW hφV hφ a ha n m hmn d r hr he]
  exact hscaled.trans ((mul_le_mul_of_nonneg_left hfbound (by norm_num : (0:ℝ) ≤ 2)).trans_eq (by ring))

/-- One joint neighborhood and one constant bound all retained diagonal
errors. The two displacement sequences and omitted root coordinate remain
explicit, so local boundedness is not confused with uniform tail decay. -/
theorem SourceLemma12_4Data.originalJacobian_diagonalDifference_locally_bounded
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (H : SourceLemma12_4Data hp hp1 W) (hW : IsOpen W)
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c) (hV : IsOpen V)
    (φ : CoeffPair p) (hφW : φ ∈ W) (hφV : φ ∈ V) (a : Coeff p) :
    ∃ U : Set (Coeff p × CoeffPair p), IsOpen U ∧ (a,φ) ∈ U ∧
      U ⊆ univ ×ˢ (W ∩ V) ∧ ∃ K : ℝ, 0 ≤ K ∧
      ∀ t ∈ U, IsRealType (CoeffPair.toMax p t.2) →
        t.1 ∈ sourcePsiOriginalRootPlacement D →
        ∀ n m : ℤ, m ≠ n →
          ‖sourcePsiOriginalJacobianEntry hp hp1 n m m t.1 t.2-
            (sourcePsiOriginalLimitOperator hp hp1 t.1 t.2 (lp.single p m 1)) m‖ ≤
          K*(‖t.1 n‖+‖sourcePeriodicMidpointDisplacement hp hp1 t.2 m‖+
            ‖sourcePeriodicGapDisplacement hp hp1 t.2 m‖)/‖((n-m:ℤ):ℂ)‖ := by
  obtain ⟨Uq,hUq,hbase,C,hC,hbound⟩ :=
    H.previous.quotients.local_allDisk_quotient_errorBound hD hV φ hφW hφV a
  let U := Uq ∩ (univ ×ˢ (W ∩ V))
  have hc : 0 ≤ c := zero_le_one.trans hD.one_le
  refine ⟨U,hUq.inter (isOpen_univ.prod (hW.inter hV)),⟨hbase,mem_univ _,hφW,hφV⟩,
    (fun _ ht => ht.2),2*c*(C+1),by positivity,?_⟩
  intro t ht hreal ha n m hmn
  obtain ⟨E,hE,_,hEq⟩ := hbound t ht.1
  apply H.originalJacobian_diagonalDifference_bound hD t.2 ht.2.2.1 ht.2.2.2 hreal t.1 ha n m hmn (C+1)
  intro z hz
  have hb := (hEq m z hz).trans ((lp.norm_apply_le_norm (zero_lt_one.trans hp1).ne' E m).trans hE)
  calc
    ‖sourceSingleRootQuotientJointProduct hp hp1 m (z,t)‖ ≤
        ‖sourceSingleRootQuotientJointProduct hp hp1 m (z,t)-1‖+‖(1:ℂ)‖ :=
      norm_le_norm_sub_add _ _
    _ ≤ C+1 := by simpa only [norm_one] using add_le_add hb (le_refl ‖(1:ℂ)‖)

end NLS.ZakharovShabat

noncomputable section
open Set Complex Metric NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The normalized standard-root period has norm at most twice the
numerator's bound on the actual gap. -/
theorem SourceCriticalRootPeriodCircle.norm_standardRoot_period_le
    {hp : p ≠ ⊤} {hp1 : 1 < p} {φ : CoeffPair p} {m : ℤ}
    (P : SourceCriticalRootPeriodCircle hp hp1 φ m) (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (closedBall (P.center:ℂ) P.radius))
    (B : ℝ) (hB : ∀ z ∈ sourcePeriodicSegment hp hp1 φ m, ‖f z‖ ≤ B) :
    ‖(I/(Real.pi:ℂ))*(∮ z in C((P.center:ℂ),P.radius),
      f z/sourceStandardRoot hp hp1 φ m z)‖ ≤ 2*B := by
  obtain ⟨z,hz,_,hb,_⟩ := P.lemma12_3_circle f hf
  let J := ∮ z in C((P.center:ℂ),P.radius), f z/sourceStandardRoot hp hp1 φ m z
  have he : ‖(I/(Real.pi:ℂ))*J‖ = 2*‖(2*(Real.pi:ℂ))⁻¹*J‖ := by
    simp only [norm_mul,norm_div,norm_inv,Complex.norm_I,Complex.norm_ofNat,
      Complex.norm_real,Real.norm_of_nonneg Real.pi_pos.le]
    field_simp
  change ‖(I/(Real.pi:ℂ))*J‖ ≤ _
  rw [he]
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 2)
  have hb' : ‖(2*(Real.pi:ℂ))⁻¹*J‖ ≤ ‖f z‖ := by
    simpa only [PiecewiseC1Loop.integral_circle,J] using hb
  exact hb'.trans (hB z hz)

/-- Original disk separation controls a normalized Cauchy period by
the numerator's gap bound, with the explicit constant 2*c. -/
theorem SourceIsolatingNeighborhoods.original_cauchyPeriod_bound
    {hp : p ≠ ⊤} {hp1 : 1 < p} {V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (φ : CoeffPair p) (hφV : φ ∈ V)
    (a : Coeff p) (ha : a ∈ sourcePsiOriginalRootPlacement D)
    (n m : ℤ) (hmn : m ≠ n) (d r : ℝ) (hr : 0 < r) (he : D m = ball (d:ℂ) r)
    (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f (closedBall (d:ℂ) r))
    (B : ℝ) (hB : ∀ z ∈ sourcePeriodicSegment hp hp1 φ m, ‖f z‖ ≤ B) :
    ‖(I/(Real.pi:ℂ))*(∮ z in C((d:ℂ),r),
      (f z/(displacedRoots a n-z))/sourceStandardRoot hp hp1 φ m z)‖ ≤
      (2*c*B)/‖((n-m:ℤ):ℂ)‖ := by
  let P := hD.periodCircle φ hφV m d r hr he
  let g : ℂ → ℂ := fun z => f z/(displacedRoots a n-z)
  have hg : AnalyticOnNhd ℂ g (closedBall (P.center:ℂ) P.radius) := by
    intro z hz
    exact (hf z hz).div (analyticAt_const.sub analyticAt_id)
      (sub_ne_zero.mpr (hD.originalRootPlacement_avoids_closedBall a ha m n hmn.symm d r hr he z hz).symm)
  have hb (z : ℂ) (hz : z ∈ sourcePeriodicSegment hp hp1 φ m) :
      ‖g z‖ ≤ c*B/‖((n-m:ℤ):ℂ)‖ := by
    have hsep := hD.weighted_separation_closure n m hmn (displacedRoots a n) (ha n)
      z (subset_closure (hD.gap φ hφV m hz))
    have hd : 0 < ‖displacedRoots a n-z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hsep.1.symm)
    have hnm : 0 < ‖((n-m:ℤ):ℂ)‖ := norm_pos_iff.mpr (by exact_mod_cast sub_ne_zero.mpr hmn.symm)
    have hinv : 1/‖displacedRoots a n-z‖ ≤ c/‖((n-m:ℤ):ℂ)‖ := by
      apply (div_le_div_iff₀ hd hnm).mpr
      simpa only [one_mul] using (div_le_iff₀ hd).mp hsep.2
    have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB z hz)
    calc
      ‖g z‖ = ‖f z‖/‖displacedRoots a n-z‖ := norm_div _ _
      _ ≤ B/‖displacedRoots a n-z‖ := div_le_div_of_nonneg_right (hB z hz) hd.le
      _ = B*(1/‖displacedRoots a n-z‖) := by ring
      _ ≤ B*(c/‖((n-m:ℤ):ℂ)‖) := mul_le_mul_of_nonneg_left hinv hB0
      _ = _ := by ring
  have hb' := P.norm_standardRoot_period_le g hg _ hb
  exact hb'.trans_eq (by ring)

/-- The two normalized contour errors have separate bounds with one
constant. These bounds retain the root term and the row's two lp
displacements before any near/far estimate is made. -/
theorem SourceLemma12_4Data.originalJacobian_diagonalErrorTerms_bound
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (H : SourceLemma12_4Data hp hp1 W)
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (φ : CoeffPair p) (hφW : φ ∈ W) (hφV : φ ∈ V)
    (a : Coeff p) (ha : a ∈ sourcePsiOriginalRootPlacement D)
    (n m : ℤ) (hmn : m ≠ n) (d r : ℝ) (hr : 0 < r) (he : D m = ball (d:ℂ) r)
    (L : ℝ) (hq : ∀ z ∈ D m, ‖sourceSingleRootQuotientJointProduct hp hp1 m (z,(a,φ))‖ ≤ L) :
    ‖(I/(Real.pi:ℂ))*(∮ z in C((d:ℂ),r),
      (((Real.pi:ℂ)*n-displacedRoots a n)*sourceSingleRootQuotientJointProduct hp hp1 m (z,(a,φ)) /
        (displacedRoots a n-z))/sourceStandardRoot hp hp1 φ m z)‖ ≤
        (2*c*L)*‖a n‖/‖((n-m:ℤ):ℂ)‖ ∧
    ‖(I/(Real.pi:ℂ))*(∮ z in C((d:ℂ),r),
      ((z-(Real.pi:ℂ)*m)*sourceSingleRootQuotientJointProduct hp hp1 m (z,(a,φ)) /
        (displacedRoots a n-z))/sourceStandardRoot hp hp1 φ m z)‖ ≤
        (2*c*L)*(‖sourcePeriodicMidpointDisplacement hp hp1 φ m‖+
          ‖sourcePeriodicGapDisplacement hp hp1 φ m‖)/‖((n-m:ℤ):ℂ)‖ := by
  let P := hD.periodCircle φ hφV m d r hr he
  let q : ℂ → ℂ := fun z => sourceSingleRootQuotientJointProduct hp hp1 m (z,(a,φ))
  have hqa : AnalyticOnNhd ℂ q (closedBall (d:ℂ) r) :=
    fun z hz => H.previous.quotients.spectral φ hφW a m z (P.closedBall_subset_omittedDomain hz)
  constructor
  · have hf : AnalyticOnNhd ℂ (fun z => ((Real.pi:ℂ)*n-displacedRoots a n)*q z)
        (closedBall (d:ℂ) r) := fun z hz => analyticAt_const.mul (hqa z hz)
    have hb (z : ℂ) (hz : z ∈ sourcePeriodicSegment hp hp1 φ m) :
        ‖((Real.pi:ℂ)*n-displacedRoots a n)*q z‖ ≤ ‖a n‖*L := by
      have hh := mul_le_mul_of_nonneg_left (hq z (hD.gap φ hφV m hz)) (norm_nonneg (a n))
      simpa [q,norm_mul,displacedRoots] using hh
    exact (hD.original_cauchyPeriod_bound φ hφV a ha n m hmn d r hr he _ hf _ hb).trans_eq (by ring)
  · have hf : AnalyticOnNhd ℂ (fun z => (z-(Real.pi:ℂ)*m)*q z)
        (closedBall (d:ℂ) r) := fun z hz => (analyticAt_id.sub analyticAt_const).mul (hqa z hz)
    have hb (z : ℂ) (hz : z ∈ sourcePeriodicSegment hp hp1 φ m) :
        ‖(z-(Real.pi:ℂ)*m)*q z‖ ≤
          (‖sourcePeriodicMidpointDisplacement hp hp1 φ m‖+
            ‖sourcePeriodicGapDisplacement hp hp1 φ m‖)*L := by
      have hzbound : ‖z-(Real.pi:ℂ)*m‖ ≤
          ‖sourcePeriodicMidpointDisplacement hp hp1 φ m‖+
            ‖sourcePeriodicGapDisplacement hp hp1 φ m‖ := by
        simpa [displacedRoots,norm_sub_rev] using norm_displacedRoot_sub_gap_le hp hp1 (0:Coeff p) φ m z hz
      simpa only [norm_mul,q] using mul_le_mul hzbound (hq z (hD.gap φ hφV m hz))
        (norm_nonneg _) (by positivity)
    exact (hD.original_cauchyPeriod_bound φ hφV a ha n m hmn d r hr he _ hf _ hb).trans_eq (by ring)

end NLS.ZakharovShabat
