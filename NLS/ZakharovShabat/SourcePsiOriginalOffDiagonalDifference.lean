import NLS.ZakharovShabat.SourcePsiOriginalDiagonalDifference

/-!
# Original retained off-diagonal contour errors

The literal contour difference has a bound with explicit factor 2*c*K*L
and both inverse index spacings. A single lp sequence bounds every row
at each original placed-root input, including complex roots.
-/

noncomputable section
open Set Complex Metric NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Every retained off-diagonal error is the literal original contour
of the multiplier error, retaining its normalization. -/
theorem SourceLemma12_4Data.originalJacobian_offDiagonalDifference_contour
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (H : SourceLemma12_4Data hp hp1 W)
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (φ : CoeffPair p) (hφW : φ ∈ W) (hφV : φ ∈ V)
    (hφ : IsRealType (CoeffPair.toMax p φ))
    (a : Coeff p) (ha : a ∈ sourcePsiOriginalRootPlacement D)
    (n m k : ℤ) (hmn : m ≠ n) (hkn : k ≠ n) (hkm : k ≠ m)
    (d r : ℝ) (hr : 0 < r) (he : D m = ball (d:ℂ) r) :
    sourcePsiOriginalJacobianEntry hp hp1 n m k a φ-
      (sourcePsiOriginalLimitOperator hp hp1 a φ (lp.single p k 1)) m =
      (I/(Real.pi:ℂ))*(∮ z in C((d:ℂ),r),
        ((sourcePsiOriginalIndexRatio n m a z-1)*(displacedRoots a m-z)*
          sourceSingleRootQuotientJointProduct hp hp1 m (z,(a,φ))/(displacedRoots a k-z))/
            sourceStandardRoot hp hp1 φ m z) := by
  let P := hD.periodCircle φ hφV m d r hr he
  let q : ℂ → ℂ := fun z => sourceSingleRootQuotientJointProduct hp hp1 m (z,(a,φ))
  let f : ℂ → ℂ := fun z => ((displacedRoots a m-z)/(displacedRoots a k-z))*q z
  have hfa : AnalyticOnNhd ℂ f (closedBall (P.center:ℂ) P.radius) := by
    intro z hz
    exact ((analyticAt_const.sub analyticAt_id).div (analyticAt_const.sub analyticAt_id)
      (sub_ne_zero.mpr (hD.originalRootPlacement_avoids_closedBall a ha m k hkm d r hr he z hz).symm)).mul
      (H.previous.quotients.spectral φ hφW a m z (P.closedBall_subset_omittedDomain hz))
  have hga : AnalyticOnNhd ℂ (fun z => sourcePsiOriginalIndexRatio n m a z*f z)
      (closedBall (P.center:ℂ) P.radius) := fun z hz =>
    (hD.original_indexRatio_analyticOnNhd a ha n m hmn d r hr he z hz).mul (hfa z hz)
  have hJn : sourcePsiOriginalJacobianEntry hp hp1 n m k a φ =
      (I/(Real.pi:ℂ))*(∮ z in C((d:ℂ),r),
        sourcePsiOriginalIndexRatio n m a z*f z/sourceStandardRoot hp hp1 φ m z) := by
    rw [H.originalJacobianEntry_contour hD φ hφW hφV hφ n m k hmn hkn a ha d r hr he,
      ← circleIntegral.integral_const_mul]
    apply circleIntegral.integral_congr hr.le
    intro z hz
    dsimp only
    rw [← sourcePsiGapRegularFactor_eq_zeta hp hp1 n m hmn a φ z
      (P.closedBall_subset_omittedDomain (sphere_subset_closedBall hz))
      (hD.originalRootPlacement_avoids_sphere a ha m n d r hr he z hz)]
    dsimp only [sourcePsiGapRegularFactor,sourcePsiOriginalIndexRatio,f,q]
    have hpi : (Real.pi:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    field_simp [hpi]
  have hQs : (sourcePsiOriginalLimitOperator hp hp1 a φ (lp.single p k 1)) m =
      (I/(Real.pi:ℂ))*(∮ z in C((d:ℂ),r), f z/sourceStandardRoot hp hp1 φ m z) := by
    rw [H.originalLimitOperator_entry hD φ hφW hφV hφ a ha m k d r hr he]
    unfold sourcePsiLimitMatrixEntry
    have hInt : (∮ z in C((d:ℂ),r), sourcePsiLimitMatrixIntegrand hp hp1 m k a φ z) =
        I*(∮ z in C((d:ℂ),r), f z/sourceStandardRoot hp hp1 φ m z) := by
      rw [← circleIntegral.integral_const_mul]
      apply circleIntegral.integral_congr hr.le
      intro z _
      dsimp only [sourcePsiLimitMatrixIntegrand,f,q]
      ring
    rw [hInt]
    ring
  rw [hJn,hQs,← mul_sub]
  congr 1
  have hsub := circleIntegral.integral_sub
    (P.standardRoot_quotient_circleIntegrable _ hga) (P.standardRoot_quotient_circleIntegrable f hfa)
  dsimp only [P,SourceIsolatingNeighborhoods.periodCircle] at hsub
  rw [← hsub]
  apply circleIntegral.integral_congr hr.le
  intro z _
  dsimp only [f,q]
  ring

/-- The retained off-diagonal error has both inverse spacings, with
the positive factor 2*c*K*L made explicit. -/
theorem SourceLemma12_4Data.originalJacobian_offDiagonalDifference_bound
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (H : SourceLemma12_4Data hp hp1 W)
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (φ : CoeffPair p) (hφW : φ ∈ W) (hφV : φ ∈ V)
    (hφ : IsRealType (CoeffPair.toMax p φ))
    (a : Coeff p) (ha : a ∈ sourcePsiOriginalRootPlacement D)
    (n m k : ℤ) (hmn : m ≠ n) (hkn : k ≠ n) (hkm : k ≠ m)
    (K L : ℝ) (hK : 0 ≤ K)
    (hratio : ∀ z ∈ D m, ‖sourcePsiOriginalIndexRatio n m a z-1‖ ≤ K/‖((n-m:ℤ):ℂ)‖)
    (hq : ∀ z ∈ D m, ‖sourceSingleRootQuotientJointProduct hp hp1 m (z,(a,φ))‖ ≤ L) :
    ‖sourcePsiOriginalJacobianEntry hp hp1 n m k a φ-
      (sourcePsiOriginalLimitOperator hp hp1 a φ (lp.single p k 1)) m‖ ≤
      (2*c*K*L)*(‖a m‖+‖sourcePeriodicMidpointDisplacement hp hp1 φ m‖+
        ‖sourcePeriodicGapDisplacement hp hp1 φ m‖)/
          (‖((n-m:ℤ):ℂ)‖*‖((k-m:ℤ):ℂ)‖) := by
  obtain ⟨d,r,hr,he⟩ := hD.discs m
  let P := hD.periodCircle φ hφV m d r hr he
  let f : ℂ → ℂ := fun z => (sourcePsiOriginalIndexRatio n m a z-1)*(displacedRoots a m-z)*
    sourceSingleRootQuotientJointProduct hp hp1 m (z,(a,φ))
  let A := ‖a m‖+‖sourcePeriodicMidpointDisplacement hp hp1 φ m‖+
    ‖sourcePeriodicGapDisplacement hp hp1 φ m‖
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hf : AnalyticOnNhd ℂ f (closedBall (d:ℂ) r) := by
    intro z hz
    exact (((hD.original_indexRatio_analyticOnNhd a ha n m hmn d r hr he z hz).sub analyticAt_const).mul
      (analyticAt_const.sub analyticAt_id)).mul
      (H.previous.quotients.spectral φ hφW a m z (P.closedBall_subset_omittedDomain hz))
  have hb (z : ℂ) (hz : z ∈ sourcePeriodicSegment hp hp1 φ m) :
      ‖f z‖ ≤ (K/‖((n-m:ℤ):ℂ)‖)*A*L := by
    have hzD := hD.gap φ hφV m hz
    have hab := mul_le_mul (hratio z hzD) (norm_displacedRoot_sub_gap_le hp hp1 a φ m z hz)
      (norm_nonneg _) (by positivity)
    simpa only [f,norm_mul] using mul_le_mul hab (hq z hzD) (norm_nonneg _)
      (mul_nonneg (div_nonneg hK (norm_nonneg _)) hA)
  rw [H.originalJacobian_offDiagonalDifference_contour hD φ hφW hφV hφ a ha n m k hmn hkn hkm d r hr he]
  have hb' := hD.original_cauchyPeriod_bound φ hφV a ha k m hkm.symm d r hr he f hf _ hb
  exact hb'.trans_eq (by dsimp only [A]; ring)


/-- One actual lp row sequence controls both inverse spacings for
all retained entries at the fixed original root/source input. -/
theorem SourceLemma12_4Data.originalJacobian_offDiagonalDifference_majorant
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (H : SourceLemma12_4Data hp hp1 W)
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c) (hV : IsOpen V)
    (φ : CoeffPair p) (hφW : φ ∈ W) (hφV : φ ∈ V)
    (hφ : IsRealType (CoeffPair.toMax p φ))
    (a : Coeff p) (ha : a ∈ sourcePsiOriginalRootPlacement D) :
    ∃ B : Coeff p, ∀ n m k : ℤ, m ≠ n → k ≠ n → k ≠ m →
      ‖sourcePsiOriginalJacobianEntry hp hp1 n m k a φ-
        (sourcePsiOriginalLimitOperator hp hp1 a φ (lp.single p k 1)) m‖ ≤
        ‖B m‖/(‖((n-m:ℤ):ℂ)‖*‖((k-m:ℤ):ℂ)‖) := by
  obtain ⟨K,hK,hratio⟩ := hD.original_indexRatio_uniform_bound
  obtain ⟨U,_,hbase,Cq,hCq,hb⟩ :=
    H.previous.quotients.local_allDisk_quotient_errorBound hD hV φ hφW hφV a
  obtain ⟨E,hE,_,hEq⟩ := hb (a,φ) hbase
  have hq (m : ℤ) (z : ℂ) (hz : z ∈ D m) :
      ‖sourceSingleRootQuotientJointProduct hp hp1 m (z,(a,φ))‖ ≤ Cq+1 := by
    have hh := (hEq m z hz).trans ((lp.norm_apply_le_norm (zero_lt_one.trans hp1).ne' E m).trans hE)
    have htri := norm_le_norm_sub_add (sourceSingleRootQuotientJointProduct hp hp1 m (z,(a,φ))) (1:ℂ)
    simpa only [norm_one] using htri.trans (add_le_add hh (le_refl ‖(1:ℂ)‖))
  let A := Coeff.magnitude a+Coeff.magnitude (sourcePeriodicMidpointDisplacement hp hp1 φ)+
    Coeff.magnitude (sourcePeriodicGapDisplacement hp hp1 φ)
  have hA (m : ℤ) : ‖A m‖ = ‖a m‖+‖sourcePeriodicMidpointDisplacement hp hp1 φ m‖+
      ‖sourcePeriodicGapDisplacement hp hp1 φ m‖ := by
    simp only [A,lp.coeFn_add,Pi.add_apply,Coeff.magnitude_apply,← Complex.ofReal_add,Complex.norm_real]
    exact Real.norm_of_nonneg (by positivity)
  let C := 2*c*K*(Cq+1)
  have hc : 0 ≤ c := zero_le_one.trans hD.one_le
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨(C:ℂ) • A,?_⟩
  intro n m k hmn hkn hkm
  have hh := H.originalJacobian_offDiagonalDifference_bound hD φ hφW hφV hφ a ha
    n m k hmn hkn hkm K (Cq+1) hK (hratio a ha n m hmn) (hq m)
  simpa only [lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,norm_mul,Complex.norm_real,
    Real.norm_of_nonneg hC,hA,C] using hh

end NLS.ZakharovShabat
