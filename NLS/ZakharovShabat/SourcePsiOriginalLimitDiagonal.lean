import NLS.ZakharovShabat.SourcePsiOriginalLimitEntries
import NLS.ZakharovShabat.SourcePsiOriginalZetaRegular

/-!
# The diagonal in equation (2.29) on the original domain

The diagonal Q* entry is twice the single-root quotient at an actual
point of the selected real gap. Placed roots make that quotient nonzero,
including at collapsed gaps. Original disk quotient-error majorants give
a locally bounded lp correction to the constant diagonal 2.
-/

noncomputable section
open Set Complex Metric Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Cancel the diagonal root factor on the original contour. -/
theorem SourceIsolatingNeighborhoods.originalLimitMatrixEntry_diagonal_contour
    {hp : p ≠ ⊤} {hp1 : 1 < p} {V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (φ : CoeffPair p) (a : Coeff p) (ha : a ∈ sourcePsiOriginalRootPlacement D)
    (m : ℤ) (d r : ℝ) (hr : 0 < r) (he : D m = ball (d:ℂ) r) :
    sourcePsiLimitMatrixEntry hp hp1 m m a φ (d:ℂ) r =
      (I/(Real.pi:ℂ))*(∮ z in C((d:ℂ),r),
        sourceSingleRootQuotientJointProduct hp hp1 m (z,(a,φ))/sourceStandardRoot hp hp1 φ m z) := by
  have heq : EqOn (sourcePsiLimitMatrixIntegrand hp hp1 m m a φ)
      (fun z => I*(sourceSingleRootQuotientJointProduct hp hp1 m (z,(a,φ))/
        sourceStandardRoot hp hp1 φ m z)) (sphere (d:ℂ) r) := by
    intro z hz
    unfold sourcePsiLimitMatrixIntegrand
    rw [div_self (sub_ne_zero.mpr (hD.originalRootPlacement_avoids_sphere a ha m m d r hr he z hz).symm),one_mul]
    ring
  unfold sourcePsiLimitMatrixEntry
  rw [circleIntegral.integral_congr hr.le heq,circleIntegral.integral_const_mul]
  ring

/-- One actual gap point computes each diagonal entry, even for collapsed gaps. -/
theorem SourceLemma12_4Data.originalLimitOperator_diagonal_meanValue
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (H : SourceLemma12_4Data hp hp1 W)
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (φ : CoeffPair p) (hφW : φ ∈ W) (hφV : φ ∈ V)
    (hφ : IsRealType (CoeffPair.toMax p φ))
    (a : Coeff p) (ha : a ∈ sourcePsiOriginalRootPlacement D)
    (haReal : ∀ k : ℤ, (a k).im = 0) (m : ℤ) :
    ∃ μ ∈ sourcePeriodicSegment hp hp1 φ m,
      (sourcePsiOriginalLimitOperator hp hp1 a φ (lp.single p m 1)) m =
        2*sourceSingleRootQuotientJointProduct hp hp1 m (μ,(a,φ)) := by
  obtain ⟨d,r,hr,he⟩ := hD.discs m
  let P := hD.periodCircle φ hφV m d r hr he
  let q : ℂ → ℂ := fun z => sourceSingleRootQuotientJointProduct hp hp1 m (z,(a,φ))
  have hqa : AnalyticOnNhd ℂ q (closedBall (P.center:ℂ) P.radius) :=
    fun z hz => H.previous.quotients.spectral φ hφW a m z (P.closedBall_subset_omittedDomain hz)
  have hqr : ∀ z ∈ sourcePeriodicSegment hp hp1 φ m, (q z).im = 0 := by
    intro z hz
    have hzReal : (z.re:ℂ) = z := by
      apply Complex.ext
      · rfl
      · simpa using (sourcePeriodicSegment_im_eq_zero_of_realType hp hp1 φ hφ m z hz).symm
    have hdom := P.closedBall_subset_omittedDomain (ball_subset_closedBall (P.gap hz))
    have hh := sourceSingleRootQuotientJointProduct_im_eq_zero_of_real_roots hp hp1 φ hφ a
      (fun k => by simp [displacedRoots,haReal]) m z.re (hzReal ▸ hdom)
    simpa only [q,hzReal] using hh
  obtain ⟨_,_,_,_,hmean⟩ := P.lemma12_3_circle q hqa
  obtain ⟨μ,hμ,hvalue⟩ := hmean hqr
  let J := ∮ z in C((d:ℂ),r), q z/sourceStandardRoot hp hp1 φ m z
  let K : ℂ := 2*(Real.pi:ℂ)*I
  have hK : K ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) I_ne_zero
  have hv : K⁻¹*J = -q μ := by
    simpa only [PiecewiseC1Loop.normalizedIntegral,PiecewiseC1Loop.integral_circle,
      P,SourceIsolatingNeighborhoods.periodCircle,K,J] using hvalue
  have hJ : J = K*(-q μ) := by
    simpa [mul_assoc,hK] using congrArg (fun z : ℂ => K*z) hv
  refine ⟨μ,hμ,?_⟩
  rw [H.originalLimitOperator_entry hD φ hφW hφV hφ a ha m m d r hr he,
    hD.originalLimitMatrixEntry_diagonal_contour φ a ha m d r hr he]
  change (I/(Real.pi:ℂ))*J = 2*q μ
  rw [hJ]
  dsimp only [K]
  field_simp
  simp [I_sq]

/-- No original real-domain diagonal entry vanishes. -/
theorem SourceLemma12_4Data.originalLimitOperator_diagonal_ne_zero
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (H : SourceLemma12_4Data hp hp1 W)
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (φ : CoeffPair p) (hφW : φ ∈ W) (hφV : φ ∈ V)
    (hφ : IsRealType (CoeffPair.toMax p φ))
    (a : Coeff p) (ha : a ∈ sourcePsiOriginalRootPlacement D)
    (haReal : ∀ k : ℤ, (a k).im = 0) (m : ℤ) :
    (sourcePsiOriginalLimitOperator hp hp1 a φ (lp.single p m 1)) m ≠ 0 := by
  obtain ⟨μ,hμ,he⟩ := H.originalLimitOperator_diagonal_meanValue hD φ hφW hφV hφ a ha haReal m
  have hzD := hD.gap φ hφV m hμ
  have hother (k : ℤ) (hkm : k ≠ m) : μ ≠ displacedRoots a k := by
    intro heq
    exact Set.disjoint_left.mp (hD.disjoint m k hkm.symm) hzD (heq ▸ ha k)
  have hdom : μ ∈ sourceStandardRootOmittedDomain hp hp1 φ m := by
    intro k hkm hμk
    exact Set.disjoint_left.mp (hD.disjoint m k hkm.symm) hzD (hD.gap φ hφV k hμk)
  rw [he]
  exact mul_ne_zero (by norm_num)
    (sourceSingleRootQuotientJointProduct_ne_zero_of_off_other hp hp1 m μ a φ hother hdom)

/-- A locally bounded lp correction gives the full original diagonal as 2+lp. -/
theorem SourceLemma12_4Data.originalLimitOperator_diagonal_lp
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (H : SourceLemma12_4Data hp hp1 W) (hW : IsOpen W)
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c) (hV : IsOpen V)
    (φ : CoeffPair p) (hφW : φ ∈ W) (hφV : φ ∈ V) (a₀ : Coeff p) :
    ∃ U : Set (Coeff p × CoeffPair p), IsOpen U ∧ (a₀,φ) ∈ U ∧ U ⊆ univ ×ˢ (W ∩ V) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ U, IsRealType (CoeffPair.toMax p t.2) →
        t.1 ∈ sourcePsiOriginalRootPlacement D → (∀ k : ℤ, (t.1 k).im = 0) →
        ∃ S : Coeff p, ‖S‖ ≤ C ∧ ∀ m : ℤ,
          (sourcePsiOriginalLimitOperator hp hp1 t.1 t.2 (lp.single p m 1)) m = 2+S m := by
  classical
  obtain ⟨Uq,hUq,hbase,C,hC,hb⟩ :=
    H.previous.quotients.local_allDisk_quotient_errorBound hD hV φ hφW hφV a₀
  let U := Uq ∩ (univ ×ˢ (W ∩ V))
  refine ⟨U,hUq.inter (isOpen_univ.prod (hW.inter hV)),⟨hbase,mem_univ _,hφW,hφV⟩,
    (fun _ ht => ht.2),2*C,by positivity,?_⟩
  intro t ht hreal ha haReal
  obtain ⟨E,hE,_,hEq⟩ := hb t ht.1
  have hmean (m : ℤ) := H.originalLimitOperator_diagonal_meanValue hD t.2 ht.2.2.1 ht.2.2.2
    hreal t.1 ha haReal m
  choose μ hμ hvalue using hmean
  let s : ℤ → ℂ := fun m => 2*(sourceSingleRootQuotientJointProduct hp hp1 m (μ m,(t.1,t.2))-1)
  let A : Coeff p := (2:ℂ) • E
  have hdom (m : ℤ) : ‖s m‖ ≤ ‖A m‖ := by
    change ‖(2:ℂ)*(sourceSingleRootQuotientJointProduct hp hp1 m (μ m,(t.1,t.2))-1)‖ ≤ ‖(2:ℂ)*E m‖
    rw [norm_mul,norm_mul]
    exact mul_le_mul_of_nonneg_left (hEq m (μ m) (hD.gap t.2 ht.2.2.2 m (hμ m))) (norm_nonneg _)
  let S : Coeff p := ⟨s,(lp.memℓp A).mono' hdom⟩
  refine ⟨S,?_,?_⟩
  · apply (lp.norm_mono (zero_lt_one.trans hp1).ne' hdom).trans
    simpa only [A,norm_smul,Complex.norm_ofNat] using mul_le_mul_of_nonneg_left hE (by norm_num : (0:ℝ)≤2)
  · intro m
    rw [hvalue m]
    change 2*sourceSingleRootQuotientJointProduct hp hp1 m (μ m,(t.1,t.2)) = 2+s m
    dsimp only [s]
    ring

end NLS.ZakharovShabat
