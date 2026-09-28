import NLS.ZakharovShabat.SourcePsiLimitQuotientUniform
import NLS.ZakharovShabat.SourcePsiLimitRatioUniform
import Mathlib.Topology.ContinuousMap.Algebra

/-!
# Uniform convergence of the candidate Q* integrand

The deleted-index ratio and the omitted-coordinate quotient converge
uniformly on fixed valid discs. Multiplication is continuous for
complex-valued continuous functions on a compact contour, allowing the
two limits to be combined before taking the circle integral.
-/

noncomputable section
open Set Filter Topology Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Products preserve uniform convergence on a compact set when the
approximating functions are eventually continuous there. -/
theorem tendstoUniformlyOn_mul_of_isCompact
    {Y ι : Type*} [TopologicalSpace Y]
    {K : Set Y} (hK : IsCompact K) {l : Filter ι}
    {f g : ι → Y → ℂ} {f₀ g₀ : Y → ℂ}
    (hf₀ : ContinuousOn f₀ K) (hg₀ : ContinuousOn g₀ K)
    (hfc : ∀ᶠ i in l, ContinuousOn (f i) K)
    (hgc : ∀ᶠ i in l, ContinuousOn (g i) K)
    (hf : TendstoUniformlyOn f f₀ l K)
    (hg : TendstoUniformlyOn g g₀ l K) :
    TendstoUniformlyOn (fun i y => f i y * g i y)
      (fun y => f₀ y * g₀ y) l K := by
  classical
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let f' : ι → Y → ℂ := fun i y =>
    if h : ContinuousOn (f i) K then f i y else f₀ y
  let g' : ι → Y → ℂ := fun i y =>
    if h : ContinuousOn (g i) K then g i y else g₀ y
  have hfc' (i : ι) : ContinuousOn (f' i) K := by
    dsimp [f']
    split_ifs with h
    · exact h
    · exact hf₀
  have hgc' (i : ι) : ContinuousOn (g' i) K := by
    dsimp [g']
    split_ifs with h
    · exact h
    · exact hg₀
  have hfeq : ∀ᶠ i in l, EqOn (f i) (f' i) K := by
    filter_upwards [hfc] with i hi y _
    simp [f',hi]
  have hgeq : ∀ᶠ i in l, EqOn (g i) (g' i) K := by
    filter_upwards [hgc] with i hi y _
    simp [g',hi]
  have hf' : TendstoUniformlyOn f' f₀ l K := hf.congr hfeq
  have hg' : TendstoUniformlyOn g' g₀ l K := hg.congr hgeq
  let F (i : ι) : C(K,ℂ) := ⟨_, (hfc' i).domRestrict⟩
  let G (i : ι) : C(K,ℂ) := ⟨_, (hgc' i).domRestrict⟩
  let F₀ : C(K,ℂ) := ⟨_, hf₀.domRestrict⟩
  let G₀ : C(K,ℂ) := ⟨_, hg₀.domRestrict⟩
  have hF : Tendsto F l (𝓝 F₀) :=
    (hf₀.tendsto_domRestrict_iff_tendstoUniformlyOn hfc').2 hf'
  have hG : Tendsto G l (𝓝 G₀) :=
    (hg₀.tendsto_domRestrict_iff_tendstoUniformlyOn hgc').2 hg'
  have hprod : Tendsto (fun i => F i * G i) l (𝓝 (F₀ * G₀)) := hF.mul hG
  have hprod' : TendstoUniformlyOn
      (fun i y => f' i y * g' i y) (fun y => f₀ y * g₀ y) l K := by
    apply ((hf₀.mul hg₀).tendsto_domRestrict_iff_tendstoUniformlyOn
      (fun i => (hfc' i).mul (hgc' i))).1
    convert hprod using 1
    · funext i
      ext y
      rfl
    · ext y
      rfl
  apply hprod'.congr
  filter_upwards [hfeq,hgeq] with i hfi hgi y hy
  change f' i y * g' i y = f i y * g i y
  rw [← hfi hy, ← hgi hy]

/-- The two moving factors in the selected-index integrand have a
uniform product limit on a fixed valid contour. -/
theorem tendstoUniformlyOn_sourcePsiQuotient_mul_ratio
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (m : ℤ) (ψ : CoeffPair p)
    (hψ : IsRealType (CoeffPair.toMax p ψ))
    (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hdisc : closedBall c R ⊆
      sourceStandardRootOmittedDomain hp hp1 ψ m)
    (a : Coeff p) :
    TendstoUniformlyOn
      (fun n : ℤ => fun z : ℂ =>
        sourceSingleRootQuotientJointProduct hp hp1 m
          (z,(Coeff.deleteCoordinate n a,ψ)) *
            sourcePsiDeletedIndexRatio n m z)
      (fun z : ℂ =>
        sourceSingleRootQuotientJointProduct hp hp1 m (z,(a,ψ)))
      (Filter.comap Int.natAbs Filter.atTop)
      (sphere c R) := by
  obtain ⟨W,_,_,hreal,hdata⟩ :=
    exists_global_source_analytic_singleRootQuotient hp hp1
  have hQcont (b : Coeff p) : ContinuousOn
      (fun z : ℂ => sourceSingleRootQuotientJointProduct hp hp1 m
        (z,(b,ψ))) (sphere c R) := by
    intro z hz
    have hzdisc : z ∈ closedBall c R :=
      sphere_subset_closedBall hz
    have ht : (z,(b,ψ)) ∈
        sourceSingleRootQuotientJointDomain hp hp1 W m :=
      ⟨hreal hψ,hdisc hzdisc⟩
    have hAna := (hdata m).2 (z,(b,ψ)) ht
    have hinc : ContinuousAt (fun w : ℂ => (w,(b,ψ))) z := by fun_prop
    exact (hAna.continuousAt.comp
      (f := fun w : ℂ => (w,(b,ψ))) hinc).continuousWithinAt
  have hQ := (tendstoUniformlyOn_sourceSingleRootQuotient_deleteCoordinate
    hp hp1 m ψ hψ c R hdisc a).mono
      sphere_subset_closedBall
  have hratio := (tendstoUniformlyOn_sourcePsiDeletedIndexRatio_anyDisc m c R hR).mono
      sphere_subset_closedBall
  have hprod := tendstoUniformlyOn_mul_of_isCompact
    (isCompact_sphere c R)
    (hQcont a) continuousOn_const
    (Filter.Eventually.of_forall fun n => hQcont (Coeff.deleteCoordinate n a))
    (eventually_continuousOn_sourcePsiDeletedIndexRatio_anyCircle m c R)
    hQ hratio
  simpa only [mul_one] using hprod

/-- The fixed rational multiplier in the candidate matrix entry is
continuous whenever its two denominators stay off the contour. -/
theorem continuousOn_sourcePsiLimitMatrixMultiplier
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (m k : ℤ) (a : Coeff p) (ψ : CoeffPair p)
    (c : ℂ) (R : ℝ)
    (hk : ∀ z ∈ sphere c R, displacedRoots a k - z ≠ 0)
    (hm : ∀ z ∈ sphere c R,
      z ∉ sourcePeriodicSegment hp hp1 ψ m) :
    ContinuousOn (fun z : ℂ =>
      ((displacedRoots a m-z)/(displacedRoots a k-z)) *
        (I / sourceStandardRoot hp hp1 ψ m z)) (sphere c R) := by
  have hstd : ContinuousOn
      (fun z : ℂ => sourceStandardRoot hp hp1 ψ m z) (sphere c R) := by
    intro z hz
    exact (sourceStandardRoot_analyticAt hp hp1 ψ m z
      (hm z hz)).continuousAt.continuousWithinAt
  exact ((continuousOn_const.sub continuousOn_id).div
    (continuousOn_const.sub continuousOn_id) hk).mul
      (continuousOn_const.div hstd
        (fun z hz => sourceStandardRoot_ne_zero_off_segment
          hp hp1 ψ m z (hm z hz)))

/-- On a fixed valid contour, the retained-entry
integrand converges uniformly to the `Q*` matrix integrand. -/
theorem tendstoUniformlyOn_sourcePsi_fullJacobianIntegrand_deletedIndex
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (m k : ℤ) (a : Coeff p) (ψ : CoeffPair p)
    (hψ : IsRealType (CoeffPair.toMax p ψ))
    (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hdisc : closedBall c R ⊆
      sourceStandardRootOmittedDomain hp hp1 ψ m)
    (hk : ∀ z ∈ sphere c R,
      displacedRoots a k - z ≠ 0)
    (hm : ∀ z ∈ sphere c R,
      z ∉ sourcePeriodicSegment hp hp1 ψ m) :
    TendstoUniformlyOn
      (fun n : ℤ => fun z : ℂ =>
        (Real.pi : ℂ) *
          (((displacedRoots (Coeff.deleteCoordinate n a) m-z) /
              (displacedRoots (Coeff.deleteCoordinate n a) k-z)) *
            ((((n-m : ℤ) : ℂ) *
              sourcePsiGapRegularFactor hp hp1 n m
                (Coeff.deleteCoordinate n a) ψ z) /
                  sourceStandardRoot hp hp1 ψ m z)))
      (sourcePsiLimitMatrixIntegrand hp hp1 m k a ψ)
      (Filter.comap Int.natAbs Filter.atTop)
      (sphere c R) := by
  let A : ℂ → ℂ := fun z =>
    ((displacedRoots a m-z)/(displacedRoots a k-z)) *
      (I / sourceStandardRoot hp hp1 ψ m z)
  have hA : ContinuousOn A (sphere c R) :=
    continuousOn_sourcePsiLimitMatrixMultiplier hp hp1 m k a ψ
      c R hk hm
  have hAunif : TendstoUniformlyOn
      (fun _n : ℤ => A) A
      (Filter.comap Int.natAbs Filter.atTop)
      (sphere c R) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [] with n z hz
    simpa only [dist_self] using hε
  have hQR := tendstoUniformlyOn_sourcePsiQuotient_mul_ratio
    hp hp1 m ψ hψ c R hR hdisc a
  obtain ⟨W,_,_,hreal,hdata⟩ :=
    exists_global_source_analytic_singleRootQuotient hp hp1
  have hQcont (b : Coeff p) : ContinuousOn
      (fun z : ℂ => sourceSingleRootQuotientJointProduct hp hp1 m
        (z,(b,ψ))) (sphere c R) := by
    intro z hz
    have hzdisc : z ∈ closedBall c R :=
      sphere_subset_closedBall hz
    have ht : (z,(b,ψ)) ∈
        sourceSingleRootQuotientJointDomain hp hp1 W m :=
      ⟨hreal hψ,hdisc hzdisc⟩
    have hAna := (hdata m).2 (z,(b,ψ)) ht
    have hinc : ContinuousAt (fun w : ℂ => (w,(b,ψ))) z := by fun_prop
    exact (hAna.continuousAt.comp
      (f := fun w : ℂ => (w,(b,ψ))) hinc).continuousWithinAt
  have hQRcont : ∀ᶠ n : ℤ in Filter.comap Int.natAbs Filter.atTop,
      ContinuousOn (fun z : ℂ =>
        sourceSingleRootQuotientJointProduct hp hp1 m
          (z,(Coeff.deleteCoordinate n a,ψ)) *
            sourcePsiDeletedIndexRatio n m z)
          (sphere c R) := by
    filter_upwards [eventually_continuousOn_sourcePsiDeletedIndexRatio_anyCircle m c R]
      with n hn
    exact (hQcont (Coeff.deleteCoordinate n a)).mul hn
  have hprod := tendstoUniformlyOn_mul_of_isCompact
    (isCompact_sphere c R)
    hA (hQcont a)
    (Filter.Eventually.of_forall fun _ => hA)
    hQRcont hAunif hQR
  have hne : ∀ᶠ n : ℤ in Filter.comap Int.natAbs Filter.atTop,
      n ≠ m ∧ n ≠ k := by
    apply eventually_comap.mpr
    apply eventually_atTop.mpr
    refine ⟨max m.natAbs k.natAbs + 1,?_⟩
    intro j hj n hn
    constructor
    · intro hnm
      subst n
      omega
    · intro hnk
      subst n
      omega
  have heq : ∀ᶠ n : ℤ in Filter.comap Int.natAbs Filter.atTop,
      EqOn
        (fun z : ℂ => A z *
          (sourceSingleRootQuotientJointProduct hp hp1 m
            (z,(Coeff.deleteCoordinate n a,ψ)) *
              sourcePsiDeletedIndexRatio n m z))
        (fun z : ℂ => (Real.pi : ℂ) *
          (((displacedRoots (Coeff.deleteCoordinate n a) m-z) /
              (displacedRoots (Coeff.deleteCoordinate n a) k-z)) *
            ((((n-m : ℤ) : ℂ) *
              sourcePsiGapRegularFactor hp hp1 n m
                (Coeff.deleteCoordinate n a) ψ z) /
                  sourceStandardRoot hp hp1 ψ m z)))
        (sphere c R) := by
    filter_upwards [hne] with n hn z _
    have hmroot : displacedRoots (Coeff.deleteCoordinate n a) m =
        displacedRoots a m := by
      simp [displacedRoots,Coeff.deleteCoordinate_apply_other n m (Ne.symm hn.1)]
    have hkroot : displacedRoots (Coeff.deleteCoordinate n a) k =
        displacedRoots a k := by
      simp [displacedRoots,Coeff.deleteCoordinate_apply_other n k (Ne.symm hn.2)]
    have hnroot : displacedRoots (Coeff.deleteCoordinate n a) n =
        (Real.pi : ℂ)*n := by
      simp [displacedRoots,Coeff.deleteCoordinate_apply_same]
    have hreg : (Real.pi : ℂ) * (((n-m : ℤ) : ℂ) *
        sourcePsiGapRegularFactor hp hp1 n m
          (Coeff.deleteCoordinate n a) ψ z) =
        (I * sourceSingleRootQuotientJointProduct hp hp1 m
          (z,(Coeff.deleteCoordinate n a,ψ))) *
            sourcePsiDeletedIndexRatio n m z := by
      dsimp only [sourcePsiGapRegularFactor,sourcePsiDeletedIndexRatio]
      rw [hnroot]
      ring
    change A z *
      (sourceSingleRootQuotientJointProduct hp hp1 m
        (z,(Coeff.deleteCoordinate n a,ψ)) *
          sourcePsiDeletedIndexRatio n m z) = _
    rw [hmroot,hkroot]
    calc
      A z *
        (sourceSingleRootQuotientJointProduct hp hp1 m
          (z,(Coeff.deleteCoordinate n a,ψ)) *
            sourcePsiDeletedIndexRatio n m z) =
        ((displacedRoots a m-z)/(displacedRoots a k-z)) *
          (((I * sourceSingleRootQuotientJointProduct hp hp1 m
            (z,(Coeff.deleteCoordinate n a,ψ))) *
              sourcePsiDeletedIndexRatio n m z) /
                sourceStandardRoot hp hp1 ψ m z) := by
          dsimp [A]
          ring
      _ = ((displacedRoots a m-z)/(displacedRoots a k-z)) *
        (((Real.pi : ℂ) * (((n-m : ℤ) : ℂ) *
          sourcePsiGapRegularFactor hp hp1 n m
            (Coeff.deleteCoordinate n a) ψ z)) /
              sourceStandardRoot hp hp1 ψ m z) := by rw [hreg]
      _ = (Real.pi : ℂ) *
        (((displacedRoots a m-z)/(displacedRoots a k-z)) *
          ((((n-m : ℤ) : ℂ) *
            sourcePsiGapRegularFactor hp hp1 n m
              (Coeff.deleteCoordinate n a) ψ z) /
                sourceStandardRoot hp hp1 ψ m z)) := by ring
  have htarget : (fun z : ℂ => A z *
      sourceSingleRootQuotientJointProduct hp hp1 m (z,(a,ψ))) =
      sourcePsiLimitMatrixIntegrand hp hp1 m k a ψ := by
    funext z
    dsimp [A,sourcePsiLimitMatrixIntegrand]
    ring
  simpa only [htarget] using hprod.congr heq

/-- The actual selected-index matrix integrand is continuous on a
fixed valid contour once the deleted index is sufficiently distant. -/
theorem eventually_continuousOn_sourcePsi_fullJacobianIntegrand_deletedIndex
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (m k : ℤ) (a : Coeff p) (ψ : CoeffPair p)
    (hψ : IsRealType (CoeffPair.toMax p ψ))
    (c : ℂ) (R : ℝ)
    (hdisc : closedBall c R ⊆
      sourceStandardRootOmittedDomain hp hp1 ψ m)
    (hk : ∀ z ∈ sphere c R,
      displacedRoots a k - z ≠ 0)
    (hm : ∀ z ∈ sphere c R,
      z ∉ sourcePeriodicSegment hp hp1 ψ m) :
    ∀ᶠ n : ℤ in Filter.comap Int.natAbs Filter.atTop,
      ContinuousOn (fun z : ℂ =>
        (Real.pi : ℂ) *
          (((displacedRoots (Coeff.deleteCoordinate n a) m-z) /
              (displacedRoots (Coeff.deleteCoordinate n a) k-z)) *
            ((((n-m : ℤ) : ℂ) *
              sourcePsiGapRegularFactor hp hp1 n m
                (Coeff.deleteCoordinate n a) ψ z) /
                  sourceStandardRoot hp hp1 ψ m z)))
        (sphere c R) := by
  obtain ⟨W,_,_,hreal,hdata⟩ :=
    exists_global_source_analytic_singleRootQuotient hp hp1
  have hfar := (tendsto_norm_freeCenter_sub_at_natAbs c).eventually_ge_atTop
    (R + 1)
  have hne : ∀ᶠ n : ℤ in Filter.comap Int.natAbs Filter.atTop,
      n ≠ k := by
    apply eventually_comap.mpr
    apply eventually_atTop.mpr
    refine ⟨k.natAbs + 1,?_⟩
    intro j hj n hn hnk
    subst n
    omega
  filter_upwards [hfar,hne] with n hnfar hnk
  have hden : ∀ z ∈ sphere c R,
      (Real.pi : ℂ) * n - z ≠ 0 := by
    intro z hz
    have hzR : ‖z-c‖ ≤ R := by
      simpa only [mem_sphere, dist_eq_norm] using le_of_eq hz
    have htri : ‖(Real.pi : ℂ) * n-c‖ ≤
        ‖(Real.pi : ℂ) * n-z‖ + ‖z-c‖ := by
      calc
        ‖(Real.pi : ℂ) * n-c‖ =
            ‖((Real.pi : ℂ) * n-z)+(z-c)‖ := by
              congr 1
              ring
        _ ≤ _ := norm_add_le _ _
    have hdenpos : 0 < ‖(Real.pi : ℂ) * n - z‖ := by linarith
    exact norm_ne_zero_iff.mp (ne_of_gt hdenpos)
  have hQ : ContinuousOn
      (fun z : ℂ => sourceSingleRootQuotientJointProduct hp hp1 m
        (z,(Coeff.deleteCoordinate n a,ψ)))
      (sphere c R) := by
    intro z hz
    have hzdisc : z ∈ closedBall c R :=
      sphere_subset_closedBall hz
    have ht : (z,(Coeff.deleteCoordinate n a,ψ)) ∈
        sourceSingleRootQuotientJointDomain hp hp1 W m :=
      ⟨hreal hψ,hdisc hzdisc⟩
    have hAna := (hdata m).2 (z,(Coeff.deleteCoordinate n a,ψ)) ht
    have hinc : ContinuousAt
        (fun w : ℂ => (w,(Coeff.deleteCoordinate n a,ψ))) z := by fun_prop
    exact (hAna.continuousAt.comp
      (f := fun w : ℂ => (w,(Coeff.deleteCoordinate n a,ψ))) hinc).continuousWithinAt
  have hnroot : displacedRoots (Coeff.deleteCoordinate n a) n =
      (Real.pi : ℂ) * n := by
    simp [displacedRoots,Coeff.deleteCoordinate_apply_same]
  have hregular : ContinuousOn
      (sourcePsiGapRegularFactor hp hp1 n m
        (Coeff.deleteCoordinate n a) ψ)
      (sphere c R) := by
    change ContinuousOn (fun z : ℂ =>
      (I * sourceSingleRootQuotientJointProduct hp hp1 m
        (z,(Coeff.deleteCoordinate n a,ψ))) /
          (displacedRoots (Coeff.deleteCoordinate n a) n-z)) _
    exact (continuousOn_const.mul hQ).div
      (continuousOn_const.sub continuousOn_id)
      (by simpa only [hnroot] using hden)
  have hkroot : displacedRoots (Coeff.deleteCoordinate n a) k =
      displacedRoots a k := by
    simp [displacedRoots,Coeff.deleteCoordinate_apply_other n k (Ne.symm hnk)]
  have hrootRatio : ContinuousOn
      (fun z : ℂ =>
        (displacedRoots (Coeff.deleteCoordinate n a) m-z) /
          (displacedRoots (Coeff.deleteCoordinate n a) k-z))
      (sphere c R) :=
    (continuousOn_const.sub continuousOn_id).div
      (continuousOn_const.sub continuousOn_id)
      (by simpa only [hkroot] using hk)
  have hstd : ContinuousOn
      (fun z : ℂ => sourceStandardRoot hp hp1 ψ m z)
      (sphere c R) := by
    intro z hz
    exact (sourceStandardRoot_analyticAt hp hp1 ψ m z
      (hm z hz)).continuousAt.continuousWithinAt
  exact continuousOn_const.mul
    (hrootRatio.mul ((continuousOn_const.mul hregular).div hstd
      (fun z hz => sourceStandardRoot_ne_zero_off_segment
        hp hp1 ψ m z (hm z hz))))

/-- The full retained matrix integrand, normalized by `π`, can be
passed through a fixed valid contour integral. This is
the scalar contour limit underlying the candidate `Q*` entries. -/
theorem tendsto_circleIntegral_sourcePsi_fullJacobianIntegrand_deletedIndex
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (m k : ℤ) (a : Coeff p) (ψ : CoeffPair p)
    (hψ : IsRealType (CoeffPair.toMax p ψ))
    (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hdisc : closedBall c R ⊆
      sourceStandardRootOmittedDomain hp hp1 ψ m)
    (hk : ∀ z ∈ sphere c R,
      displacedRoots a k - z ≠ 0)
    (hm : ∀ z ∈ sphere c R,
      z ∉ sourcePeriodicSegment hp hp1 ψ m) :
    Tendsto (fun n : ℤ =>
      ∮ z in C(c,R),
        (Real.pi : ℂ) *
          (((displacedRoots (Coeff.deleteCoordinate n a) m-z) /
              (displacedRoots (Coeff.deleteCoordinate n a) k-z)) *
            ((((n-m : ℤ) : ℂ) *
              sourcePsiGapRegularFactor hp hp1 n m
                (Coeff.deleteCoordinate n a) ψ z) /
                  sourceStandardRoot hp hp1 ψ m z)))
      (Filter.comap Int.natAbs Filter.atTop)
      (𝓝 (∮ z in C(c,R),
        sourcePsiLimitMatrixIntegrand hp hp1 m k a ψ z)) := by
  exact (tendstoUniformlyOn_sourcePsi_fullJacobianIntegrand_deletedIndex
    hp hp1 m k a ψ hψ c R hR hdisc hk hm).tendsto_circleIntegral_of_continuousOn
      hR (eventually_continuousOn_sourcePsi_fullJacobianIntegrand_deletedIndex
        hp hp1 m k a ψ hψ c R hdisc hk hm)

end NLS.ZakharovShabat
