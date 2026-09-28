import NLS.ZakharovShabat.SourcePsiLimitIntegrandUniform

/-!
# The Q* integrand with varying deleted root data

Lemma 12.10 uses deleted root sequences that vary with the omitted
index. Assuming these sequences converge strongly in `ℓᵖ`, the joint
analytic quotient and the explicit deleted-index ratio converge
uniformly on a fixed valid contour. The retained root ratio also
converges uniformly provided its limiting denominator avoids the
contour.
-/

noncomputable section
open Set Filter Topology Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Joint analyticity makes the quotient converge uniformly on a
fixed valid disc for any strongly converging sequence of deleted root
data, not only projections of one fixed sequence. -/
theorem tendstoUniformlyOn_sourceSingleRootQuotient_varyingDeleted
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (m : ℤ) (ψ : CoeffPair p)
    (hψ : IsRealType (CoeffPair.toMax p ψ))
    (c : ℂ) (R : ℝ)
    (hdisc : closedBall c R ⊆
      sourceStandardRootOmittedDomain hp hp1 ψ m)
    (b : ∀ n : ℤ, DeletedCoeff p n) (a : Coeff p)
    (hb : Tendsto (fun n : ℤ => (b n : Coeff p))
      (Filter.comap Int.natAbs Filter.atTop) (𝓝 a)) :
    TendstoUniformlyOn
      (fun n : ℤ => fun z : ℂ =>
        sourceSingleRootQuotientJointProduct hp hp1 m (z,((b n : Coeff p),ψ)))
      (fun z : ℂ => sourceSingleRootQuotientJointProduct hp hp1 m (z,(a,ψ)))
      (Filter.comap Int.natAbs Filter.atTop) (closedBall c R) := by
  obtain ⟨W,_,_,hreal,hdata⟩ :=
    exists_global_source_analytic_singleRootQuotient hp hp1
  apply tendstoUniformlyOn_of_joint_continuousAt_compact
    (isCompact_closedBall c R) (a := a)
    (a' := fun n : ℤ => (b n : Coeff p))
    (F := fun x : Coeff p => fun z : ℂ =>
      sourceSingleRootQuotientJointProduct hp hp1 m (z,(x,ψ)))
    ?_ hb
  intro z hz
  have ht : (z,(a,ψ)) ∈ sourceSingleRootQuotientJointDomain hp hp1 W m :=
    ⟨hreal hψ,hdisc hz⟩
  have hAna := (hdata m).2 (z,(a,ψ)) ht
  have hinc : ContinuousAt
      (fun q : Coeff p × ℂ => (q.2,(q.1,ψ))) (a,z) := by fun_prop
  exact hAna.continuousAt.comp
    (f := fun q : Coeff p × ℂ => (q.2,(q.1,ψ))) hinc

/-- The moving quotient times the deleted-index ratio converges
uniformly on a fixed valid circle. -/
theorem tendstoUniformlyOn_sourcePsiQuotient_mul_ratio_varyingDeleted
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (m : ℤ) (ψ : CoeffPair p)
    (hψ : IsRealType (CoeffPair.toMax p ψ))
    (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hdisc : closedBall c R ⊆
      sourceStandardRootOmittedDomain hp hp1 ψ m)
    (b : ∀ n : ℤ, DeletedCoeff p n) (a : Coeff p)
    (hb : Tendsto (fun n : ℤ => (b n : Coeff p))
      (Filter.comap Int.natAbs Filter.atTop) (𝓝 a)) :
    TendstoUniformlyOn
      (fun n : ℤ => fun z : ℂ =>
        sourceSingleRootQuotientJointProduct hp hp1 m
          (z,((b n : Coeff p),ψ)) * sourcePsiDeletedIndexRatio n m z)
      (fun z : ℂ => sourceSingleRootQuotientJointProduct hp hp1 m (z,(a,ψ)))
      (Filter.comap Int.natAbs Filter.atTop) (sphere c R) := by
  obtain ⟨W,_,_,hreal,hdata⟩ :=
    exists_global_source_analytic_singleRootQuotient hp hp1
  have hQcont (x : Coeff p) : ContinuousOn
      (fun z : ℂ => sourceSingleRootQuotientJointProduct hp hp1 m (z,(x,ψ)))
      (sphere c R) := by
    intro z hz
    have ht : (z,(x,ψ)) ∈ sourceSingleRootQuotientJointDomain hp hp1 W m :=
      ⟨hreal hψ,hdisc (sphere_subset_closedBall hz)⟩
    have hAna := (hdata m).2 (z,(x,ψ)) ht
    have hinc : ContinuousAt (fun w : ℂ => (w,(x,ψ))) z := by fun_prop
    exact (hAna.continuousAt.comp
      (f := fun w : ℂ => (w,(x,ψ))) hinc).continuousWithinAt
  have hQ := (tendstoUniformlyOn_sourceSingleRootQuotient_varyingDeleted
    hp hp1 m ψ hψ c R hdisc b a hb).mono sphere_subset_closedBall
  have hratio := (tendstoUniformlyOn_sourcePsiDeletedIndexRatio_anyDisc
    m c R hR).mono sphere_subset_closedBall
  have hprod := tendstoUniformlyOn_mul_of_isCompact (isCompact_sphere c R)
    (hQcont a) continuousOn_const
    (Filter.Eventually.of_forall fun n => hQcont (b n : Coeff p))
    (eventually_continuousOn_sourcePsiDeletedIndexRatio_anyCircle m c R)
    hQ hratio
  simpa only [mul_one] using hprod

/-- The rational multiplier in the candidate entry remains uniformly
controlled when the entire deleted-root vector varies strongly. -/
theorem tendstoUniformlyOn_sourcePsiLimitMatrixMultiplier_varyingDeleted
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (m k : ℤ) (ψ : CoeffPair p)
    (c : ℂ) (R : ℝ)
    (b : ∀ n : ℤ, DeletedCoeff p n) (a : Coeff p)
    (hk : ∀ z ∈ sphere c R, displacedRoots a k - z ≠ 0)
    (hm : ∀ z ∈ sphere c R,
      z ∉ sourcePeriodicSegment hp hp1 ψ m)
    (hb : Tendsto (fun n : ℤ => (b n : Coeff p))
      (Filter.comap Int.natAbs Filter.atTop) (𝓝 a)) :
    TendstoUniformlyOn
      (fun n : ℤ => fun z : ℂ =>
        ((displacedRoots (b n : Coeff p) m-z) /
          (displacedRoots (b n : Coeff p) k-z)) *
            (I / sourceStandardRoot hp hp1 ψ m z))
      (fun z : ℂ =>
        ((displacedRoots a m-z)/(displacedRoots a k-z)) *
          (I / sourceStandardRoot hp hp1 ψ m z))
      (Filter.comap Int.natAbs Filter.atTop) (sphere c R) := by
  apply tendstoUniformlyOn_of_joint_continuousAt_compact
    (isCompact_sphere c R) (a := a)
    (a' := fun n : ℤ => (b n : Coeff p))
    (F := fun x : Coeff p => fun z : ℂ =>
      ((displacedRoots x m-z)/(displacedRoots x k-z)) *
        (I / sourceStandardRoot hp hp1 ψ m z)) ?_ hb
  intro z hz
  have hroot (j : ℤ) : Continuous (fun q : Coeff p × ℂ =>
      displacedRoots q.1 j - q.2) := by
    have heval : Continuous (fun x : Coeff p => x j) :=
      (lp.evalCLM ℂ (fun _ : ℤ => ℂ) p j).continuous
    change Continuous (fun q : Coeff p × ℂ =>
      ((Real.pi : ℂ) * j + q.1 j) - q.2)
    exact ((continuous_const.add (heval.comp continuous_fst)).sub
      continuous_snd)
  have hstd : ContinuousAt
      (fun q : Coeff p × ℂ => sourceStandardRoot hp hp1 ψ m q.2)
      (a,z) :=
    (sourceStandardRoot_analyticAt hp hp1 ψ m z
      (hm z hz)).continuousAt.comp continuousAt_snd
  exact (((hroot m).continuousAt.div (hroot k).continuousAt
    (hk z hz)).mul (continuousAt_const.div hstd
      (sourceStandardRoot_ne_zero_off_segment hp hp1 ψ m z
        (hm z hz))))

/-- Strong convergence of the deleted-root vectors gives the full
retained matrix integrand limit on a fixed valid contour. -/
theorem tendstoUniformlyOn_sourcePsi_fullJacobianIntegrand_varyingDeleted
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (m k : ℤ) (ψ : CoeffPair p)
    (hψ : IsRealType (CoeffPair.toMax p ψ))
    (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hdisc : closedBall c R ⊆
      sourceStandardRootOmittedDomain hp hp1 ψ m)
    (b : ∀ n : ℤ, DeletedCoeff p n) (a : Coeff p)
    (hb : Tendsto (fun n : ℤ => (b n : Coeff p))
      (Filter.comap Int.natAbs Filter.atTop) (𝓝 a))
    (hk : ∀ z ∈ sphere c R, displacedRoots a k - z ≠ 0)
    (hm : ∀ z ∈ sphere c R,
      z ∉ sourcePeriodicSegment hp hp1 ψ m) :
    TendstoUniformlyOn
      (fun n : ℤ => fun z : ℂ =>
        (Real.pi : ℂ) *
          (((displacedRoots (b n : Coeff p) m-z) /
              (displacedRoots (b n : Coeff p) k-z)) *
            ((((n-m : ℤ) : ℂ) *
              sourcePsiGapRegularFactor hp hp1 n m
                (b n : Coeff p) ψ z) /
                  sourceStandardRoot hp hp1 ψ m z)))
      (sourcePsiLimitMatrixIntegrand hp hp1 m k a ψ)
      (Filter.comap Int.natAbs Filter.atTop) (sphere c R) := by
  let A (x : Coeff p) (z : ℂ) :=
    ((displacedRoots x m-z)/(displacedRoots x k-z)) *
      (I / sourceStandardRoot hp hp1 ψ m z)
  have hA : ContinuousOn (A a) (sphere c R) :=
    continuousOn_sourcePsiLimitMatrixMultiplier hp hp1 m k a ψ
      c R hk hm
  have hroot : Continuous (fun x : Coeff p => displacedRoots x k) := by
    have heval : Continuous (fun x : Coeff p => x k) :=
      (lp.evalCLM ℂ (fun _ : ℤ => ℂ) p k).continuous
    change Continuous (fun x : Coeff p => (Real.pi : ℂ)*k + x k)
    exact continuous_const.add heval
  have hnot : displacedRoots a k ∉ sphere c R := by
    intro hmem
    exact hk (displacedRoots a k) hmem (sub_self _)
  have hrootlim : Tendsto
      (fun n : ℤ => displacedRoots (b n : Coeff p) k)
      (Filter.comap Int.natAbs Filter.atTop)
      (𝓝 (displacedRoots a k)) := hroot.continuousAt.tendsto.comp hb
  have hrootavoid : ∀ᶠ n : ℤ in Filter.comap Int.natAbs Filter.atTop,
      displacedRoots (b n : Coeff p) k ∉ sphere c R :=
    hrootlim.eventually (isClosed_sphere.isOpen_compl.mem_nhds hnot)
  have hAevent : ∀ᶠ n : ℤ in Filter.comap Int.natAbs Filter.atTop,
      ContinuousOn (A (b n : Coeff p)) (sphere c R) := by
    filter_upwards [hrootavoid] with n hn
    apply continuousOn_sourcePsiLimitMatrixMultiplier hp hp1 m k
      (b n : Coeff p) ψ c R _ hm
    intro z hz hzero
    have hzeq : displacedRoots (b n : Coeff p) k = z :=
      sub_eq_zero.mp hzero
    exact hn (hzeq.symm ▸ hz)
  have hAunif : TendstoUniformlyOn
      (fun n : ℤ => A (b n : Coeff p)) (A a)
      (Filter.comap Int.natAbs Filter.atTop) (sphere c R) :=
    tendstoUniformlyOn_sourcePsiLimitMatrixMultiplier_varyingDeleted
      hp hp1 m k ψ c R b a hk hm hb
  have hQR := tendstoUniformlyOn_sourcePsiQuotient_mul_ratio_varyingDeleted
    hp hp1 m ψ hψ c R hR hdisc b a hb
  obtain ⟨W,_,_,hreal,hdata⟩ :=
    exists_global_source_analytic_singleRootQuotient hp hp1
  have hQcont (x : Coeff p) : ContinuousOn
      (fun z : ℂ => sourceSingleRootQuotientJointProduct hp hp1 m
        (z,(x,ψ))) (sphere c R) := by
    intro z hz
    have ht : (z,(x,ψ)) ∈
        sourceSingleRootQuotientJointDomain hp hp1 W m :=
      ⟨hreal hψ,hdisc (sphere_subset_closedBall hz)⟩
    have hAna := (hdata m).2 (z,(x,ψ)) ht
    have hinc : ContinuousAt (fun w : ℂ => (w,(x,ψ))) z := by fun_prop
    exact (hAna.continuousAt.comp
      (f := fun w : ℂ => (w,(x,ψ))) hinc).continuousWithinAt
  have hQRcont : ∀ᶠ n : ℤ in Filter.comap Int.natAbs Filter.atTop,
      ContinuousOn (fun z : ℂ =>
        sourceSingleRootQuotientJointProduct hp hp1 m
          (z,((b n : Coeff p),ψ)) * sourcePsiDeletedIndexRatio n m z)
        (sphere c R) := by
    filter_upwards [eventually_continuousOn_sourcePsiDeletedIndexRatio_anyCircle
      m c R] with n hn
    exact (hQcont (b n : Coeff p)).mul hn
  have hprod := tendstoUniformlyOn_mul_of_isCompact
    (isCompact_sphere c R) hA (hQcont a) hAevent hQRcont
    hAunif hQR
  have heq (n : ℤ) (z : ℂ) :
      A (b n : Coeff p) z *
        (sourceSingleRootQuotientJointProduct hp hp1 m
          (z,((b n : Coeff p),ψ)) * sourcePsiDeletedIndexRatio n m z) =
      (Real.pi : ℂ) *
        (((displacedRoots (b n : Coeff p) m-z) /
            (displacedRoots (b n : Coeff p) k-z)) *
          ((((n-m : ℤ) : ℂ) *
            sourcePsiGapRegularFactor hp hp1 n m
              (b n : Coeff p) ψ z) /
                sourceStandardRoot hp hp1 ψ m z)) := by
    have hnroot : displacedRoots (b n : Coeff p) n =
        (Real.pi : ℂ)*n := by
      simp [displacedRoots,show (b n : Coeff p) n = 0 from (b n).property]
    have hreg : (Real.pi : ℂ) * (((n-m : ℤ) : ℂ) *
        sourcePsiGapRegularFactor hp hp1 n m
          (b n : Coeff p) ψ z) =
        (I * sourceSingleRootQuotientJointProduct hp hp1 m
          (z,((b n : Coeff p),ψ))) * sourcePsiDeletedIndexRatio n m z := by
      dsimp only [sourcePsiGapRegularFactor,sourcePsiDeletedIndexRatio]
      rw [hnroot]
      ring
    calc
      A (b n : Coeff p) z *
        (sourceSingleRootQuotientJointProduct hp hp1 m
          (z,((b n : Coeff p),ψ)) * sourcePsiDeletedIndexRatio n m z) =
        ((displacedRoots (b n : Coeff p) m-z) /
          (displacedRoots (b n : Coeff p) k-z)) *
          (((I * sourceSingleRootQuotientJointProduct hp hp1 m
            (z,((b n : Coeff p),ψ))) * sourcePsiDeletedIndexRatio n m z) /
              sourceStandardRoot hp hp1 ψ m z) := by
          dsimp [A]
          ring
      _ = ((displacedRoots (b n : Coeff p) m-z) /
          (displacedRoots (b n : Coeff p) k-z)) *
        (((Real.pi : ℂ) * (((n-m : ℤ) : ℂ) *
          sourcePsiGapRegularFactor hp hp1 n m
            (b n : Coeff p) ψ z)) /
              sourceStandardRoot hp hp1 ψ m z) := by rw [hreg]
      _ = _ := by ring
  have htarget : (fun z : ℂ => A a z *
      sourceSingleRootQuotientJointProduct hp hp1 m (z,(a,ψ))) =
      sourcePsiLimitMatrixIntegrand hp hp1 m k a ψ := by
    funext z
    dsimp [A,sourcePsiLimitMatrixIntegrand]
    ring
  simpa only [htarget] using hprod.congr
    (Filter.Eventually.of_forall fun n z _ => heq n z)

/-- The moving full integrands are eventually continuous on the
fixed circle. The selected deleted root is exactly its free center. -/
theorem eventually_continuousOn_sourcePsi_fullJacobianIntegrand_varyingDeleted
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (m k : ℤ) (ψ : CoeffPair p)
    (hψ : IsRealType (CoeffPair.toMax p ψ))
    (c : ℂ) (R : ℝ)
    (hdisc : closedBall c R ⊆
      sourceStandardRootOmittedDomain hp hp1 ψ m)
    (b : ∀ n : ℤ, DeletedCoeff p n) (a : Coeff p)
    (hb : Tendsto (fun n : ℤ => (b n : Coeff p))
      (Filter.comap Int.natAbs Filter.atTop) (𝓝 a))
    (hk : ∀ z ∈ sphere c R, displacedRoots a k - z ≠ 0)
    (hm : ∀ z ∈ sphere c R,
      z ∉ sourcePeriodicSegment hp hp1 ψ m) :
    ∀ᶠ n : ℤ in Filter.comap Int.natAbs Filter.atTop,
      ContinuousOn (fun z : ℂ =>
        (Real.pi : ℂ) *
          (((displacedRoots (b n : Coeff p) m-z) /
              (displacedRoots (b n : Coeff p) k-z)) *
            ((((n-m : ℤ) : ℂ) *
              sourcePsiGapRegularFactor hp hp1 n m
                (b n : Coeff p) ψ z) /
                  sourceStandardRoot hp hp1 ψ m z)))
        (sphere c R) := by
  obtain ⟨W,_,_,hreal,hdata⟩ :=
    exists_global_source_analytic_singleRootQuotient hp hp1
  have hfar := (tendsto_norm_freeCenter_sub_at_natAbs c).eventually_ge_atTop
    (R + 1)
  have hroot : Continuous (fun x : Coeff p => displacedRoots x k) := by
    have heval : Continuous (fun x : Coeff p => x k) :=
      (lp.evalCLM ℂ (fun _ : ℤ => ℂ) p k).continuous
    change Continuous (fun x : Coeff p => (Real.pi : ℂ)*k + x k)
    exact continuous_const.add heval
  have hnot : displacedRoots a k ∉ sphere c R := by
    intro hmem
    exact hk (displacedRoots a k) hmem (sub_self _)
  have hrootlim : Tendsto
      (fun n : ℤ => displacedRoots (b n : Coeff p) k)
      (Filter.comap Int.natAbs Filter.atTop)
      (𝓝 (displacedRoots a k)) := hroot.continuousAt.tendsto.comp hb
  have hrootavoid : ∀ᶠ n : ℤ in Filter.comap Int.natAbs Filter.atTop,
      displacedRoots (b n : Coeff p) k ∉ sphere c R :=
    hrootlim.eventually (isClosed_sphere.isOpen_compl.mem_nhds hnot)
  filter_upwards [hfar,hrootavoid] with n hnfar hnrootavoid
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
    have hdenpos : 0 < ‖(Real.pi : ℂ) * n-z‖ := by linarith
    exact norm_ne_zero_iff.mp (ne_of_gt hdenpos)
  have hQ : ContinuousOn
      (fun z : ℂ => sourceSingleRootQuotientJointProduct hp hp1 m
        (z,((b n : Coeff p),ψ)))
      (sphere c R) := by
    intro z hz
    have ht : (z,((b n : Coeff p),ψ)) ∈
        sourceSingleRootQuotientJointDomain hp hp1 W m :=
      ⟨hreal hψ,hdisc (sphere_subset_closedBall hz)⟩
    have hAna := (hdata m).2 (z,((b n : Coeff p),ψ)) ht
    have hinc : ContinuousAt
        (fun w : ℂ => (w,((b n : Coeff p),ψ))) z := by fun_prop
    exact (hAna.continuousAt.comp
      (f := fun w : ℂ => (w,((b n : Coeff p),ψ))) hinc).continuousWithinAt
  have hnroot : displacedRoots (b n : Coeff p) n =
      (Real.pi : ℂ) * n := by
    simp [displacedRoots,show (b n : Coeff p) n = 0 from (b n).property]
  have hregular : ContinuousOn
      (sourcePsiGapRegularFactor hp hp1 n m (b n : Coeff p) ψ)
      (sphere c R) := by
    change ContinuousOn (fun z : ℂ =>
      (I * sourceSingleRootQuotientJointProduct hp hp1 m
        (z,((b n : Coeff p),ψ))) /
          (displacedRoots (b n : Coeff p) n-z)) _
    exact (continuousOn_const.mul hQ).div
      (continuousOn_const.sub continuousOn_id)
      (by simpa only [hnroot] using hden)
  have hrootRatio : ContinuousOn
      (fun z : ℂ =>
        (displacedRoots (b n : Coeff p) m-z) /
          (displacedRoots (b n : Coeff p) k-z))
      (sphere c R) :=
    (continuousOn_const.sub continuousOn_id).div
      (continuousOn_const.sub continuousOn_id)
      (by
        intro z hz hzero
        have hzeq : displacedRoots (b n : Coeff p) k = z :=
          sub_eq_zero.mp hzero
        exact hnrootavoid (hzeq.symm ▸ hz))
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

/-- Strong convergence of the moving deleted-root data allows the
full selected integrand to pass through a fixed contour integral. -/
theorem tendsto_circleIntegral_sourcePsi_fullJacobianIntegrand_varyingDeleted
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (m k : ℤ) (ψ : CoeffPair p)
    (hψ : IsRealType (CoeffPair.toMax p ψ))
    (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hdisc : closedBall c R ⊆
      sourceStandardRootOmittedDomain hp hp1 ψ m)
    (b : ∀ n : ℤ, DeletedCoeff p n) (a : Coeff p)
    (hb : Tendsto (fun n : ℤ => (b n : Coeff p))
      (Filter.comap Int.natAbs Filter.atTop) (𝓝 a))
    (hk : ∀ z ∈ sphere c R, displacedRoots a k - z ≠ 0)
    (hm : ∀ z ∈ sphere c R,
      z ∉ sourcePeriodicSegment hp hp1 ψ m) :
    Tendsto (fun n : ℤ =>
      ∮ z in C(c,R),
        (Real.pi : ℂ) *
          (((displacedRoots (b n : Coeff p) m-z) /
              (displacedRoots (b n : Coeff p) k-z)) *
            ((((n-m : ℤ) : ℂ) *
              sourcePsiGapRegularFactor hp hp1 n m
                (b n : Coeff p) ψ z) /
                  sourceStandardRoot hp hp1 ψ m z)))
      (Filter.comap Int.natAbs Filter.atTop)
      (𝓝 (∮ z in C(c,R),
        sourcePsiLimitMatrixIntegrand hp hp1 m k a ψ z)) := by
  exact (tendstoUniformlyOn_sourcePsi_fullJacobianIntegrand_varyingDeleted
    hp hp1 m k ψ hψ c R hR hdisc b a hb hk hm).tendsto_circleIntegral_of_continuousOn
      hR (eventually_continuousOn_sourcePsi_fullJacobianIntegrand_varyingDeleted
        hp hp1 m k ψ hψ c R hdisc b a hb hk hm)

end NLS.ZakharovShabat
