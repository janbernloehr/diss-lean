import NLS.ZakharovShabat.SourceCanonicalRootProduct

/-!
# Joint analyticity of the canonical root

One connected almost-real source domain supports all analytic midpoint
and squared-gap coordinates. On the joint complement of every moving
gap segment, the central root and its omitted complementary product are
jointly analytic. Their product is the canonical root of equation (2.13).
-/

noncomputable section
open Set Filter Topology Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The canonical root as a joint spectral/source function. -/
def sourceCanonicalRootJointProduct (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ℂ × CoeffPair p → ℂ :=
  fun t => sourceCanonicalRoot hp hp1 t.2 t.1

/-- The full moving-gap complement over a source domain. -/
def sourceCanonicalRootJointDomain (hp : p ≠ ⊤) (hp1 : 1 < p)
    (W : Set (CoeffPair p)) : Set (ℂ × CoeffPair p) :=
  {t | t.2 ∈ W ∧ t.1 ∈ sourceCanonicalRootDomain hp hp1 t.2}

/-- The full gap complement is the intersection of two arbitrary-index
omitted-root domains. Each of indices zero and one restores the gap
missing from the other domain. -/
theorem sourceCanonicalRootJointDomain_eq_inter_omitted
    (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p)) :
    sourceCanonicalRootJointDomain hp hp1 W =
      sourceStandardRootOmittedJointDomain hp hp1 W 0 ∩
        sourceStandardRootOmittedJointDomain hp hp1 W 1 := by
  ext t
  constructor
  · intro ht
    exact ⟨⟨ht.1, fun m _ => ht.2 m⟩,
      ⟨ht.1, fun m _ => ht.2 m⟩⟩
  · rintro ⟨hzero,hone⟩
    refine ⟨hzero.1, ?_⟩
    intro m
    by_cases hm : m = 0
    · subst m
      exact hone.2 0 (by norm_num)
    · exact hzero.2 m hm

set_option maxHeartbeats 800000 in
/-- On one connected almost-real source domain, the canonical root is
jointly analytic outside all moving periodic gap segments. -/
theorem exists_global_source_analytic_canonicalRoot
    (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ IsConnected W ∧
      realTypeSourceLocus p ⊆ W ∧
      IsOpen (sourceCanonicalRootJointDomain hp hp1 W) ∧
      AnalyticOnNhd ℂ (sourceCanonicalRootJointProduct hp hp1)
        (sourceCanonicalRootJointDomain hp hp1 W) := by
  obtain ⟨W,hWopen,hWconn,hreal,hA⟩ :=
    exists_global_source_analytic_midpoint_squaredGap hp hp1
  obtain ⟨hDzero,hpaired⟩ :=
    sourceStandardRootOmittedJointProduct_analyticOnNhd_of_symmetric
      hp hp1 W hWopen hA 0
  obtain ⟨hDone,_⟩ :=
    sourceStandardRootOmittedJointProduct_analyticOnNhd_of_symmetric
      hp hp1 W hWopen hA 1
  have hDopen : IsOpen (sourceCanonicalRootJointDomain hp hp1 W) := by
    rw [sourceCanonicalRootJointDomain_eq_inter_omitted]
    exact hDzero.inter hDone
  refine ⟨W,hWopen,hWconn,hreal,hDopen,?_⟩
  intro t ht
  have htz : t ∈ sourceStandardRootOmittedJointDomain hp hp1 W 0 :=
    ⟨ht.1, fun m _ => ht.2 m⟩
  have hroot : AnalyticAt ℂ
      (fun q : ℂ × CoeffPair p => sourceStandardRoot hp hp1 q.2 0 q.1) t :=
    sourceStandardRoot_joint_analyticAt_of_symmetric hp hp1 t.2 0 t.1
      (hA t.2 ht.1 0).1 (hA t.2 ht.1 0).2 (ht.2 0)
  have hpaired' : AnalyticAt ℂ
      (fun q : ℂ × CoeffPair p => sourceStandardRootPairedProduct hp hp1 q.2 q.1) t := by
    change AnalyticAt ℂ (sourceStandardRootPairedJointProduct hp hp1) t
    rw [← sourceStandardRootOmittedJointProduct_zero hp hp1]
    exact hpaired t htz
  change AnalyticAt ℂ (fun q : ℂ × CoeffPair p =>
    2*I * sourceStandardRoot hp hp1 q.2 0 q.1 *
      sourceStandardRootPairedProduct hp hp1 q.2 q.1) t
  exact (analyticAt_const.mul hroot).mul hpaired'

/-- When the `n`th periodic gap collapses, its standard root becomes a
linear factor. The canonical root therefore extends analytically through
that gap, provided all other gap segments are avoided. -/
theorem sourceCanonicalRoot_analyticOnNhd_of_zeroGap
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (W : Set (CoeffPair p)) (n : ℤ)
    (hprod : AnalyticOnNhd ℂ (sourceStandardRootOmittedJointProduct hp hp1 n)
      (sourceStandardRootOmittedJointDomain hp hp1 W n))
    (ψ : CoeffPair p) (hψ : ψ ∈ W)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n = 0) :
    AnalyticOnNhd ℂ (sourceCanonicalRoot hp hp1 ψ)
      (sourceStandardRootOmittedDomain hp hp1 ψ n) := by
  have hpaired := sourceStandardRootOmittedProduct_analyticOnNhd_spectral
    hp hp1 n W hprod ψ hψ
  let τ := canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  have hfun : sourceCanonicalRoot hp hp1 ψ =
      (fun w => 2*I * (τ-w) * sourceStandardRootOmittedProduct hp hp1 n ψ w) := by
    funext w
    rw [sourceCanonicalRoot_eq_omitted hp hp1 n ψ w,
      sourceStandardRoot_of_zeroGap hp hp1 ψ n w hgap]
  rw [hfun]
  intro z hz
  have hlinear : AnalyticAt ℂ (fun w : ℂ => τ-w) z :=
    analyticAt_const.sub analyticAt_id
  exact (analyticAt_const.mul hlinear).mul (hpaired z hz)

end NLS.ZakharovShabat
