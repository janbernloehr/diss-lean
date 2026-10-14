import NLS.ZakharovShabat.SourceLemma10_5
import NLS.ZakharovShabat.SourceSingleRootQuotientAnalytic
import NLS.ZakharovShabat.SourceSingleRootQuotientAbsolute
import Mathlib.Analysis.Normed.Field.Lemmas

/-!
# Quotient products on the original common analytic domains

The literal symmetric cutoffs converge locally uniformly in all three
variables. Their limit agrees with the unconditional product, including
at numerator zeros. The printed closed-disk domain and the entire selected
disk retain the local source neighborhood from Lemma 10.5.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Global joint local uniform convergence of the literal deleted numerator cutoffs. -/
theorem tendstoLocallyUniformlyOn_jointDeletedSingleSpectralPartialProduct (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) :
    TendstoLocallyUniformlyOn (jointDeletedSingleSpectralPartialProduct (p := p) n)
      (jointDeletedSingleSpectralProduct n) atTop univ := by
  intro u hu q _
  have hb : ∀ a ∈ closedBall q.2 1, ‖a‖ ≤ ‖q.2‖+1 := by
    intro a ha
    have hd : ‖a-q.2‖ ≤ 1 := by simpa only [mem_closedBall,dist_eq_norm] using ha
    have hn := norm_le_norm_sub_add a q.2
    linarith
  have hc := tendstoUniformlyOn_jointDeletedSingleSpectralProduct hp hp1 n
    (closedBall q.1 1) (isCompact_closedBall _ _) (closedBall q.2 1) (‖q.2‖+1) (by positivity) hb
  refine ⟨ball q.1 1 ×ˢ ball q.2 1,
    mem_nhdsWithin_of_mem_nhds ((isOpen_ball.prod isOpen_ball).mem_nhds
      ⟨mem_ball_self (by norm_num),mem_ball_self (by norm_num)⟩),?_⟩
  exact (hc.mono (fun t ht => ⟨ball_subset_closedBall ht.1,ball_subset_closedBall ht.2⟩)) u hu

/-- The quotient retains exactly the Lemma 10.5 source domain. -/
theorem SourceLemma10_5Data.quotientJoint
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (h : SourceLemma10_5Data hp hp1 W) (n : ℤ) :
    IsOpen (sourceSingleRootQuotientJointDomain hp hp1 W n) ∧
    AnalyticOnNhd ℂ (sourceSingleRootQuotientJointProduct hp hp1 n)
      (sourceSingleRootQuotientJointDomain hp hp1 W n) :=
  ⟨isOpen_sourceSingleRootQuotientJointDomain hp hp1 W n (h.joint n).1,
    sourceSingleRootQuotientJointProduct_analyticOnNhd hp hp1 n W (h.joint n).2
      (fun q hq => h.nonzero q.2 n q.1 hq.2)⟩

/-- Joint local uniform convergence covers numerator zeros and coinciding displaced roots. -/
theorem SourceLemma10_5Data.quotientLocallyUniform
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (h : SourceLemma10_5Data hp hp1 W) (n : ℤ) :
    TendstoLocallyUniformlyOn (sourceSingleRootQuotientPartialProduct hp hp1 n)
      (sourceSingleRootQuotientJointProduct hp hp1 n) atTop
      (sourceSingleRootQuotientJointDomain hp hp1 W n) := by
  let Q := sourceSingleRootQuotientJointDomain hp hp1 W n
  let A : ℂ × (Coeff p × CoeffPair p) → ℂ × Coeff p := fun q => (q.1,q.2.1)
  let B : ℂ × (Coeff p × CoeffPair p) → ℂ × CoeffPair p := fun q => (q.1,q.2.2)
  have hAc : Continuous A := continuous_fst.prodMk (continuous_fst.comp continuous_snd)
  have hBc : Continuous B := continuous_fst.prodMk (continuous_snd.comp continuous_snd)
  have hBmap : MapsTo B Q (sourceStandardRootOmittedJointDomain hp hp1 W n) := fun _ hq => hq
  have hnum := (tendstoLocallyUniformlyOn_jointDeletedSingleSpectralPartialProduct hp hp1 n).comp A (mapsTo_univ _ Q) hAc.continuousOn
  have hden := (h.locally_uniform n).comp B hBmap hBc.continuousOn
  have hnumc : ContinuousOn (jointDeletedSingleSpectralProduct n ∘ A) Q :=
    (analyticOnNhd_jointDeletedSingleSpectralProduct hp hp1 n).continuousOn.comp hAc.continuousOn (mapsTo_univ _ Q)
  have hdenc : ContinuousOn (sourceStandardRootOmittedJointProduct hp hp1 n ∘ B) Q :=
    (h.joint n).2.continuousOn.comp hBc.continuousOn hBmap
  have hden0 : ∀ q ∈ Q, (sourceStandardRootOmittedJointProduct hp hp1 n ∘ B) q ≠ 0 :=
    fun q hq => h.nonzero q.2.2 n q.1 hq.2
  have hd := hnum.div₀ hden hnumc hdenc hden0
  apply hd.congr
  intro N q hq
  exact (sourceSingleRootQuotientPartialProduct_eq_div hp hp1 n N W q hq).symm

/-- The printed domain is the closed-disk complement times all displacement sequences and the same V. -/
theorem SourceLemma10_5Data.quotientClosedFixed
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    (h : SourceLemma10_5Data hp hp1 W) (hVW : V ⊆ W)
    {D : ℤ → Set ℂ} {c : ℝ} (hD : SourceIsolatingNeighborhoods hp hp1 V D c) (n : ℤ) :
    AnalyticOnNhd ℂ (sourceSingleRootQuotientJointProduct hp hp1 n)
      ((⋃ m : ℤ, ⋃ (_ : m ≠ n), closure (D m))ᶜ ×ˢ (univ ×ˢ V)) := by
  apply (h.quotientJoint n).2.mono
  intro q hq
  refine ⟨hVW hq.2.2,?_⟩
  intro m hm hseg
  exact hq.1 (mem_iUnion.mpr ⟨m,mem_iUnion.mpr ⟨hm,subset_closure (hD.gap q.2.2 hq.2.2 m hseg)⟩⟩)

/-- The literal unordered product is jointly analytic on the full moving-gap domain. -/
theorem SourceLemma10_5Data.quotientTprod
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (h : SourceLemma10_5Data hp hp1 W) (n : ℤ) :
    AnalyticOnNhd ℂ (fun q : ℂ × (Coeff p × CoeffPair p) =>
      ∏' m : {m : ℤ // m ≠ n},
        (displacedRoots q.2.1 m-q.1)/sourceStandardRoot hp hp1 q.2.2 m q.1)
      (sourceSingleRootQuotientJointDomain hp hp1 W n) := by
  intro q hq
  apply ((h.quotientJoint n).2 q hq).congr
  filter_upwards [(h.quotientJoint n).1.mem_nhds hq] with t ht
  exact (hasProd_sourceSingleRootQuotient_subtype hp hp1 t.2.2 t.2.1 t.1 n ht.2).tprod_eq.symm

/-- The quotient is jointly analytic on the whole selected disk for every displacement sequence. -/
theorem SourceLemma10_5Data.quotientDisk
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    (h : SourceLemma10_5Data hp hp1 W) (hVW : V ⊆ W)
    {D : ℤ → Set ℂ} {c : ℝ} (hD : SourceIsolatingNeighborhoods hp hp1 V D c) (n : ℤ) :
    AnalyticOnNhd ℂ (sourceSingleRootQuotientJointProduct hp hp1 n)
      (D n ×ˢ (univ ×ˢ V)) := by
  apply (h.quotientJoint n).2.mono
  intro q hq
  exact ⟨hVW hq.2.2,hD.disk_subset_omittedDomain q.2.2 hq.2.2 n hq.1⟩

/-- Fixing the source and displacement retains analyticity on the natural spectral domain. -/
theorem SourceLemma10_5Data.quotientSpectral
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (h : SourceLemma10_5Data hp hp1 W) (ψ : CoeffPair p) (hψ : ψ ∈ W)
    (a : Coeff p) (n : ℤ) :
    AnalyticOnNhd ℂ (fun z => sourceSingleRootQuotientJointProduct hp hp1 n (z,(a,ψ)))
      (sourceStandardRootOmittedDomain hp hp1 ψ n) := by
  intro z hz
  exact ((h.quotientJoint n).2 (z,(a,ψ)) ⟨hψ,hz⟩).comp
    (f := fun z : ℂ => (z,(a,ψ))) (analyticAt_id.prod analyticAt_const)

/-- The literal symmetric cutoffs converge uniformly on compact subsets of the triple domain. -/
theorem SourceLemma10_5Data.quotientCompact
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (h : SourceLemma10_5Data hp hp1 W) (n : ℤ)
    (K : Set (ℂ × (Coeff p × CoeffPair p))) (hK : IsCompact K)
    (hsub : K ⊆ sourceSingleRootQuotientJointDomain hp hp1 W n) :
    TendstoUniformlyOn (sourceSingleRootQuotientPartialProduct hp hp1 n)
      (sourceSingleRootQuotientJointProduct hp hp1 n) atTop K :=
  (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp
    ((h.quotientLocallyUniform n).mono hsub)

/-- The literal product is analytic on precisely the closed-disk domain printed in Corollary 10.6. -/
theorem SourceLemma10_5Data.quotientTprodClosedFixed
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    (h : SourceLemma10_5Data hp hp1 W) (hVW : V ⊆ W)
    {D : ℤ → Set ℂ} {c : ℝ} (hD : SourceIsolatingNeighborhoods hp hp1 V D c) (n : ℤ) :
    AnalyticOnNhd ℂ (fun q : ℂ × (Coeff p × CoeffPair p) =>
      ∏' m : {m : ℤ // m ≠ n},
        (displacedRoots q.2.1 m-q.1)/sourceStandardRoot hp hp1 q.2.2 m q.1)
      ((⋃ m : ℤ, ⋃ (_ : m ≠ n), closure (D m))ᶜ ×ˢ (univ ×ˢ V)) := by
  apply (h.quotientTprod n).mono
  intro q hq
  refine ⟨hVW hq.2.2,?_⟩
  intro m hm hseg
  exact hq.1 (mem_iUnion.mpr ⟨m,mem_iUnion.mpr ⟨hm,subset_closure (hD.gap q.2.2 hq.2.2 m hseg)⟩⟩)

end NLS.ZakharovShabat
