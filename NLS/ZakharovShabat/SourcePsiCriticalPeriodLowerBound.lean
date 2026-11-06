import NLS.ZakharovShabat.SourcePsiCriticalNormalizer
import NLS.ZakharovShabat.SourceRootPeriodPerturbation
import NLS.ZakharovShabat.SourceCriticalRelativeComparison

/-! # A constructed uniform lower bound for the actual comparison periods

Equation (38) uses the critical-filled numerator ξ from (36). Its analytic
extension to the original closed isolating disc follows from actual quotient
analyticity and separated critical roots. The uniform gap estimate then
gives a lower bound of one half for the normalized period, independently of
the deleted index and locally uniformly near every real source.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- One actual comparison circle with quantitative invertibility and product control. -/
def SourcePsiCriticalPeriodControl (hp : p ≠ ⊤) (hp1 : 1 < p)
    (s : (n : ℤ) → CoeffPair p → DeletedCoeff p n) (ψ : CoeffPair p) (n k : ℤ) (c : ℝ) : Prop :=
  ∃ P : SourceCriticalRootPeriodCircle hp hp1 ψ k,
    (∀ z ∈ closedBall (P.center:ℂ) P.radius, sourceCriticalRoot hp hp1 ψ n-z ≠ 0) ∧
    AnalyticOnNhd ℂ (sourcePsiCriticalFilledQuotient hp hp1 n k (s n ψ) ψ)
      (closedBall (P.center:ℂ) P.radius) ∧
    AnalyticOnNhd ℂ (sourceCriticalDeletedQuotient hp hp1 k ψ)
      (closedBall (P.center:ℂ) P.radius) ∧
    AnalyticOnNhd ℂ (sourcePsiCriticalNormalizer hp hp1 n k (s n ψ) ψ)
      (closedBall (P.center:ℂ) P.radius) ∧
    (1/2:ℝ) ≤ ‖(2*(Real.pi:ℂ))⁻¹*(∮ z in C((P.center:ℂ),P.radius),
      sourcePsiCriticalNormalizer hp hp1 n k (s n ψ) ψ z/sourceStandardRoot hp hp1 ψ k z)‖ ∧
    SourcePsiCriticalComparisonIdentity hp hp1 n k (s n ψ) ψ (P.center:ℂ) P.radius ∧
    ∀ z ∈ closedBall (P.center:ℂ) P.radius,
      SourcePsiCriticalRelativeEstimate hp hp1 n k (s n ψ) ψ z c

/-- The literal normalizing numerator is analytic on each separated comparison disc. -/
theorem analyticOnNhd_sourcePsiCriticalNormalizer
    (hp : p ≠ ⊤) (hp1 : 1 < p) {Q : Set (CoeffPair p)}
    (hQ : ∀ k : ℤ, AnalyticOnNhd ℂ (sourceSingleRootQuotientJointProduct hp hp1 k)
      (sourceSingleRootQuotientJointDomain hp hp1 Q k))
    (ψ : CoeffPair p) (hψ : ψ ∈ Q) (n k : ℤ) (a : DeletedCoeff p n)
    (P : SourceCriticalRootPeriodCircle hp hp1 ψ k)
    (havoid : ∀ z ∈ closedBall (P.center:ℂ) P.radius, sourceCriticalRoot hp hp1 ψ n-z ≠ 0) :
    AnalyticOnNhd ℂ (sourcePsiCriticalNormalizer hp hp1 n k a ψ)
      (closedBall (P.center:ℂ) P.radius) := by
  intro z hz
  have hquot := (hQ k (z,(sourcePsiFillDeletedRoot n a (sourceCriticalRoot hp hp1 ψ n),ψ))
    ⟨hψ,P.closedBall_subset_omittedDomain hz⟩).comp
      (f := fun z : ℂ => (z,(sourcePsiFillDeletedRoot n a (sourceCriticalRoot hp hp1 ψ n),ψ)))
      (analyticAt_id.prod (analyticAt_const.prod analyticAt_const))
  exact (analyticAt_const.div (analyticAt_const.sub analyticAt_id) (havoid z hz)).mul hquot

/-- The actual cancellation identity has a uniformly invertible normalizing period
on constructed original circles for every distant selected index. -/
theorem SourceLemma12_11Data.exists_local_critical_comparison_period_lower_bound
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W : Set (CoeffPair p)}
    {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
    (H : SourceLemma12_11Data hp hp1 W₀ W s)
    (φ : realTypeSourceLocus p) (hφ : φ.val ∈ W) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ.val ∈ V ∧ V ⊆ W ∧
      ∃ K : ℕ, ∃ c : ℝ, 1 ≤ c ∧ ∀ ψ ∈ V, ∀ n k : ℤ, K ≤ k.natAbs → k ≠ n →
        SourcePsiCriticalPeriodControl hp hp1 s ψ n k c := by
  obtain ⟨Vs,hVs,hφs,hVsW,K,hs⟩ := H.exists_local_critical_normalizer_small_tail φ hφ
  obtain ⟨I,_,_,hrealI,hisol⟩ := sourceLemma10_1 hp hp1
  obtain ⟨D,hDopen,_,hφD,_,χ,_,N,ε,_,_,c,hD⟩ := hisol φ.val (hrealI φ.property)
  obtain ⟨Q,hQ,_,hrealQ,hquot⟩ := exists_global_source_analytic_singleRootQuotient hp hp1
  obtain ⟨C,hC,_,hrealC,HC⟩ := sourceLemma10_11CirclePeriods hp hp1
  let V := Vs ∩ (D ∩ (Q ∩ C))
  refine ⟨V,hVs.inter (hDopen.inter (hQ.inter hC)),
    ⟨hφs,hφD,hrealQ φ.property,hrealC φ.property⟩,fun _ h => hVsW h.1,K,c,hD.one_le,?_⟩
  intro ψ hψ n k hk hkn
  obtain ⟨a,r,hr,he⟩ := hD.discs k
  let P := hD.periodCircle ψ hψ.2.1 k a r hr he
  have hcrit : sourceCriticalRoot hp hp1 ψ n ∈ sourceIsolatingDisc hp hp1 χ N ε n :=
    hD.cluster ψ hψ.2.1 n (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
  have havoid : ∀ z ∈ closedBall (P.center:ℂ) P.radius, sourceCriticalRoot hp hp1 ψ n-z ≠ 0 := by
    intro z hz hnz
    have hzcl : z ∈ closure (sourceIsolatingDisc hp hp1 χ N ε k) := by
      rw [he,closure_ball _ hr.ne']
      exact hz
    have hd := (hD.disjoint n k hkn.symm).closure_right
      (isOpen_sourceIsolatingDisc hp hp1 χ N ε n)
    rw [sub_eq_zero.mp hnz] at hcrit
    exact Set.disjoint_left.mp hd hcrit hzcl
  have hf := analyticOnNhd_sourcePsiCriticalNormalizer hp hp1 (fun j => (hquot j).2)
    ψ hψ.2.2.1 n k (s n ψ) P havoid
  have hprod (a' : Coeff p) : AnalyticOnNhd ℂ
      (fun z => sourceSingleRootQuotientJointProduct hp hp1 k (z,(a',ψ)))
      (closedBall (P.center:ℂ) P.radius) := by
    intro z hz
    exact ((hquot k).2 (z,(a',ψ)) ⟨hψ.2.2.1,P.closedBall_subset_omittedDomain hz⟩).comp
      (f := fun z : ℂ => (z,(a',ψ))) (analyticAt_id.prod (analyticAt_const.prod analyticAt_const))
  refine ⟨P,havoid,hprod _,hprod _,hf,?_,?_,?_⟩
  · have hb := P.normalized_period_lower_bound _ hf (1/2) (hs ψ hψ.1 n k hk hkn)
    norm_num only at hb
    exact hb
  · exact H.previous.psi.psi_critical_root_comparison HC (fun j => (hquot j).2) ψ
      (hVsW hψ.1) hψ.2.2.2 hψ.2.2.1 n k hkn P
        (fun z hz => havoid z (sphere_subset_closedBall hz))
  · intro z hz
    have hzcl : z ∈ closure (sourceIsolatingDisc hp hp1 χ N ε k) := by
      rw [he,closure_ball _ hr.ne']
      exact hz
    exact hD.norm_psiFilledQuotient_sub_critical_le ψ hψ.2.1 n k (s n ψ) z hzcl

/-- On a constructed open neighborhood of the entire real locus, the actual comparison
periods are bounded below uniformly in both indices and locally uniformly at every
complex source. The root family, circles, products and constants are all constructed. -/
theorem exists_sourcePsi_critical_period_control (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W₀ W : Set (CoeffPair p), ∃ s : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
      SourceLemma12_11Data hp hp1 W₀ W s ∧ ∃ U : Set (CoeffPair p),
        IsOpen U ∧ realTypeSourceLocus p ⊆ U ∧ U ⊆ W ∧
        ∀ ψ ∈ U, ∃ V : Set (CoeffPair p), IsOpen V ∧ ψ ∈ V ∧ V ⊆ U ∧
          ∃ K : ℕ, ∃ c : ℝ, 1 ≤ c ∧ ∀ χ ∈ V, ∀ n k : ℤ,
            K ≤ k.natAbs → k ≠ n → SourcePsiCriticalPeriodControl hp hp1 s χ n k c := by
  obtain ⟨W₀,_,_,_,W,_,_,hreal,s,H⟩ := sourceLemma12_11 hp hp1
  have hlocal (φ : realTypeSourceLocus p) :=
    H.exists_local_critical_comparison_period_lower_bound φ (hreal φ.property)
  choose V hV hφV hVW K c hc hcontrol using hlocal
  let U := ⋃ φ : realTypeSourceLocus p, V φ
  refine ⟨W₀,W,s,H,U,isOpen_iUnion hV,?_,?_,?_⟩
  · intro ψ hψ
    exact mem_iUnion.mpr ⟨⟨ψ,hψ⟩,hφV ⟨ψ,hψ⟩⟩
  · intro ψ hψ
    obtain ⟨φ,hφ⟩ := mem_iUnion.mp hψ
    exact hVW φ hφ
  · intro ψ hψ
    obtain ⟨φ,hφ⟩ := mem_iUnion.mp hψ
    exact ⟨V φ,hV φ,hφ,subset_iUnion V φ,K φ,c φ,hc φ,hcontrol φ⟩

end NLS.ZakharovShabat
