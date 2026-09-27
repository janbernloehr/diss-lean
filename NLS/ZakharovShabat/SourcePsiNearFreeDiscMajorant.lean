import NLS.ZakharovShabat.SourcePsiNearFreeGapGeometry
import NLS.ZakharovShabat.SourcePsiQuotientDiscMajorant
import NLS.SequenceSpaces.FiniteModification

/-!
# An all-index quotient majorant near the free source

Lemma 10.8 supplies an `ℓᵖ` quotient-error majorant on all distant
selected discs. On a sufficiently small source neighborhood, the
finitely many remaining free eighth-π discs also lie in the analytic
omitted-root domain. Compactness gives a maximum on each of those
discs, and finite modification preserves the `ℓᵖ` majorant.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- A quotient analytic through one closed spectral disc has a
pointwise maximum there, represented by a complex value. -/
theorem exists_sourcePsiQuotient_closedDisc_bound
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (W : Set (CoeffPair p)) (m : ℤ) (a : Coeff p) (ψ : CoeffPair p)
    (hψ : ψ ∈ W)
    (hQ : AnalyticOnNhd ℂ
      (sourceSingleRootQuotientJointProduct hp hp1 m)
      (sourceSingleRootQuotientJointDomain hp hp1 W m))
    (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hdom : closedBall c R ⊆
      sourceStandardRootOmittedDomain hp hp1 ψ m) :
    ∃ v : ℂ, ∀ z ∈ closedBall c R,
      ‖sourceSingleRootQuotientJointProduct hp hp1 m
        (z,(a,ψ))-1‖ ≤ ‖v‖ := by
  let Q : ℂ → ℂ := fun z =>
    sourceSingleRootQuotientJointProduct hp hp1 m (z,(a,ψ))-1
  have hcont : ContinuousOn Q (closedBall c R) := by
    intro z hz
    have hmap : AnalyticAt ℂ (fun w : ℂ => (w,(a,ψ))) z :=
      analyticAt_id.prod (analyticAt_const.prod analyticAt_const)
    have hquot : AnalyticAt ℂ
        (fun w => sourceSingleRootQuotientJointProduct hp hp1 m
          (w,(a,ψ))) z :=
      (hQ (z,(a,ψ)) ⟨hψ,hdom hz⟩).comp
        (f := fun w : ℂ => (w,(a,ψ))) hmap
    exact (hquot.sub analyticAt_const).continuousAt.continuousWithinAt
  have hne : (closedBall c R).Nonempty :=
    ⟨c,mem_closedBall_self hR⟩
  obtain ⟨zmax,hzmax,hmax⟩ :=
    (isCompact_closedBall c R).exists_isMaxOn hne hcont.norm
  refine ⟨Q zmax,?_⟩
  intro z hz
  exact hmax hz

/-- On one open source neighborhood, every selected free eighth-π
disc has a quotient-error majorant from a single `ℓᵖ` sequence,
with no exceptional spectral indices. -/
theorem exists_nearFree_sourcePsiQuotient_allDiscMajorant
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ (0 : CoeffPair p) ∈ V ∧
      ∀ ψ ∈ V, ∀ a : Coeff p,
        ∃ B : Coeff p, ∀ m : ℤ,
          ∀ z ∈ closedBall ((Real.pi : ℂ)*m) (Real.pi/8),
            ‖sourceSingleRootQuotientJointProduct hp hp1 m
              (z,(a,ψ))-1‖ ≤ ‖B m‖ := by
  obtain ⟨N,ε,hε,Vtail,hVtailOpen,hzeroTail,K,hNK,htail⟩ :=
    exists_local_sourcePsiQuotient_lpDiscMajorant hp hp1
      (0 : CoeffPair p) (by simp)
  obtain ⟨Vgeom,hVgeomOpen,hzeroGeom,hgeom⟩ :=
    exists_nearFree_freeQuarterDisc_subset_omittedDomain hp hp1
  obtain ⟨W,hWopen,_,hreal,hQ⟩ :=
    exists_global_source_analytic_singleRootQuotient hp hp1
  have hzeroW : (0 : CoeffPair p) ∈ W :=
    hreal (by simp [realTypeSourceLocus])
  let V := Vtail ∩ Vgeom ∩ W
  refine ⟨V,(hVtailOpen.inter hVgeomOpen).inter hWopen,
    ⟨⟨hzeroTail,hzeroGeom⟩,hzeroW⟩,?_⟩
  intro ψ hψ a
  obtain ⟨Btail,hBtail⟩ := htail ψ hψ.1.1 a
  have hhead (m : ℤ) :
      ∃ v : ℂ, ∀ z ∈ closedBall ((Real.pi : ℂ)*m) (Real.pi/8),
        ‖sourceSingleRootQuotientJointProduct hp hp1 m
          (z,(a,ψ))-1‖ ≤ ‖v‖ := by
    apply exists_sourcePsiQuotient_closedDisc_bound hp hp1 W m a ψ
      hψ.2 (hQ m).2 ((Real.pi : ℂ)*m) (Real.pi/8) (by positivity)
    exact (Metric.closedBall_subset_closedBall (by nlinarith [Real.pi_pos])).trans
      (hgeom ψ hψ.1.2 m)
  choose head hheadBound using hhead
  let s : Finset ℤ := Finset.Icc (-(K : ℤ)) (K : ℤ)
  let b : ℤ → ℂ := fun m => if m ∈ s then head m else Btail m
  have hbmem : Memℓp b p := by
    apply NLS.memℓp_of_eq_outside_finset (lp.memℓp Btail) s
    intro m hm
    simp [b,hm]
  let B : Coeff p := ⟨b,hbmem⟩
  refine ⟨B,?_⟩
  intro m z hz
  by_cases hm : m ∈ s
  · simpa [B,b,hm] using hheadBound m z hz
  · have hmK : K ≤ m.natAbs := by
      simp only [s,Finset.mem_Icc] at hm
      omega
    have hN : ¬m.natAbs ≤ N := by omega
    have hzdisc : z ∈ sourceIsolatingDisc hp hp1
        (0 : CoeffPair p) N ε m := by
      have hzref : z ∈ refinedResonantDisk m := by
        exact (Metric.closedBall_subset_ball (by nlinarith [Real.pi_pos])) hz
      simpa only [sourceIsolatingDisc,if_neg hN] using hzref
    simpa [B,b,hm] using hBtail m hmK z hzdisc

/-- The weighted regular factor in the actual psi contour integrand
has an all-index `ℓᵖ` disc majorant near the free source, uniformly in
the deleted index. This is the near-free form of (2.26). -/
theorem exists_nearFree_deletedPsi_gapRegularFactor_allDiscMajorant
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ (0 : CoeffPair p) ∈ V ∧
      ∀ ψ ∈ V, ∀ n : ℤ, ∀ a : DeletedCoeff p n,
        ∃ B : Coeff p, ∀ m : ℤ, m ≠ n →
          ∀ z ∈ closedBall ((Real.pi : ℂ)*m) (Real.pi/8),
            ‖(((n-m : ℤ) : ℂ) *
              sourcePsiGapRegularFactor hp hp1 n m
                (a : Coeff p) ψ z)‖ ≤
              (2/Real.pi)*(1+‖B m‖) := by
  obtain ⟨V,hVopen,hzero,hmajor⟩ :=
    exists_nearFree_sourcePsiQuotient_allDiscMajorant hp hp1
  refine ⟨V,hVopen,hzero,?_⟩
  intro ψ hψ n a
  obtain ⟨B,hB⟩ := hmajor ψ hψ (a : Coeff p)
  refine ⟨B,?_⟩
  intro m hmn z hz
  exact norm_deletedPsi_gapRegularFactor_weighted_le
    hp hp1 n m (Ne.symm hmn) a ψ B (Real.pi/8)
      (by nlinarith [Real.pi_pos]) z hz (hB m z hz)

end NLS.ZakharovShabat
