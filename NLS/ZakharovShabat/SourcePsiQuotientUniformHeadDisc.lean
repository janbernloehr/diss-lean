import NLS.ZakharovShabat.SourcePsiNearFreeDiscMajorant
import NLS.ZakharovShabat.SourcePsiQuotientQuantitativeDisc
import NLS.ZakharovShabat.CompleteParityDisplacementBounds
import NLS.ComplexAnalysis.CompactParameterBounds

/-!
# Locally uniform bounds on finitely many psi quotient discs

The tail majorant from Lemma 10.8 leaves finitely many selected
spectral discs. Joint analyticity and compactness control all of them
over a common neighborhood of the source and root input.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- For any finite set of selected free discs, the quotient error is
uniformly bounded near an arbitrary root input and the free source. -/
theorem exists_nearFree_sourcePsiQuotient_uniformFiniteDiscBound
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (s : Finset ℤ) (a₀ : Coeff p) :
    ∃ U : Set (Coeff p × CoeffPair p), IsOpen U ∧
      (a₀,(0 : CoeffPair p)) ∈ U ∧
      ∃ M : ℝ, 0 ≤ M ∧
        ∀ t ∈ U, ∀ m ∈ s,
          ∀ z ∈ closedBall ((Real.pi : ℂ)*m) (Real.pi/8),
            ‖sourceSingleRootQuotientJointProduct hp hp1 m
              (z,t)-1‖ ≤ M := by
  obtain ⟨Vgeom,_,hzeroGeom,hgeom⟩ :=
    exists_nearFree_freeQuarterDisc_subset_omittedDomain hp hp1
  obtain ⟨W,_,_,hreal,hQ⟩ :=
    exists_global_source_analytic_singleRootQuotient hp hp1
  have hzeroW : (0 : CoeffPair p) ∈ W :=
    hreal (by simp [realTypeSourceLocus])
  have hlocal (m : ℤ) :
      ∃ U : Set (Coeff p × CoeffPair p), IsOpen U ∧
        (a₀,(0 : CoeffPair p)) ∈ U ∧
        ∃ M : ℝ, 0 ≤ M ∧
          ∀ t ∈ U,
            ∀ z ∈ closedBall ((Real.pi : ℂ)*m) (Real.pi/8),
              ‖sourceSingleRootQuotientJointProduct hp hp1 m
                (z,t)-1‖ ≤ M := by
    let D := sourceSingleRootQuotientJointDomain hp hp1 W m
    let f : ℂ × (Coeff p × CoeffPair p) → ℂ := fun q =>
      sourceSingleRootQuotientJointProduct hp hp1 m q - 1
    have hf : ContinuousOn f D :=
      (hQ m).2.continuousOn.sub continuousOn_const
    have hbase : ∀ z ∈ closedBall ((Real.pi : ℂ)*m) (Real.pi/8),
        (z,(a₀,(0 : CoeffPair p))) ∈ D := by
      intro z hz
      change (0 : CoeffPair p) ∈ W ∧
        z ∈ sourceStandardRootOmittedDomain hp hp1 0 m
      refine ⟨hzeroW,?_⟩
      apply hgeom 0 hzeroGeom m
      exact (Metric.closedBall_subset_closedBall
        (by nlinarith [Real.pi_pos])) hz
    obtain ⟨U,hUopen,hbaseU,M,hM,hbound⟩ :=
      NLS.ComplexAnalysis.exists_local_uniform_bound_on_compact_of_continuousOn
        f D (hQ m).1 hf _ (isCompact_closedBall _ _)
        (a₀,(0 : CoeffPair p)) hbase
    exact ⟨U,hUopen,hbaseU,M,hM,fun t ht z hz => (hbound t ht z hz).2⟩
  choose U hUopen hbase M hM hbound using hlocal
  let V : Set (Coeff p × CoeffPair p) := ⋂ m ∈ s, U m
  let C : ℝ := ∑ m ∈ s, M m
  have hVopen : IsOpen V := isOpen_biInter_finset (fun m _ => hUopen m)
  have hbaseV : (a₀,(0 : CoeffPair p)) ∈ V := by
    simp only [V,Set.mem_iInter]
    intro m hm
    exact hbase m
  have hC : 0 ≤ C := Finset.sum_nonneg (fun m _ => hM m)
  refine ⟨V,hVopen,hbaseV,C,hC,?_⟩
  intro t ht m hm z hz
  simp only [V,Set.mem_iInter] at ht
  have htm : t ∈ U m := ht m hm
  have hmC : M m ≤ C :=
    Finset.single_le_sum (f := M) (fun k hk => hM k) hm
  exact (hbound m t htm z hz).trans hmC

/-- Near an arbitrary root input and the free source, one `ℓᵖ`
quotient-error majorant controls every selected free eighth-π disc,
and its norm has a common bound on the parameter neighborhood. -/
theorem exists_nearFree_sourcePsiQuotient_uniformAllDiscMajorant
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (a₀ : Coeff p) :
    ∃ U : Set (Coeff p × CoeffPair p), IsOpen U ∧
      (a₀,(0 : CoeffPair p)) ∈ U ∧
      ∃ M : ℝ, 0 ≤ M ∧
        ∀ t ∈ U, ∃ B : Coeff p, ‖B‖ ≤ M ∧
          ∀ m : ℤ,
            ∀ z ∈ closedBall ((Real.pi : ℂ)*m) (Real.pi/8),
              ‖sourceSingleRootQuotientJointProduct hp hp1 m
                (z,t)-1‖ ≤ ‖B m‖ := by
  let T : ℝ := ‖a₀‖+1
  have hT : 0 ≤ T := by dsimp [T]; positivity
  obtain ⟨N,ε,hε,Vtail,hVtailOpen,hzeroTail,K,hNK,Mtail,hMtail,htail⟩ :=
    exists_local_sourcePsiQuotient_uniformBoundedBallTailMajorant
      hp hp1 (0 : CoeffPair p) (by simp) T hT
  let s : Finset ℤ := Finset.Icc (-(K : ℤ)) (K : ℤ)
  obtain ⟨Uhead,hUheadOpen,hbaseHead,Mhead,hMhead,hhead⟩ :=
    exists_nearFree_sourcePsiQuotient_uniformFiniteDiscBound hp hp1 s a₀
  let U : Set (Coeff p × CoeffPair p) :=
    Uhead ∩ (ball a₀ 1 ×ˢ Vtail)
  let M : ℝ := s.card*Mhead+Mtail
  have hUopen : IsOpen U :=
    hUheadOpen.inter (isOpen_ball.prod hVtailOpen)
  have hbase : (a₀,(0 : CoeffPair p)) ∈ U := by
    exact ⟨hbaseHead,mem_ball_self (by norm_num),hzeroTail⟩
  have hM : 0 ≤ M := by dsimp [M]; positivity
  refine ⟨U,hUopen,hbase,M,hM,?_⟩
  intro t ht
  obtain ⟨htHead,htBall,htTail⟩ := ht
  have ha : ‖t.1‖ ≤ T := by
    have hdist : ‖t.1-a₀‖ < 1 := by
      simpa only [mem_ball,dist_eq_norm] using htBall
    have hsum : ‖t.1‖ ≤ ‖a₀‖+‖t.1-a₀‖ := by
      have heq : t.1 = a₀+(t.1-a₀) := by abel
      calc
        ‖t.1‖ = ‖a₀+(t.1-a₀)‖ := congrArg norm heq
        _ ≤ _ := norm_add_le a₀ (t.1-a₀)
    dsimp [T]
    linarith
  obtain ⟨Btail,hBtailNorm,hBtail⟩ := htail t.2 htTail t.1 ha
  let b : ℤ → ℂ := fun m => if m ∈ s then (Mhead : ℂ) else Btail m
  have hbmem : Memℓp b p := by
    apply NLS.memℓp_of_eq_outside_finset (lp.memℓp Btail) s
    intro m hm
    simp [b,hm]
  let B : Coeff p := ⟨b,hbmem⟩
  have hBhead (m : ℤ) (hm : m ∈ s) : ‖B m‖ = Mhead := by
    simp only [B,b,if_pos hm,Complex.norm_real]
    exact Real.norm_of_nonneg hMhead
  have hBtailEq (m : ℤ) (hm : m ∉ s) : B m = Btail m := by
    simp [B,b,hm]
  have hBnorm : ‖B‖ ≤ M := by
    calc
      ‖B‖ ≤ s.card*Mhead+‖Btail‖ := by
        apply NLS.Coeff.norm_le_of_eq_outside_finset B Btail s Mhead
        · intro m hm
          exact (hBhead m hm).le
        · exact hBtailEq
      _ ≤ M := by dsimp [M]; gcongr
  refine ⟨B,hBnorm,?_⟩
  intro m z hz
  by_cases hm : m ∈ s
  · rw [hBhead m hm]
    exact hhead t htHead m hm z hz
  · have hmK : K ≤ m.natAbs := by
      simp only [s,Finset.mem_Icc] at hm
      omega
    have hN : ¬m.natAbs ≤ N := by omega
    have hzdisc : z ∈ sourceIsolatingDisc hp hp1
        (0 : CoeffPair p) N ε m := by
      have hzref : z ∈ refinedResonantDisk m := by
        exact (Metric.closedBall_subset_ball
          (by nlinarith [Real.pi_pos])) hz
      simpa only [sourceIsolatingDisc,if_neg hN] using hzref
    rw [hBtailEq m hm]
    exact hBtail m hmK z hzdisc

/-- The all-disc estimate supplies the regular factor in the psi
equation with one locally uniform majorant norm, independently of the
deleted coordinate. -/
theorem exists_nearFree_deletedPsi_uniformRegularFactorMajorant
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (a₀ : Coeff p) :
    ∃ U : Set (Coeff p × CoeffPair p), IsOpen U ∧
      (a₀,(0 : CoeffPair p)) ∈ U ∧
      ∃ M : ℝ, 0 ≤ M ∧
        ∀ n : ℤ, ∀ a : DeletedCoeff p n, ∀ ψ : CoeffPair p,
          ((a : Coeff p),ψ) ∈ U →
            ∃ B : Coeff p, ‖B‖ ≤ M ∧
              ∀ m : ℤ, m ≠ n →
                ∀ z ∈ closedBall ((Real.pi : ℂ)*m) (Real.pi/8),
                  ‖(((n-m : ℤ) : ℂ) *
                    sourcePsiGapRegularFactor hp hp1 n m
                      (a : Coeff p) ψ z)‖ ≤
                    (2/Real.pi)*(1+‖B m‖) := by
  obtain ⟨U,hUopen,hbase,M,hM,hmajor⟩ :=
    exists_nearFree_sourcePsiQuotient_uniformAllDiscMajorant hp hp1 a₀
  refine ⟨U,hUopen,hbase,M,hM,?_⟩
  intro n a ψ hpair
  obtain ⟨B,hBnorm,hB⟩ := hmajor ((a : Coeff p),ψ) hpair
  refine ⟨B,hBnorm,?_⟩
  intro m hmn z hz
  exact norm_deletedPsi_gapRegularFactor_weighted_le
    hp hp1 n m (Ne.symm hmn) a ψ B (Real.pi/8)
      (by nlinarith [Real.pi_pos]) z hz (hB m z hz)

end NLS.ZakharovShabat
