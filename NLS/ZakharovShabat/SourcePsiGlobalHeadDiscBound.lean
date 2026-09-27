import NLS.ZakharovShabat.SourcePsiGlobalScalarAnalytic
import NLS.ZakharovShabat.SourcePsiQuotientUniformHeadDisc

/-!
# Uniform quotient bounds on finitely many selected contour discs

The finite head of an arbitrary real-type source has individually
chosen contour discs. Joint quotient analyticity and compactness give
one bound on all those discs near any fixed root input.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Finitely many selected discs contained in the omitted-root domains
have a common quotient-error bound on a neighborhood of both Banach
parameters. Their centers and radii need not be free-centered. -/
theorem exists_local_sourcePsiQuotient_uniformFiniteSelectedDiscBound
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (s : Finset ℤ) (c : ℤ → ℂ) (R : ℤ → ℝ)
    (hdom : ∀ m : ℤ,
      closedBall (c m) (R m) ⊆
        sourceStandardRootOmittedDomain hp hp1 φ m)
    (a₀ : Coeff p) :
    ∃ U : Set (Coeff p × CoeffPair p), IsOpen U ∧
      (a₀,φ) ∈ U ∧
      ∃ M : ℝ, 0 ≤ M ∧
        ∀ t ∈ U, ∀ m ∈ s,
          ∀ z ∈ closedBall (c m) (R m),
            ‖sourceSingleRootQuotientJointProduct hp hp1 m
              (z,t)-1‖ ≤ M := by
  obtain ⟨W,_,_,hreal,hQ⟩ :=
    exists_global_source_analytic_singleRootQuotient hp hp1
  have hφW : φ ∈ W := hreal hφ
  have hlocal (m : ℤ) :
      ∃ U : Set (Coeff p × CoeffPair p), IsOpen U ∧
        (a₀,φ) ∈ U ∧
        ∃ M : ℝ, 0 ≤ M ∧
          ∀ t ∈ U,
            ∀ z ∈ closedBall (c m) (R m),
              ‖sourceSingleRootQuotientJointProduct hp hp1 m
                (z,t)-1‖ ≤ M := by
    let D := sourceSingleRootQuotientJointDomain hp hp1 W m
    let f : ℂ × (Coeff p × CoeffPair p) → ℂ := fun q =>
      sourceSingleRootQuotientJointProduct hp hp1 m q - 1
    have hf : ContinuousOn f D :=
      (hQ m).2.continuousOn.sub continuousOn_const
    have hbase : ∀ z ∈ closedBall (c m) (R m),
        (z,(a₀,φ)) ∈ D := by
      intro z hz
      exact ⟨hφW,hdom m hz⟩
    obtain ⟨U,hUopen,hbaseU,M,hM,hbound⟩ :=
      NLS.ComplexAnalysis.exists_local_uniform_bound_on_compact_of_continuousOn
        f D (hQ m).1 hf _ (isCompact_closedBall _ _)
        (a₀,φ) hbase
    exact ⟨U,hUopen,hbaseU,M,hM,
      fun t ht z hz => (hbound t ht z hz).2⟩
  choose U hUopen hbase M hM hbound using hlocal
  let V : Set (Coeff p × CoeffPair p) := ⋂ m ∈ s, U m
  let C : ℝ := ∑ m ∈ s, M m
  have hVopen : IsOpen V := isOpen_biInter_finset (fun m _ => hUopen m)
  have hbaseV : (a₀,φ) ∈ V := by
    simp only [V,Set.mem_iInter]
    intro m _
    exact hbase m
  have hC : 0 ≤ C := Finset.sum_nonneg (fun m _ => hM m)
  refine ⟨V,hVopen,hbaseV,C,hC,?_⟩
  intro t ht m hm z hz
  simp only [V,Set.mem_iInter] at ht
  have htm : t ∈ U m := ht m hm
  have hmC : M m ≤ C :=
    Finset.single_le_sum (f := M) (fun k hk => hM k) hm
  exact (hbound m t htm z hz).trans hmC

/-- Near an arbitrary real-type source and any root input, the
quotient error on every selected contour disc has one `ℓᵖ`
majorant with a locally uniform norm bound. The bound is uniform
across the finite nonstandard head and the free-centered tail. -/
theorem exists_local_sourcePsiQuotient_uniformAllSelectedDiscMajorant
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (a₀ : Coeff p) :
    ∃ U : Set (Coeff p × CoeffPair p), IsOpen U ∧
      (a₀,φ) ∈ U ∧
      ∃ c : ℤ → ℂ, ∃ R : ℤ → ℝ,
        (∀ t ∈ U, ∀ m : ℤ,
          0 < R m ∧
          sourcePeriodicSegment hp hp1 t.2 m ⊆ ball (c m) (R m) ∧
          closedBall (c m) (R m) ⊆
            sourceStandardRootOmittedDomain hp hp1 t.2 m ∧
          sphere (c m) (R m) ⊆
            sourceCanonicalRootDomain hp hp1 t.2) ∧
        ∃ M : ℝ, 0 ≤ M ∧
          ∀ t ∈ U, ∃ B : Coeff p, ‖B‖ ≤ M ∧
            ∀ m : ℤ, ∀ z ∈ closedBall (c m) (R m),
              ‖sourceSingleRootQuotientJointProduct hp hp1 m
                (z,t)-1‖ ≤ ‖B m‖ := by
  obtain ⟨Kgeom,Vgeom,hVgeomOpen,hφVgeom,c,R,hchoice,hgeom⟩ :=
    exists_local_sourcePsi_allGap_contourFamily hp hp1 φ hφ
  let T : ℝ := ‖a₀‖+1
  have hT : 0 ≤ T := by dsimp [T]; positivity
  obtain ⟨N,ε,hε,Vtail,hVtailOpen,hφVtail,Ktail,hNK,
      Mtail,hMtail,htail⟩ :=
    exists_local_sourcePsiQuotient_uniformBoundedBallTailMajorant
      hp hp1 φ hφ T hT
  let K := max Kgeom Ktail
  let s : Finset ℤ := Finset.Icc (-(K : ℤ)) (K : ℤ)
  have hdom (m : ℤ) : closedBall (c m) (R m) ⊆
      sourceStandardRootOmittedDomain hp hp1 φ m :=
    (hgeom φ hφVgeom m).2.2.1
  obtain ⟨Uhead,hUheadOpen,hbaseHead,Mhead,hMhead,hhead⟩ :=
    exists_local_sourcePsiQuotient_uniformFiniteSelectedDiscBound
      hp hp1 φ hφ s c R hdom a₀
  let U : Set (Coeff p × CoeffPair p) :=
    Uhead ∩ (ball a₀ 1 ×ˢ (Vtail ∩ Vgeom))
  have hUopen : IsOpen U :=
    hUheadOpen.inter
      (isOpen_ball.prod (hVtailOpen.inter hVgeomOpen))
  have hbase : (a₀,φ) ∈ U := by
    exact ⟨hbaseHead,mem_ball_self (by norm_num),hφVtail,hφVgeom⟩
  let M : ℝ := s.card*Mhead+Mtail
  have hM : 0 ≤ M := by dsimp [M]; positivity
  refine ⟨U,hUopen,hbase,c,R,?_,M,hM,?_⟩
  · intro t ht m
    exact hgeom t.2 ht.2.2.2 m
  intro t ht
  obtain ⟨htHead,htBall,htTail,htGeom⟩ := ht
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
  · have hmK : K < m.natAbs := by
      simp only [s,Finset.mem_Icc] at hm
      omega
    have hmTail : Ktail ≤ m.natAbs := by dsimp [K] at hmK; omega
    have hN : ¬m.natAbs ≤ N := by omega
    obtain ⟨hc,hR⟩ := hchoice m (by dsimp [K] at hmK; omega)
    have hzref : z ∈ refinedResonantDisk m := by
      rw [hc,hR] at hz
      exact (Metric.closedBall_subset_ball
        (by nlinarith [Real.pi_pos])) hz
    have hzdisc : z ∈ sourceIsolatingDisc hp hp1 φ N ε m := by
      simpa only [sourceIsolatingDisc,if_neg hN] using hzref
    rw [hBtailEq m hm]
    exact hBtail m hmTail z hzdisc

end NLS.ZakharovShabat
