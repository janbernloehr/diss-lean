import NLS.ZakharovShabat.SourceNormalizedActionUniformTailCircles
import NLS.ZakharovShabat.SourceCriticalRootRatioUniformCircle

/-!
# A common contour family near an arbitrary real-type source

Uniform free-centered tail circles and finitely many individually
selected head circles are patched on one complex source neighborhood.
Every circle encloses its moving gap and avoids every other gap.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Near any real-type source, one family of circles works for every
periodic gap, uniformly over a common complex source neighborhood.
Only finitely many circle centers and radii differ from the free
eighth-π choice. -/
theorem exists_local_sourcePsi_allGap_realCenteredContourFamily
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ K : ℕ, ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∃ c : ℤ → ℂ, ∃ R : ℤ → ℝ,
        (∀ m : ℤ, (c m).im = 0) ∧
        (∀ m : ℤ, K < m.natAbs →
          c m = (Real.pi : ℂ)*m ∧ R m = Real.pi/8) ∧
        ∀ ψ ∈ V, ∀ m : ℤ,
          0 < R m ∧
          sourcePeriodicSegment hp hp1 ψ m ⊆ ball (c m) (R m) ∧
          closedBall (c m) (R m) ⊆
            sourceStandardRootOmittedDomain hp hp1 ψ m ∧
          sphere (c m) (R m) ⊆
            sourceCanonicalRootDomain hp hp1 ψ := by
  obtain ⟨K,Vtail,hVtailOpen,hφVtail,htail⟩ :=
    exists_local_sourceNormalizedAction_uniform_tail_circle_data
      hp hp1 φ hφ
  have hlocal (m : ℤ) :
      ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
        ∃ c : ℂ, ∃ R : ℝ, c.im = 0 ∧ 0 < R ∧
          ∀ ψ ∈ V,
            sourcePeriodicSegment hp hp1 ψ m ⊆ ball c R ∧
            closedBall c R ⊆
              sourceStandardRootOmittedDomain hp hp1 ψ m ∧
            sphere c R ⊆ sourceCanonicalRootDomain hp hp1 ψ :=
    exists_local_sourceCriticalRootRatio_uniformRealCenteredEnclosingCircle
      hp hp1 φ hφ m
  choose Vhead hVheadOpen hφVhead chead Rhead hcheadReal hRhead hhead using hlocal
  let s : Finset ℤ := Finset.Icc (-(K : ℤ)) (K : ℤ)
  let Vheads : Set (CoeffPair p) := ⋂ m ∈ s, Vhead m
  have hVheadsOpen : IsOpen Vheads :=
    isOpen_biInter_finset (fun m _ => hVheadOpen m)
  have hφVheads : φ ∈ Vheads := by
    simp only [Vheads,Set.mem_iInter]
    intro m _
    exact hφVhead m
  let V : Set (CoeffPair p) := Vtail ∩ Vheads
  have hVopen : IsOpen V := hVtailOpen.inter hVheadsOpen
  have hφV : φ ∈ V := ⟨hφVtail,hφVheads⟩
  let c : ℤ → ℂ := fun m =>
    if m ∈ s then chead m else (Real.pi : ℂ)*m
  let R : ℤ → ℝ := fun m =>
    if m ∈ s then Rhead m else Real.pi/8
  have htailChoice (m : ℤ) (hm : K < m.natAbs) :
      c m = (Real.pi : ℂ)*m ∧ R m = Real.pi/8 := by
    have hms : m ∉ s := by
      simp only [s,Finset.mem_Icc]
      omega
    simp [c,R,hms]
  have hcReal (m : ℤ) : (c m).im = 0 := by
    by_cases hms : m ∈ s
    · simpa only [c,if_pos hms] using hcheadReal m
    · simp [c,hms,Complex.mul_im]
  refine ⟨K,V,hVopen,hφV,c,R,hcReal,htailChoice,?_⟩
  intro ψ hψ m
  by_cases hms : m ∈ s
  · have hψhead : ψ ∈ Vhead m := by
      have hv : ψ ∈ Vheads := hψ.2
      simp only [Vheads,Set.mem_iInter] at hv
      exact hv m hms
    have hdata := hhead m ψ hψhead
    simpa only [c,R,if_pos hms] using
      ⟨hRhead m,hdata.1,hdata.2.1,hdata.2.2⟩
  · have hmK : K ≤ m.natAbs := by
      simp only [s,Finset.mem_Icc] at hms
      omega
    obtain ⟨hseg,hdom,_,_,_⟩ := htail ψ hψ.1 m hmK
    have hroot : sphere ((Real.pi : ℂ)*m) (Real.pi/8) ⊆
        sourceCanonicalRootDomain hp hp1 ψ :=
      sourceCanonicalRootDomain_of_enclosingCircle
        hp hp1 ψ m ((Real.pi : ℂ)*m) (Real.pi/8) hseg hdom
    simpa only [c,R,if_neg hms] using
      ⟨(by positivity : 0 < Real.pi/8),hseg,hdom,hroot⟩

/-- All selected circles can be chosen inside one fixed family of
pairwise disjoint isolating discs. The free-centered tail circles and
finitely many head circles share one complex source neighborhood. -/
theorem exists_local_sourcePsi_allGap_realCenteredContourFamily_with_isolatingDiscs
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ N : ℕ, ∃ ε : ℝ, 0 < ε ∧ ε ≤ Real.pi/4 ∧
      ∃ K : ℕ, ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
        ∃ c : ℤ → ℂ, ∃ R : ℤ → ℝ,
          (∀ m : ℤ, (c m).im = 0) ∧
          (∀ m : ℤ, K < m.natAbs →
            c m = (Real.pi : ℂ)*m ∧ R m = Real.pi/8) ∧
          (∀ ψ ∈ V, ∀ m : ℤ,
            sourceSpectralCluster hp hp1 ψ m ⊆
              sourceIsolatingDisc hp hp1 φ N ε m) ∧
          (∀ i j : ℤ, i ≠ j →
            Disjoint (sourceIsolatingDisc hp hp1 φ N ε i)
              (sourceIsolatingDisc hp hp1 φ N ε j)) ∧
          (∀ m : ℤ, closedBall (c m) (R m) ⊆
            sourceIsolatingDisc hp hp1 φ N ε m) ∧
          ∀ ψ ∈ V, ∀ m : ℤ,
            0 < R m ∧
            sourcePeriodicSegment hp hp1 ψ m ⊆ ball (c m) (R m) ∧
            closedBall (c m) (R m) ⊆
              sourceStandardRootOmittedDomain hp hp1 ψ m ∧
            sphere (c m) (R m) ⊆
              sourceCanonicalRootDomain hp hp1 ψ := by
  obtain ⟨N,ε,hε,hεmax,Uiso,hUisoOpen,_,hφiso,hcluster,hdisjoint⟩ :=
    exists_local_source_connected_isolating_discs hp hp1 φ hφ
  obtain ⟨K₀,Vtail,hVtailOpen,hφVtail,htail⟩ :=
    exists_local_sourceNormalizedAction_uniform_tail_circle_data
      hp hp1 φ hφ
  let K : ℕ := max K₀ (N+1)
  have hlocal (m : ℤ) :
      ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧ V ⊆ Uiso ∧
        ∃ c : ℂ, ∃ R : ℝ, c.im = 0 ∧ 0 < R ∧
          closedBall c R ⊆ sourceIsolatingDisc hp hp1 φ N ε m ∧
          ∀ ψ ∈ V,
            sourcePeriodicSegment hp hp1 ψ m ⊆ ball c R ∧
            closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 ψ m ∧
            sphere c R ⊆ sourceCanonicalRootDomain hp hp1 ψ :=
    exists_local_sourceCriticalRootRatio_uniformRealCenteredEnclosingCircle_of_isolatingDiscs
      hp hp1 φ hφ N ε Uiso hUisoOpen hφiso hcluster hdisjoint m
  choose Vhead hVheadOpen hφVhead hVheadSub chead Rhead hcheadReal
    hRhead hfilledHead hhead using hlocal
  let s : Finset ℤ := Finset.Icc (-(K : ℤ)) (K : ℤ)
  let Vheads : Set (CoeffPair p) := ⋂ m ∈ s, Vhead m
  have hVheadsOpen : IsOpen Vheads :=
    isOpen_biInter_finset (fun m _ => hVheadOpen m)
  have hφVheads : φ ∈ Vheads := by
    simp only [Vheads,Set.mem_iInter]
    intro m _
    exact hφVhead m
  let V : Set (CoeffPair p) := (Vtail ∩ Uiso) ∩ Vheads
  have hVopen : IsOpen V :=
    (hVtailOpen.inter hUisoOpen).inter hVheadsOpen
  have hφV : φ ∈ V := ⟨⟨hφVtail,hφiso⟩,hφVheads⟩
  let c : ℤ → ℂ := fun m =>
    if m ∈ s then chead m else (Real.pi : ℂ)*m
  let R : ℤ → ℝ := fun m =>
    if m ∈ s then Rhead m else Real.pi/8
  have htailChoice (m : ℤ) (hm : K < m.natAbs) :
      c m = (Real.pi : ℂ)*m ∧ R m = Real.pi/8 := by
    have hms : m ∉ s := by
      simp only [s,Finset.mem_Icc]
      omega
    simp [c,R,hms]
  have hcReal (m : ℤ) : (c m).im = 0 := by
    by_cases hms : m ∈ s
    · simpa only [c,if_pos hms] using hcheadReal m
    · simp [c,hms,Complex.mul_im]
  have hfilled (m : ℤ) :
      closedBall (c m) (R m) ⊆
        sourceIsolatingDisc hp hp1 φ N ε m := by
    by_cases hms : m ∈ s
    · simpa only [c,R,if_pos hms] using hfilledHead m
    · have hmK : K < m.natAbs := by
        simp only [s,Finset.mem_Icc] at hms
        omega
      have hnN : N < m.natAbs := by dsimp [K] at hmK; omega
      have hsmall : Real.pi/8 < Real.pi/4 := by
        nlinarith [Real.pi_pos]
      simpa only [c,R,if_neg hms,sourceIsolatingDisc,
        if_neg (not_le.mpr hnN),refinedResonantDisk] using
        (Metric.closedBall_subset_ball hsmall :
          closedBall ((Real.pi : ℂ)*m) (Real.pi/8) ⊆
            ball ((Real.pi : ℂ)*m) (Real.pi/4))
  refine ⟨N,ε,hε,hεmax,K,V,hVopen,hφV,c,R,hcReal,htailChoice,
    (fun ψ hψ m => hcluster ψ hψ.1.2 m),hdisjoint,hfilled,?_⟩
  intro ψ hψ m
  by_cases hms : m ∈ s
  · have hψhead : ψ ∈ Vhead m := by
      have hv : ψ ∈ Vheads := hψ.2
      simp only [Vheads,Set.mem_iInter] at hv
      exact hv m hms
    have hdata := hhead m ψ hψhead
    simpa only [c,R,if_pos hms] using
      ⟨hRhead m,hdata.1,hdata.2.1,hdata.2.2⟩
  · have hmK : K < m.natAbs := by
      simp only [s,Finset.mem_Icc] at hms
      omega
    have hmK₀ : K₀ ≤ m.natAbs := by dsimp [K] at hmK; omega
    obtain ⟨hseg,hdom,_,_,_⟩ := htail ψ hψ.1.1 m hmK₀
    have hroot : sphere ((Real.pi : ℂ)*m) (Real.pi/8) ⊆
        sourceCanonicalRootDomain hp hp1 ψ :=
      sourceCanonicalRootDomain_of_enclosingCircle
        hp hp1 ψ m ((Real.pi : ℂ)*m) (Real.pi/8) hseg hdom
    simpa only [c,R,if_neg hms] using
      ⟨(by positivity : 0 < Real.pi/8),hseg,hdom,hroot⟩

/-- Near any real-type source, one family of circles encloses every
periodic gap and avoids every other gap. -/
theorem exists_local_sourcePsi_allGap_contourFamily
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ K : ℕ, ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∃ c : ℤ → ℂ, ∃ R : ℤ → ℝ,
        (∀ m : ℤ, K < m.natAbs →
          c m = (Real.pi : ℂ)*m ∧ R m = Real.pi/8) ∧
        ∀ ψ ∈ V, ∀ m : ℤ,
          0 < R m ∧
          sourcePeriodicSegment hp hp1 ψ m ⊆ ball (c m) (R m) ∧
          closedBall (c m) (R m) ⊆
            sourceStandardRootOmittedDomain hp hp1 ψ m ∧
          sphere (c m) (R m) ⊆
            sourceCanonicalRootDomain hp hp1 ψ := by
  obtain ⟨K,V,hVopen,hφV,c,R,_,htail,hdata⟩ :=
    exists_local_sourcePsi_allGap_realCenteredContourFamily hp hp1 φ hφ
  exact ⟨K,V,hVopen,hφV,c,R,htail,hdata⟩

end NLS.ZakharovShabat
