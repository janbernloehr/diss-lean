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
  obtain ⟨K,Vtail,hVtailOpen,hφVtail,htail⟩ :=
    exists_local_sourceNormalizedAction_uniform_tail_circle_data
      hp hp1 φ hφ
  have hlocal (m : ℤ) :
      ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
        ∃ c : ℂ, ∃ R : ℝ, 0 < R ∧
          ∀ ψ ∈ V,
            sourcePeriodicSegment hp hp1 ψ m ⊆ ball c R ∧
            closedBall c R ⊆
              sourceStandardRootOmittedDomain hp hp1 ψ m ∧
            sphere c R ⊆ sourceCanonicalRootDomain hp hp1 ψ :=
    exists_local_sourceCriticalRootRatio_uniformEnclosingCircle
      hp hp1 φ hφ m
  choose Vhead hVheadOpen hφVhead chead Rhead hRhead hhead using hlocal
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
  refine ⟨K,V,hVopen,hφV,c,R,htailChoice,?_⟩
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

end NLS.ZakharovShabat
