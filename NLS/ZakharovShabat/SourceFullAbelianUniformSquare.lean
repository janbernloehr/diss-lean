import NLS.ZakharovShabat.SourceFullAbelianSquare

/-! # Square continuation on a common almost-real source neighborhood

Every normalized square is analytic across its own gap for every source
in one open connected neighborhood. The original square is preserved on
the complement of noncollapsed cuts, with exact zero endpoint values.
-/
noncomputable section
open Set Metric Filter Topology Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Lemma 19.1(iv) for the full canonical complex-source primitive.
The same source neighborhood works for all signed gap indices. -/
theorem exists_sourceFullAbelian_almostReal_uniformSquare (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W V : Set (CoeffPair p), IsOpen V ∧ IsConnected V ∧ realTypeSourceLocus p ⊆ V ∧ V ⊆ W ∧
      ∀ ψ ∈ V, ∀ n : ℤ,
        AnalyticOnNhd ℂ (fun z => sourceFullAbelianSquare hp hp1 W n (z,ψ))
          (sourceFullAbelianSquareDomain hp hp1 ψ n) ∧
        EqOn (fun z => sourceFullAbelianSquare hp hp1 W n (z,ψ))
          (fun z => (sourceFullAbelianPrimitive hp hp1 W n (z,ψ))^2) (sourceOpenGapComplement hp hp1 ψ) ∧
        ∀ a ∈ ({canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n,
          canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n} : Set ℂ),
          sourceFullAbelianSquare hp hp1 W n (a,ψ) = 0 := by
  obtain ⟨W,_,_,hfamilies⟩ := exists_sourceFullAbelianUniformCauchyFamilies hp hp1
  choose C hC using hfamilies
  let U : Set (CoeffPair p) := ⋃ φ : realTypeSourceSubmodule p, ball (C φ).discs.source.val (C φ).discs.sourceRadius
  have hU : IsOpen U := isOpen_iUnion (fun _ => isOpen_ball)
  have hrealU : realTypeSourceLocus p ⊆ U := by
    intro ψ hψ
    apply mem_iUnion.mpr
    refine ⟨⟨ψ,hψ⟩,?_⟩
    rw [hC]
    exact mem_ball_self (C ⟨ψ,hψ⟩).discs.sourceRadius_pos
  have hUW : U ⊆ W := by
    intro ψ hψ
    obtain ⟨φ,hφ⟩ := mem_iUnion.mp hψ
    exact (C φ).discs.source_subset hφ
  let V := connectedComponentIn U (0 : CoeffPair p)
  have hzero : (0 : CoeffPair p) ∈ realTypeSourceLocus p := by simp [realTypeSourceLocus]
  have hrealV : realTypeSourceLocus p ⊆ V :=
    isConnected_realTypeSourceLocus.isPreconnected.subset_connectedComponentIn hzero hrealU
  have hVU : V ⊆ U := connectedComponentIn_subset U 0
  refine ⟨W,V,hU.connectedComponentIn,isConnected_connectedComponentIn_iff.mpr (hrealU hzero),hrealV,hVU.trans hUW,?_⟩
  intro ψ hψ n
  obtain ⟨φ,hφ⟩ := mem_iUnion.mp (hVU hψ)
  obtain ⟨E⟩ := (C φ).charts ψ hφ
  exact ⟨(C φ).fullSquare_analytic n ψ hφ,sourceFullAbelianSquare_eq_sq E n,
    fun a ha => (C φ).fullSquare_endpoint n ψ hφ a ha⟩

end NLS.ZakharovShabat
