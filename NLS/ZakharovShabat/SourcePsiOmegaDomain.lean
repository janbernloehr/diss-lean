import NLS.ZakharovShabat.SourcePsiGapRootAnalyticExistence
import NLS.ZakharovShabat.SourceCriticalRootRatioTransverseBound
import NLS.ZakharovShabat.SourcePsiGapRootTailBound
import NLS.SequenceSpaces.DeletedRealImag

/-!
# Real deleted roots and the local psi placement domain

The source analogue of the domain `Ωᵖ` in Proposition 12.9 uses
real deleted-root coordinates. Its local isolating neighborhoods are
represented here by the source isolating discs. The omitted coordinate
may be filled with a point in its assigned disc.
-/

noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Deleted coefficient vectors whose retained coordinates are real. -/
def realDeletedCoeffSubmodule
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (n : ℤ) :
    Submodule ℝ (DeletedCoeff p n) where
  carrier := {a | ∀ m : ℤ, ((a : Coeff p) m).im = 0}
  zero_mem' := by
    intro m
    simp
  add_mem' := by
    intro a b ha hb m
    change (((a : Coeff p) m + (b : Coeff p) m)).im = 0
    simp [ha m, hb m]
  smul_mem' := by
    intro r a ha m
    change ((r • ((a : Coeff p) m))).im = 0
    simp [ha m]

/-- The real deleted-root space is a closed Banach subspace. -/
theorem isClosed_realDeletedCoeffSubmodule
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (n : ℤ) :
    IsClosed (realDeletedCoeffSubmodule p n : Set (DeletedCoeff p n)) := by
  have hcoord (m : ℤ) : IsClosed
      {a : DeletedCoeff p n | ((a : Coeff p) m).im = 0} := by
    exact isClosed_eq
      (Complex.continuous_im.comp
        ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) p m).continuous.comp
          continuous_subtype_val)) continuous_const
  have hset : (realDeletedCoeffSubmodule p n : Set (DeletedCoeff p n)) =
      ⋂ m : ℤ, {a : DeletedCoeff p n | ((a : Coeff p) m).im = 0} := by
    ext a
    simp only [SetLike.mem_coe, Set.mem_iInter, Set.mem_ofPred_eq]
    rfl
  rw [hset]
  exact isClosed_iInter hcoord

instance realDeletedCoeffSubmodule_completeSpace
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (n : ℤ) :
    CompleteSpace (realDeletedCoeffSubmodule p n) :=
  (isClosed_realDeletedCoeffSubmodule n).completeSpace_coe

/-- Real part as a bounded real-linear projection into the real
deleted-root subspace. -/
def realDeletedCoeffProjection
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (n : ℤ) :
    DeletedCoeff p n →L[ℝ] realDeletedCoeffSubmodule p n :=
  { toFun := fun a => ⟨DeletedCoeff.realPart a,
      DeletedCoeff.realPart_im_eq_zero a⟩
    map_add' := by
      intro a b
      apply Subtype.ext
      apply Subtype.ext
      ext m
      simp [DeletedCoeff.realPart_apply, Complex.add_re]
    map_smul' := by
      intro r a
      apply Subtype.ext
      apply Subtype.ext
      ext m
      simp [DeletedCoeff.realPart_apply, Complex.real_smul]
    cont := by
      have hrealPart : Continuous
          (DeletedCoeff.realPart : DeletedCoeff p n → DeletedCoeff p n) := by
        unfold DeletedCoeff.realPart
        have hsum : Continuous
            (fun a : DeletedCoeff p n => a + DeletedCoeff.conj a) :=
          continuous_id.add (DeletedCoeff.continuous_conj (p := p) (n := n))
        exact (continuous_const : Continuous
          (fun _ : DeletedCoeff p n => (1/2 : ℂ))).smul hsum
      exact hrealPart.subtype_mk _ }

theorem realDeletedCoeffProjection_eq_self
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (n : ℤ)
    (a : realDeletedCoeffSubmodule p n) :
    realDeletedCoeffProjection n (a : DeletedCoeff p n) = a := by
  apply Subtype.ext
  change DeletedCoeff.realPart (a : DeletedCoeff p n) = (a : DeletedCoeff p n)
  apply Subtype.ext
  ext m
  change ((DeletedCoeff.realPart (a : DeletedCoeff p n) : Coeff p) m) =
    ((a : DeletedCoeff p n) : Coeff p) m
  rw [DeletedCoeff.realPart_apply]
  have him : (((a : DeletedCoeff p n) : Coeff p) m).im = 0 := a.property m
  simpa [him] using
    (Complex.re_add_im (((a : DeletedCoeff p n) : Coeff p) m))

/-- Every canonical selected root has a real displacement. -/
theorem sourcePsiGapRoot_mem_realDeletedCoeffSubmodule
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (φ : realTypeSourceSubmodule p) :
    sourcePsiGapRoot hp hp1 n φ ∈ realDeletedCoeffSubmodule p n := by
  intro m
  by_cases hmn : m = n
  · subst m
    simp [show (sourcePsiGapRoot hp hp1 n φ : Coeff p) n = 0 from
      (sourcePsiGapRoot hp hp1 n φ).property]
  · have hreal := sourcePeriodicSegment_im_eq_zero_of_realType
      hp hp1 (φ : CoeffPair p) φ.property m _
        (sourcePsiGapRoot_mem_periodicSegment hp hp1 n m hmn φ)
    have hfree : (((Real.pi : ℂ) * m)).im = 0 := by simp
    have hroot : displacedRoots
        (sourcePsiGapRoot hp hp1 n φ : Coeff p) m =
          (Real.pi : ℂ) * m +
            (sourcePsiGapRoot hp hp1 n φ : Coeff p) m := rfl
    rw [hroot] at hreal
    simpa [Complex.add_im, hfree] using hreal

/-- The canonical deleted-root map with its real codomain. -/
def sourcePsiGapRootReal
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (φ : realTypeSourceSubmodule p) :
    realDeletedCoeffSubmodule p n :=
  ⟨sourcePsiGapRoot hp hp1 n φ,
    sourcePsiGapRoot_mem_realDeletedCoeffSubmodule hp hp1 n φ⟩

/-- Analyticity of the canonical gap roots with the real deleted-root
Banach space as codomain. -/
theorem analyticOnNhd_sourcePsiGapRootReal
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) :
    AnalyticOnNhd ℝ (sourcePsiGapRootReal hp hp1 n) univ := by
  intro φ _
  have hproj : AnalyticAt ℝ (realDeletedCoeffProjection (p := p) n)
      (sourcePsiGapRoot hp hp1 n φ) := by
    apply ContinuousLinearMap.analyticAt
  have hcomp : AnalyticAt ℝ
      (fun ψ : realTypeSourceSubmodule p =>
        realDeletedCoeffProjection (p := p) n (sourcePsiGapRoot hp hp1 n ψ)) φ :=
    hproj.comp (analyticAt_sourcePsiGapRoot_real hp hp1 n φ)
  have heq : (fun ψ : realTypeSourceSubmodule p =>
      realDeletedCoeffProjection (p := p) n (sourcePsiGapRoot hp hp1 n ψ)) =
      sourcePsiGapRootReal hp hp1 n := by
    funext ψ
    exact realDeletedCoeffProjection_eq_self n (sourcePsiGapRootReal hp hp1 n ψ)
  exact heq ▸ hcomp

/-- The local real psi domain: retained roots lie in their assigned
discs and the omitted root can be filled inside its own disc. -/
def sourcePsiOmegaLocal
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (N : ℕ) (ε : ℝ) (n : ℤ)
    (U : Set (CoeffPair p)) :
    Set (realDeletedCoeffSubmodule p n × realTypeSourceSubmodule p) :=
  {t | (t.2 : CoeffPair p) ∈ U ∧
    ∃ ξ : ℂ, ξ.im = 0 ∧ ∀ m : ℤ,
      displacedRoots (sourcePsiFillDeletedRoot n (t.1 : DeletedCoeff p n) ξ) m ∈
        sourceIsolatingDisc hp hp1 φ N ε m}

/-- The real psi domain is open in the real source and real deleted-root
spaces. A witness for the omitted root remains valid when the retained
coordinates and source vary inside their open conditions. -/
theorem isOpen_sourcePsiOmegaLocal
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (N : ℕ) (ε : ℝ) (n : ℤ)
    (U : Set (CoeffPair p)) (hU : IsOpen U) :
    IsOpen (sourcePsiOmegaLocal hp hp1 φ N ε n U) := by
  let V : Set (realDeletedCoeffSubmodule p n × realTypeSourceSubmodule p) :=
    {t | (t.2 : CoeffPair p) ∈ U ∧
      (t.1 : DeletedCoeff p n) ∈ sourcePsiRootPlacementSet hp hp1 φ N ε n}
  have hVopen : IsOpen V := by
    exact (hU.preimage (continuous_subtype_val.comp continuous_snd)).inter
      ((isOpen_sourcePsiRootPlacementSet hp hp1 φ N ε n).preimage
        (continuous_subtype_val.comp continuous_fst))
  apply isOpen_iff_mem_nhds.mpr
  intro t ht
  obtain ⟨htU,ξ,hξReal,hξ⟩ := ht
  have htV : t ∈ V := by
    refine ⟨htU,?_⟩
    intro m hmn
    simpa only [displacedRoots_sourcePsiFillDeletedRoot_other n m hmn]
      using hξ m
  have hVsub : V ⊆ sourcePsiOmegaLocal hp hp1 φ N ε n U := by
    intro u hu
    refine ⟨hu.1,ξ,hξReal,?_⟩
    intro m
    by_cases hmn : m = n
    · subst m
      simpa only [displacedRoots_sourcePsiFillDeletedRoot_same] using hξ n
    · simpa only [displacedRoots_sourcePsiFillDeletedRoot_other n m hmn]
        using hu.2 m hmn
  exact mem_of_superset (hVopen.mem_nhds htV) hVsub

/-- One open real-source neighborhood places the graphs of all
canonical deleted-index solutions in their local real psi domains,
including each filled omitted coordinate. -/
theorem exists_local_graph_sourcePsiOmegaLocal_allIndices
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) :
    ∃ N : ℕ, ∃ ε : ℝ, 0 < ε ∧ ε ≤ Real.pi/4 ∧
      ∃ U : Set (CoeffPair p), IsOpen U ∧ (φ : CoeffPair p) ∈ U ∧
        ∀ n : ℤ, ∀ ψ : realTypeSourceSubmodule p, (ψ : CoeffPair p) ∈ U →
          (sourcePsiGapRootReal hp hp1 n ψ,ψ) ∈
            sourcePsiOmegaLocal hp hp1 (φ : CoeffPair p) N ε n U := by
  obtain ⟨N,ε,hε,hεmax,U,hUopen,hφU,hplacement⟩ :=
    exists_local_graph_filledRootPlacement_sourcePsiGapRoot_allIndices hp hp1 φ
  refine ⟨N,ε,hε,hεmax,U,hUopen,hφU,?_⟩
  intro n ψ hψ
  obtain ⟨ξ,hξSeg,hξ⟩ := hplacement n ψ hψ
  exact ⟨hψ,ξ,
    sourcePeriodicSegment_im_eq_zero_of_realType hp hp1
      (ψ : CoeffPair p) ψ.property n ξ hξSeg,hξ⟩

/-- The simultaneous local-domain theorem for a fixed deleted index. -/
theorem exists_local_graph_sourcePsiOmegaLocal
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (φ : realTypeSourceSubmodule p) :
    ∃ N : ℕ, ∃ ε : ℝ, 0 < ε ∧ ε ≤ Real.pi/4 ∧
      ∃ U : Set (CoeffPair p), IsOpen U ∧ (φ : CoeffPair p) ∈ U ∧
        ∀ ψ : realTypeSourceSubmodule p, (ψ : CoeffPair p) ∈ U →
          (sourcePsiGapRootReal hp hp1 n ψ,ψ) ∈
            sourcePsiOmegaLocal hp hp1 (φ : CoeffPair p) N ε n U := by
  obtain ⟨N,ε,hε,hεmax,U,hUopen,hφU,hplace⟩ :=
    exists_local_graph_sourcePsiOmegaLocal_allIndices hp hp1 φ
  exact ⟨N,ε,hε,hεmax,U,hUopen,hφU,hplace n⟩

/-- The all-index local placement and compactness estimates hold on
one real-source neighborhood. Both the isolating family and the tail
cutoff are independent of the deleted index. -/
theorem exists_local_allIndices_sourcePsiOmega_uniformTails
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) {δ : ℝ} (hδ : 0 < δ) :
    ∃ Niso : ℕ, ∃ εiso : ℝ,
      0 < εiso ∧ εiso ≤ Real.pi/4 ∧
      ∃ K : ℕ, ∃ U : Set (CoeffPair p),
        IsOpen U ∧ (φ : CoeffPair p) ∈ U ∧
        ∀ n : ℤ, ∀ ψ : realTypeSourceSubmodule p,
          (ψ : CoeffPair p) ∈ U →
          (sourcePsiGapRootReal hp hp1 n ψ,ψ) ∈
            sourcePsiOmegaLocal hp hp1 (φ : CoeffPair p) Niso εiso n U ∧
          ∀ M : ℕ, K ≤ M →
            ‖(sourcePsiGapRoot hp hp1 n ψ : Coeff p) -
              Coeff.truncate (Finset.Icc (-(M : ℤ)) M)
                (sourcePsiGapRoot hp hp1 n ψ : Coeff p)‖ ≤ δ := by
  obtain ⟨Niso,εiso,hεiso,hεisomax,U₀,hU₀open,hφU₀,hplace⟩ :=
    exists_local_graph_sourcePsiOmegaLocal_allIndices hp hp1 φ
  obtain ⟨K,V,hVopen,hφV,htail⟩ :=
    exists_uniform_small_deletedGapRoots_tails_allIndices
      hp hp1 (φ : CoeffPair p) hδ
  let U := U₀ ∩ V
  refine ⟨Niso,εiso,hεiso,hεisomax,K,U,
    hU₀open.inter hVopen,⟨hφU₀,hφV⟩,?_⟩
  intro n ψ hψ
  obtain ⟨_,ξ,hξReal,hξPlace⟩ := hplace n ψ hψ.1
  refine ⟨⟨hψ,ξ,hξReal,hξPlace⟩,?_⟩
  intro M hM
  exact htail (ψ : CoeffPair p) hψ.2 n
    (sourcePsiGapRoot hp hp1 n ψ)
    (fun m hmn => sourcePsiGapRoot_mem_periodicSegment hp hp1 n m hmn ψ)
    M hM

/-- Source analogue of Proposition 12.9: the unique real-analytic
gap-contained solution solves the selected psi equation, and its graph
locally belongs to an open real placement domain with every index
filled. -/
theorem existsUnique_analytic_sourcePsiGapRootReal_localOmega
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) :
    ∃! s : realTypeSourceSubmodule p → realDeletedCoeffSubmodule p n,
      AnalyticOnNhd ℝ s univ ∧
      (∀ φ : realTypeSourceSubmodule p,
        SourcePsiGapSolution hp hp1 n (φ : CoeffPair p)
          (s φ : DeletedCoeff p n)) ∧
      ∀ φ : realTypeSourceSubmodule p,
        ∃ N : ℕ, ∃ ε : ℝ, 0 < ε ∧ ε ≤ Real.pi/4 ∧
          ∃ U : Set (CoeffPair p), IsOpen U ∧ (φ : CoeffPair p) ∈ U ∧
            ∀ ψ : realTypeSourceSubmodule p, (ψ : CoeffPair p) ∈ U →
              (s ψ,ψ) ∈ sourcePsiOmegaLocal hp hp1
                (φ : CoeffPair p) N ε n U := by
  refine ⟨sourcePsiGapRootReal hp hp1 n,?_,?_⟩
  · exact ⟨analyticOnNhd_sourcePsiGapRootReal hp hp1 n,
      fun φ => sourcePsiGapRoot_solution hp hp1 n φ,
      exists_local_graph_sourcePsiOmegaLocal hp hp1 n⟩
  · intro s hs
    funext φ
    apply Subtype.ext
    exact SourcePsiGapSolution.eq_sourcePsiGapRoot hp hp1 n φ
      (s φ : DeletedCoeff p n) (hs.2.1 φ)

end NLS.ZakharovShabat
