import NLS.ZakharovShabat.SourcePsiRootPlacementDomain
import NLS.ZakharovShabat.SourcePsiGapProductCompact

/-!
# A common isolating-disc margin for the full gap product

The full root-placement set is open: one fixed coordinate and its
deleted projection reduce the claim to the already open deleted-root
placement set. Compactness of the full gap product then supplies a
single positive perturbation radius about every gap-contained vector.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def sourcePsiFullRootPlacementSet (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (N : ℕ) (ε : ℝ) : Set (Coeff p) :=
  {a | ∀ m : ℤ, displacedRoots a m ∈ sourceIsolatingDisc hp hp1 φ N ε m}

theorem isOpen_sourcePsiFullRootPlacementSet (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (N : ℕ) (ε : ℝ) :
    IsOpen (sourcePsiFullRootPlacementSet hp hp1 φ N ε) := by
  have hdelete (a : Coeff p) (m : ℤ) (hm : m ≠ 0) :
      displacedRoots ((Coeff.deleteCoordinateTo 0 a : DeletedCoeff p 0) : Coeff p) m =
        displacedRoots a m := by
    change (Real.pi : ℂ)*m+Coeff.deleteCoordinate 0 a m = (Real.pi : ℂ)*m+a m
    rw [Coeff.deleteCoordinate_apply_other 0 m hm]
  have hset : sourcePsiFullRootPlacementSet hp hp1 φ N ε =
      (Coeff.deleteCoordinateTo 0) ⁻¹' sourcePsiRootPlacementSet hp hp1 φ N ε 0 ∩
        (fun a : Coeff p => displacedRoots a 0) ⁻¹' sourceIsolatingDisc hp hp1 φ N ε 0 := by
    ext a
    constructor
    · intro ha
      refine ⟨?_,ha 0⟩
      intro m hm
      rw [hdelete a m hm]
      exact ha m
    · intro ha m
      by_cases hm : m = 0
      · subst m
        exact ha.2
      · have h := ha.1 m hm
        rw [hdelete a m hm] at h
        exact h
  have hcoord : Continuous (fun a : Coeff p => displacedRoots a 0) := by
    have heval : Continuous (fun a : Coeff p => a 0) :=
      (lp.lipschitzWith_one_eval p (0 : ℤ)).continuous
    simpa [displacedRoots] using heval
  rw [hset]
  exact ((isOpen_sourcePsiRootPlacementSet hp hp1 φ N ε 0).preimage
    (Coeff.deleteCoordinateTo 0).continuous).inter
      ((isOpen_sourceIsolatingDisc hp hp1 φ N ε 0).preimage hcoord)

theorem exists_uniform_fullRootPlacement_radius (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (N : ℕ) (ε : ℝ)
    (hgap : ∀ m : ℤ, sourcePeriodicSegment hp hp1 φ m ⊆ sourceIsolatingDisc hp hp1 φ N ε m) :
    ∃ μ : ℝ, 0 < μ ∧ ∀ a ∈ sourcePeriodicGapRootSet hp hp1 φ,
      ball a μ ⊆ sourcePsiFullRootPlacementSet hp hp1 φ N ε := by
  have hsub : sourcePeriodicGapRootSet hp hp1 φ ⊆ sourcePsiFullRootPlacementSet hp hp1 φ N ε :=
    fun a ha m => hgap m (ha m)
  obtain ⟨μ,hμ,hthick⟩ := (isCompact_sourcePeriodicGapRootSet hp hp1 φ).exists_cthickening_subset_open
    (isOpen_sourcePsiFullRootPlacementSet hp hp1 φ N ε) hsub
  refine ⟨μ,hμ,?_⟩
  intro a ha b hb
  exact hthick (mem_cthickening_of_dist_le b a μ (sourcePeriodicGapRootSet hp hp1 φ)
    ha (mem_ball.mp hb).le)

end NLS.ZakharovShabat
