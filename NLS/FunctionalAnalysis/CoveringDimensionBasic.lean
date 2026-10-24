import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Data.Finset.Card

/-! # Finite open covers and covering-dimension bounds

We use the finite-open-refinement definition of Lebesgue covering dimension
(Engelking, Dimension Theory, Definition 1.6.7). On normal spaces,
`HasCoveringDimensionLE X n` is the standard assertion `dim X ≤ n`.
Every refinement in the definition covers the whole space, and its
multiplicity counts the indices containing each point. No dimension
conclusion is inferred merely from a failure of local contractibility.
-/
noncomputable section
open Set
namespace NLS.FunctionalAnalysis
universe u v
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- A finite indexed open cover, including the possibility of an empty index set. -/
structure FiniteOpenCover (X : Type u) [TopologicalSpace X] where
  count : ℕ
  sets : Fin count → Set X
  isOpen : ∀ i, IsOpen (sets i)
  covers : ∀ x, ∃ i, x ∈ sets i

namespace FiniteOpenCover

/-- The number of members of a finite cover containing a given point. -/
def multiplicity (U : FiniteOpenCover X) (x : X) : ℕ := by
  classical
  exact (Finset.univ.filter (fun i => x ∈ U.sets i)).card

/-- Each member of the refining cover is contained in some member of the original. -/
def Refines (V U : FiniteOpenCover X) : Prop :=
  ∀ j, ∃ i, V.sets j ⊆ U.sets i

theorem Refines.refl (U : FiniteOpenCover X) : U.Refines U := fun i => ⟨i,Subset.rfl⟩

theorem Refines.trans {W V U : FiniteOpenCover X}
    (hWV : W.Refines V) (hVU : V.Refines U) : W.Refines U := by
  intro k
  obtain ⟨j,hj⟩ := hWV k
  obtain ⟨i,hi⟩ := hVU j
  exact ⟨i,hj.trans hi⟩

/-- Pull back a finite open cover along a continuous map. -/
def comap (U : FiniteOpenCover Y) (f : X → Y) (hf : Continuous f) : FiniteOpenCover X where
  count := U.count
  sets i := f ⁻¹' U.sets i
  isOpen i := (U.isOpen i).preimage hf
  covers x := U.covers (f x)

theorem multiplicity_comap (U : FiniteOpenCover Y) (f : X → Y) (hf : Continuous f) (x : X) :
    (U.comap f hf).multiplicity x = U.multiplicity (f x) := rfl

theorem Refines.comap {V U : FiniteOpenCover Y} (h : V.Refines U)
    (f : X → Y) (hf : Continuous f) : (V.comap f hf).Refines (U.comap f hf) := by
  intro j
  obtain ⟨i,hi⟩ := h j
  exact ⟨i,preimage_mono hi⟩

/-- The empty cover of an empty space. -/
def empty [IsEmpty X] : FiniteOpenCover X where
  count := 0
  sets := Fin.elim0
  isOpen i := Fin.elim0 i
  covers x := isEmptyElim x

end FiniteOpenCover

/-- Every finite open cover has a finite open refinement of multiplicity at most `n + 1`.
This is the usual nonnegative covering-dimension bound on normal spaces. -/
def HasCoveringDimensionLE (X : Type u) [TopologicalSpace X] (n : ℕ) : Prop :=
  ∀ U : FiniteOpenCover X, ∃ V : FiniteOpenCover X,
    V.Refines U ∧ ∀ x, V.multiplicity x ≤ n + 1

theorem HasCoveringDimensionLE.mono {m n : ℕ} (hmn : m ≤ n)
    (h : HasCoveringDimensionLE X m) : HasCoveringDimensionLE X n := by
  intro U
  obtain ⟨V,hVU,hV⟩ := h U
  exact ⟨V,hVU,fun x => (hV x).trans (Nat.add_le_add_right hmn 1)⟩

theorem hasCoveringDimensionLE_of_isEmpty [IsEmpty X] (n : ℕ) :
    HasCoveringDimensionLE X n := by
  intro U
  exact ⟨FiniteOpenCover.empty,(fun i => Fin.elim0 i),fun x => isEmptyElim x⟩

/-- Transport a covering-dimension bound along a homeomorphism. -/
theorem HasCoveringDimensionLE.homeomorph {n : ℕ}
    (h : HasCoveringDimensionLE X n) (e : X ≃ₜ Y) : HasCoveringDimensionLE Y n := by
  intro U
  obtain ⟨V,hV,horder⟩ := h (U.comap e e.continuous)
  refine ⟨V.comap e.symm e.symm.continuous,?_,?_⟩
  · intro j
    obtain ⟨i,hi⟩ := hV j
    refine ⟨i,fun y hy => ?_⟩
    have hh := hi hy
    change e (e.symm y) ∈ U.sets i at hh
    simpa only [Homeomorph.apply_symm_apply] using hh
  · intro y
    exact horder (e.symm y)

/-- Covering-dimension bounds are unchanged under homeomorphism. -/
theorem hasCoveringDimensionLE_homeomorph_iff (e : X ≃ₜ Y) (n : ℕ) :
    HasCoveringDimensionLE X n ↔ HasCoveringDimensionLE Y n :=
  ⟨fun h => h.homeomorph e,fun h => h.homeomorph e.symm⟩

end NLS.FunctionalAnalysis
