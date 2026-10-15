import NLS.ZakharovShabat.SourcePsiOriginalOmega
import NLS.SequenceSpaces.DeletedRealEquiv

/-!
# The original deleted root-placement domain

The source-first real domain records only retained roots. It is exactly
the image of the original full Omega under coordinate deletion, and is
open whenever the source neighborhood is open.
-/

noncomputable section
open Set Complex Metric Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The original real placement domain after deleting the unused coordinate. -/
def sourcePsiOriginalDeletedOmega (V : Set (CoeffPair p)) (D : ℤ → Set ℂ) (n : ℤ) :
    Set (realTypeSourceSubmodule p × RealDeletedCoeff p n) :=
  {t | (t.1:CoeffPair p) ∈ V ∧ ∀ k : ℤ, k ≠ n →
    displacedRoots (RealDeletedCoeff.complexCLM n t.2:Coeff p) k ∈ D k}

/-- The deleted original domain is open in the real product Banach space. -/
theorem SourceIsolatingNeighborhoods.isOpen_originalDeletedOmega
    {hp : p ≠ ⊤} {hp1 : 1 < p} {V : Set (CoeffPair p)} {D : ℤ → Set ℂ} {c : ℝ}
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c) (hV : IsOpen V) (n : ℤ) :
    IsOpen (sourcePsiOriginalDeletedOmega V D n) := by
  obtain ⟨d,r,hr,he⟩ := hD.discs n
  let L : RealDeletedCoeff p n →L[ℝ] Coeff p :=
    (((lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n).ker.subtypeL).restrictScalars ℝ).comp
      (RealDeletedCoeff.complexCLM n)
  let fill (a : RealDeletedCoeff p n) : Coeff p := L a + lp.single p n ((d:ℂ)-(Real.pi:ℂ)*n)
  have hsame (a : RealDeletedCoeff p n) : displacedRoots (fill a) n = (d:ℂ) := by
    change (Real.pi:ℂ)*n + ((RealDeletedCoeff.complexCLM n a:Coeff p) n +
      (lp.single p n ((d:ℂ)-(Real.pi:ℂ)*n):Coeff p) n) = (d:ℂ)
    rw [show (RealDeletedCoeff.complexCLM n a:Coeff p) n = 0 from (RealDeletedCoeff.complexCLM n a).property]
    simp
  have hother (a : RealDeletedCoeff p n) (m : ℤ) (hmn : m ≠ n) :
      displacedRoots (fill a) m = displacedRoots (RealDeletedCoeff.complexCLM n a:Coeff p) m := by
    change (Real.pi:ℂ)*m + ((RealDeletedCoeff.complexCLM n a:Coeff p) m +
      (lp.single p n ((d:ℂ)-(Real.pi:ℂ)*n):Coeff p) m) = _
    rw [lp.single_apply_ne _ _ _ hmn, add_zero]
    rfl
  have hfill : Continuous fill := L.continuous.add continuous_const
  have hset : sourcePsiOriginalDeletedOmega V D n =
      {t : realTypeSourceSubmodule p × RealDeletedCoeff p n |
        (t.1:CoeffPair p) ∈ V ∧ fill t.2 ∈ sourcePsiOriginalRootPlacement D} := by
    ext t
    constructor
    · intro ht
      refine ⟨ht.1,?_⟩
      intro m
      by_cases hmn : m = n
      · subst m
        rw [hsame,he]
        exact mem_ball_self hr
      · rw [hother t.2 m hmn]
        exact ht.2 m hmn
    · intro ht
      refine ⟨ht.1,?_⟩
      intro m hmn
      rw [← hother t.2 m hmn]
      exact ht.2 m
  rw [hset]
  exact (hV.preimage (continuous_subtype_val.comp continuous_fst)).inter
    (hD.isOpen_originalRootPlacement.preimage (hfill.comp continuous_snd))

/-- The deleted domain is exactly the projection of the full original Omega. -/
theorem SourceIsolatingNeighborhoods.mem_originalDeletedOmega_iff
    {hp : p ≠ ⊤} {hp1 : 1 < p} {V : Set (CoeffPair p)} {D : ℤ → Set ℂ} {c : ℝ}
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c) (n : ℤ)
    (t : realTypeSourceSubmodule p × RealDeletedCoeff p n) :
    t ∈ sourcePsiOriginalDeletedOmega V D n ↔
      ∃ a : RealCoeff p, (t.1,a) ∈ sourcePsiOriginalOmega V D ∧
        RealDeletedCoeff.deleteCoordinateTo n a = t.2 := by
  constructor
  · intro ht
    obtain ⟨d,r,hr,he⟩ := hD.discs n
    let a : RealCoeff p := (t.2:RealCoeff p) + lp.single p n (d-Real.pi*n)
    have hcoord (m : ℤ) (hmn : m ≠ n) :
        (RealCoeff.complexCLM p a) m = (RealDeletedCoeff.complexCLM n t.2:Coeff p) m := by
      simp [a,lp.single_apply,hmn]
    have hsame : displacedRoots (RealCoeff.complexCLM p a) n = (d:ℂ) := by
      have htn : (t.2:RealCoeff p) n = 0 := t.2.property
      simp [a,displacedRoots,htn]
    refine ⟨a,⟨ht.1,?_⟩,?_⟩
    · intro m
      by_cases hmn : m = n
      · subst m
        rw [hsame,he]
        exact mem_ball_self hr
      · change (Real.pi:ℂ)*m+(RealCoeff.complexCLM p a) m ∈ D m
        rw [hcoord m hmn]
        exact ht.2 m hmn
    · apply Subtype.ext
      ext m
      change ((Coeff.deleteCoordinate n (RealCoeff.complexCLM p a)) m).re = (t.2:RealCoeff p) m
      by_cases hmn : m = n
      · subst m
        rw [Coeff.deleteCoordinate_apply_same]
        exact t.2.property.symm
      · rw [Coeff.deleteCoordinate_apply_other n m hmn,hcoord m hmn]
        simp
  · rintro ⟨a,ha,hdel⟩
    refine ⟨ha.1,?_⟩
    intro m hmn
    rw [← hdel, RealDeletedCoeff.complex_deleteCoordinateTo]
    change (Real.pi:ℂ)*m+(Coeff.deleteCoordinate n (RealCoeff.complexCLM p a)) m ∈ D m
    rw [Coeff.deleteCoordinate_apply_other n m hmn]
    exact ha.2 m

end NLS.ZakharovShabat
