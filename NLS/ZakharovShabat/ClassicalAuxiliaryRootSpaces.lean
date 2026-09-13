import NLS.ZakharovShabat.ClassicalAuxiliaryClosed
import NLS.ZakharovShabat.ClassicalIntervalRootSpaces

/-!
# Generalized root spaces of the original physical auxiliary operator

The recursion uses the actual physical auxiliary pencil and inclusion, requiring
the original auxiliary H¹ domain at each chain step. The physical phase maps
identify every finite chain and the full generalized eigenspace with the ordinary
physical problem at the transformed potential.
-/

noncomputable section
namespace NLS.ZakharovShabat.BoundaryCondition

/-- Actual physical auxiliary root chains, with domain membership at every application. -/
def classicalAuxiliaryRootSpace (b : BoundaryCondition) (u : IntervalPairL2) (z : ℂ) :
    ℕ → Submodule ℂ IntervalPairL2
  | 0 => ⊥
  | n + 1 => ((classicalAuxiliaryRootSpace b u z n).comap (classicalAuxiliaryPencil b u z).toLinearMap).map
      (classicalAuxiliaryInclusion b).toLinearMap

@[simp] theorem classicalAuxiliaryRootSpace_zero (b : BoundaryCondition) (u : IntervalPairL2) (z : ℂ) :
    classicalAuxiliaryRootSpace b u z 0 = ⊥ := rfl

theorem mem_classicalAuxiliaryRootSpace_succ (b : BoundaryCondition) (u : IntervalPairL2) (z : ℂ) (n : ℕ)
    (x : IntervalPairL2) : x ∈ classicalAuxiliaryRootSpace b u z (n + 1) ↔
      ∃ f : ClassicalAuxiliaryDomain b, classicalAuxiliaryInclusion b f = x ∧
        classicalAuxiliaryPencil b u z f ∈ classicalAuxiliaryRootSpace b u z n := by
  simp only [classicalAuxiliaryRootSpace, Submodule.mem_map, Submodule.mem_comap]
  exact exists_congr fun _ => and_comm

/-- Level one is the actual included physical eigenspace. -/
theorem classicalAuxiliaryRootSpace_one (b : BoundaryCondition) (u : IntervalPairL2) (z : ℂ) :
    classicalAuxiliaryRootSpace b u z 1 =
      (classicalAuxiliaryPencil b u z).ker.map (classicalAuxiliaryInclusion b).toLinearMap := rfl

/-- Phase conjugation preserves every finite physical generalized root chain. -/
theorem mem_classicalAuxiliaryRootSpace_phase (b : BoundaryCondition) (u : IntervalPairL2) (z : ℂ)
    (n : ℕ) (x : IntervalPairL2) :
    intervalAuxiliaryPhase x ∈ classicalAuxiliaryRootSpace b u z n ↔
      x ∈ classicalRootSpace b (intervalAuxiliaryPotential u) z n := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [mem_classicalAuxiliaryRootSpace_succ, mem_classicalRootSpace_succ]
    constructor
    · rintro ⟨f, hf, hn⟩
      obtain ⟨g, rfl⟩ := (classicalAuxiliaryDomainPhase b).surjective f
      rw [classicalAuxiliaryInclusion_phase] at hf
      rw [classicalAuxiliaryPencil_phase] at hn
      exact ⟨g, intervalAuxiliaryPhase.injective hf, (ih _).mp hn⟩
    · rintro ⟨f, hf, hn⟩
      refine ⟨classicalAuxiliaryDomainPhase b f, ?_, ?_⟩
      · rw [classicalAuxiliaryInclusion_phase, hf]
      · rw [classicalAuxiliaryPencil_phase]
        exact (ih _).mpr hn

theorem classicalAuxiliaryRootSpace_mono (b : BoundaryCondition) (u : IntervalPairL2) (z : ℂ) :
    Monotone (classicalAuxiliaryRootSpace b u z) := by
  apply monotone_nat_of_le_succ
  intro n
  induction n with
  | zero => exact bot_le
  | succ n ih => exact Submodule.map_mono (Submodule.comap_mono ih)

/-- The actual full physical generalized eigenspace. -/
def classicalAuxiliaryRootSpaceTop (b : BoundaryCondition) (u : IntervalPairL2) (z : ℂ) : Submodule ℂ IntervalPairL2 :=
  ⨆ n : ℕ, classicalAuxiliaryRootSpace b u z n

theorem mem_classicalAuxiliaryRootSpaceTop (b : BoundaryCondition) (u : IntervalPairL2) (z : ℂ) (x : IntervalPairL2) :
    x ∈ classicalAuxiliaryRootSpaceTop b u z ↔ ∃ n, x ∈ classicalAuxiliaryRootSpace b u z n :=
  Submodule.mem_iSup_of_directed _ (classicalAuxiliaryRootSpace_mono b u z).directed_le

theorem mem_classicalAuxiliaryRootSpaceTop_phase (b : BoundaryCondition) (u : IntervalPairL2) (z : ℂ)
    (x : IntervalPairL2) : intervalAuxiliaryPhase x ∈ classicalAuxiliaryRootSpaceTop b u z ↔
      x ∈ classicalRootSpaceTop b (intervalAuxiliaryPotential u) z := by
  simp only [mem_classicalAuxiliaryRootSpaceTop, mem_classicalRootSpaceTop, mem_classicalAuxiliaryRootSpace_phase]

theorem map_classicalRootSpaceTop_auxiliary (b : BoundaryCondition) (u : IntervalPairL2) (z : ℂ) :
    (classicalRootSpaceTop b (intervalAuxiliaryPotential u) z).map intervalAuxiliaryPhase.toLinearEquiv.toLinearMap =
      classicalAuxiliaryRootSpaceTop b u z := by
  ext x
  obtain ⟨y, rfl⟩ := intervalAuxiliaryPhase.surjective x
  rw [mem_classicalAuxiliaryRootSpaceTop_phase]
  constructor
  · rintro ⟨a, ha, he⟩
    exact intervalAuxiliaryPhase.injective he ▸ ha
  · intro hy
    exact ⟨y, hy, rfl⟩

/-- An equivalence of full physical generalized eigenspaces, including all Jordan chains. -/
def classicalAuxiliaryRootSpaceTopEquiv (b : BoundaryCondition) (u : IntervalPairL2) (z : ℂ) :
    classicalRootSpaceTop b (intervalAuxiliaryPotential u) z ≃ₗ[ℂ] classicalAuxiliaryRootSpaceTop b u z :=
  intervalAuxiliaryPhase.toLinearEquiv.ofSubmodules _ _ (map_classicalRootSpaceTop_auxiliary b u z)

theorem finiteDimensional_classicalAuxiliaryRootSpaceTop (b : BoundaryCondition) (u : IntervalPairL2) (z : ℂ) :
    FiniteDimensional ℂ (classicalAuxiliaryRootSpaceTop b u z) := by
  let := finiteDimensional_classicalRootSpaceTop b (intervalAuxiliaryPotential u) z
  exact FiniteDimensional.of_injective (V₂ := ↥(classicalRootSpaceTop b (intervalAuxiliaryPotential u) z))
    (classicalAuxiliaryRootSpaceTopEquiv b u z).symm.toLinearMap (classicalAuxiliaryRootSpaceTopEquiv b u z).symm.injective

theorem exists_classicalAuxiliaryRootSpace_eq_top (b : BoundaryCondition) (u : IntervalPairL2) (z : ℂ) :
    ∃ n : ℕ, classicalAuxiliaryRootSpace b u z n = classicalAuxiliaryRootSpaceTop b u z := by
  obtain ⟨n, hn⟩ := exists_classicalRootSpace_eq_top b (intervalAuxiliaryPotential u) z
  refine ⟨n, ?_⟩
  ext x
  obtain ⟨y, rfl⟩ := intervalAuxiliaryPhase.surjective x
  rw [mem_classicalAuxiliaryRootSpace_phase, mem_classicalAuxiliaryRootSpaceTop_phase, hn]

/-- Every physical generalized root vector belongs to the original unbounded auxiliary domain. -/
theorem classicalAuxiliaryRootSpaceTop_le_domain (b : BoundaryCondition) (u : IntervalPairL2) (z : ℂ) :
    classicalAuxiliaryRootSpaceTop b u z ≤ (classicalAuxiliaryUnboundedOperator b u).domain := by
  intro x hx
  obtain ⟨n, hn⟩ := (mem_classicalAuxiliaryRootSpaceTop b u z x).mp hx
  rw [mem_classicalAuxiliaryUnboundedOperator_domain]
  cases n with
  | zero => exact ⟨0, by simpa using (show x = 0 from hn).symm⟩
  | succ n =>
    obtain ⟨f, hf, _⟩ := (mem_classicalAuxiliaryRootSpace_succ b u z n x).mp hn
    exact ⟨f, hf⟩

theorem isClosed_classicalAuxiliaryRootSpaceTop (b : BoundaryCondition) (u : IntervalPairL2) (z : ℂ) :
    IsClosed (classicalAuxiliaryRootSpaceTop b u z : Set IntervalPairL2) := by
  let := finiteDimensional_classicalAuxiliaryRootSpaceTop b u z
  exact (classicalAuxiliaryRootSpaceTop b u z).closed_of_finiteDimensional

end NLS.ZakharovShabat.BoundaryCondition
