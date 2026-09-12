import NLS.ZakharovShabat.ClassicalIntervalClosed
import NLS.ZakharovShabat.BoundaryRootSpaces

/-!
# Root chains of the original physical interval operator

The recursion uses the original classical-domain pencil and physical inclusion,
requiring domain membership at every application. It is defined independently
of coefficient root spaces. The base and domain isomorphisms preserve every
finite chain level and the full increasing union.
-/

noncomputable section
open MeasureTheory Set
namespace NLS.ZakharovShabat.BoundaryCondition

/-- Physical vectors annihilated by `n` applications of `z-L`, with the original domain required at each step. -/
def classicalRootSpace (b : BoundaryCondition) (u : IntervalPairL2) (z : ℂ) : ℕ → Submodule ℂ IntervalPairL2
  | 0 => ⊥
  | n + 1 => ((classicalRootSpace b u z n).comap (classicalPencil b u z).toLinearMap).map
      (classicalInclusion b).toLinearMap

@[simp] theorem classicalRootSpace_zero (b : BoundaryCondition) (u : IntervalPairL2) (z : ℂ) :
    classicalRootSpace b u z 0 = ⊥ := rfl

theorem mem_classicalRootSpace_succ (b : BoundaryCondition) (u : IntervalPairL2) (z : ℂ) (n : ℕ)
    (x : IntervalPairL2) : x ∈ classicalRootSpace b u z (n + 1) ↔
      ∃ f : ClassicalIntervalDomain b, classicalInclusion b f = x ∧ classicalPencil b u z f ∈ classicalRootSpace b u z n := by
  simp only [classicalRootSpace, Submodule.mem_map, Submodule.mem_comap]
  exact exists_congr fun _ => and_comm

/-- At the first level, the physical root space is exactly the included ordinary eigenspace. -/
theorem classicalRootSpace_one (b : BoundaryCondition) (u : IntervalPairL2) (z : ℂ) :
    classicalRootSpace b u z 1 = (classicalPencil b u z).ker.map (classicalInclusion b).toLinearMap := rfl

/-- Root chains are preserved, including all intermediate domain requirements. -/
theorem mem_classicalRootSpace_iff (b : BoundaryCondition) (u : IntervalPairL2) (z : ℂ) (n : ℕ)
    (x : IntervalPairL2) : x ∈ classicalRootSpace b u z n ↔
      intervalL2Equiv b x ∈ rootSpace b (by simp) (intervalPotentialCoefficients u)
        (intervalPotentialCoefficients_mem u) z n := by
  induction n generalizing x with
  | zero =>
    change x = 0 ↔ intervalL2Equiv b x = 0
    constructor
    · rintro rfl; exact map_zero _
    · intro h; exact (intervalL2Equiv b).injective (h.trans (map_zero _).symm)
  | succ n ih =>
    rw [mem_classicalRootSpace_succ, mem_rootSpace_succ]
    constructor
    · rintro ⟨f, hf, hn⟩
      refine ⟨classicalIntervalEquiv b f, ?_, ?_⟩
      · rw [← intervalL2Equiv_classicalInclusion, hf]
      · rw [← intervalL2Equiv_classicalPencil]
        exact (ih _).mp hn
    · rintro ⟨f, hf, hn⟩
      refine ⟨(classicalIntervalEquiv b).symm f, ?_, ?_⟩
      · apply (intervalL2Equiv b).injective
        rw [intervalL2Equiv_classicalInclusion, (classicalIntervalEquiv b).apply_symm_apply]
        exact hf
      · apply (ih _).mpr
        rw [intervalL2Equiv_classicalPencil, (classicalIntervalEquiv b).apply_symm_apply]
        exact hn

theorem classicalRootSpace_mono (b : BoundaryCondition) (u : IntervalPairL2) (z : ℂ) :
    Monotone (classicalRootSpace b u z) := by
  apply monotone_nat_of_le_succ
  intro n
  induction n with
  | zero => exact bot_le
  | succ n ih => exact Submodule.map_mono (Submodule.comap_mono ih)

/-- Every physical root vector is in the original classical domain. -/
theorem exists_domain_of_mem_classicalRootSpace (b : BoundaryCondition) (u : IntervalPairL2) (z : ℂ)
    (n : ℕ) (x : IntervalPairL2) (hx : x ∈ classicalRootSpace b u z n) :
    ∃ f : ClassicalIntervalDomain b, classicalInclusion b f = x := by
  cases n with
  | zero => exact ⟨0, by simpa using (show x = 0 from hx).symm⟩
  | succ n =>
    obtain ⟨f, hf, _⟩ := (mem_classicalRootSpace_succ b u z n x).mp hx
    exact ⟨f, hf⟩

/-- The full physical generalized eigenspace is the union over finite chain lengths. -/
def classicalRootSpaceTop (b : BoundaryCondition) (u : IntervalPairL2) (z : ℂ) : Submodule ℂ IntervalPairL2 :=
  ⨆ n : ℕ, classicalRootSpace b u z n

theorem mem_classicalRootSpaceTop (b : BoundaryCondition) (u : IntervalPairL2) (z : ℂ) (x : IntervalPairL2) :
    x ∈ classicalRootSpaceTop b u z ↔ ∃ n, x ∈ classicalRootSpace b u z n :=
  Submodule.mem_iSup_of_directed _ (classicalRootSpace_mono b u z).directed_le

/-- Full root-space membership is equivalent under the physical Fourier isomorphism. -/
theorem mem_classicalRootSpaceTop_iff (b : BoundaryCondition) (u : IntervalPairL2) (z : ℂ) (x : IntervalPairL2) :
    x ∈ classicalRootSpaceTop b u z ↔ intervalL2Equiv b x ∈
      rootSpaceTop b (by simp) (intervalPotentialCoefficients u) (intervalPotentialCoefficients_mem u) z := by
  simp only [mem_classicalRootSpaceTop, mem_rootSpaceTop, mem_classicalRootSpace_iff]

/-- Full physical root vectors belong to the actual unbounded operator domain. -/
theorem classicalRootSpaceTop_le_domain (b : BoundaryCondition) (u : IntervalPairL2) (z : ℂ) :
    classicalRootSpaceTop b u z ≤ (classicalUnboundedOperator b u).domain := by
  intro x hx
  obtain ⟨n, hn⟩ := (mem_classicalRootSpaceTop b u z x).mp hx
  exact (mem_classicalUnboundedOperator_domain b u x).mpr (exists_domain_of_mem_classicalRootSpace b u z n x hn)

/-- The physical base-space map restricts to a linear equivalence of full generalized eigenspaces. -/
def classicalRootSpaceTopEquiv (b : BoundaryCondition) (u : IntervalPairL2) (z : ℂ) :
    classicalRootSpaceTop b u z ≃ₗ[ℂ]
      rootSpaceTop b (by simp) (intervalPotentialCoefficients u) (intervalPotentialCoefficients_mem u) z where
  toFun x := ⟨intervalL2Equiv b x.val, (mem_classicalRootSpaceTop_iff b u z x.val).mp x.property⟩
  invFun y := ⟨(intervalL2Equiv b).symm y.val, (mem_classicalRootSpaceTop_iff b u z _).mpr (by
    rw [(intervalL2Equiv b).apply_symm_apply]; exact y.property)⟩
  left_inv x := Subtype.ext ((intervalL2Equiv b).symm_apply_apply x.val)
  right_inv y := Subtype.ext ((intervalL2Equiv b).apply_symm_apply y.val)
  map_add' x y := Subtype.ext (map_add (intervalL2Equiv b) x.val y.val)
  map_smul' c x := Subtype.ext (map_smul (intervalL2Equiv b) c x.val)

/-- Physical root chains stabilize at a finite length. -/
theorem exists_classicalRootSpace_eq_top (b : BoundaryCondition) (u : IntervalPairL2) (z : ℂ) :
    ∃ n : ℕ, classicalRootSpace b u z n = classicalRootSpaceTop b u z := by
  obtain ⟨n, hn⟩ := exists_rootSpace_eq_top b (by simp) (intervalPotentialCoefficients u)
    (intervalPotentialCoefficients_mem u) z
  refine ⟨n, ?_⟩
  ext x
  rw [mem_classicalRootSpace_iff, mem_classicalRootSpaceTop_iff, hn]

/-- The original full generalized eigenspaces are finite dimensional. -/
theorem finiteDimensional_classicalRootSpaceTop (b : BoundaryCondition) (u : IntervalPairL2) (z : ℂ) :
    FiniteDimensional ℂ (classicalRootSpaceTop b u z) := by
  have hp : (2 : ENNReal) ≠ ⊤ := by simp
  let : FiniteDimensional ℂ (rootSpaceTop b hp (intervalPotentialCoefficients u)
    (intervalPotentialCoefficients_mem u) z) := finiteDimensional_rootSpaceTop b hp _ _ z
  exact FiniteDimensional.of_injective
    (V₂ := rootSpaceTop b hp (intervalPotentialCoefficients u) (intervalPotentialCoefficients_mem u) z)
    (classicalRootSpaceTopEquiv b u z).toLinearMap
    (classicalRootSpaceTopEquiv b u z).injective

theorem isClosed_classicalRootSpaceTop (b : BoundaryCondition) (u : IntervalPairL2) (z : ℂ) :
    IsClosed (classicalRootSpaceTop b u z : Set IntervalPairL2) := by
  let : FiniteDimensional ℂ (classicalRootSpaceTop b u z) := finiteDimensional_classicalRootSpaceTop b u z
  exact (classicalRootSpaceTop b u z).closed_of_finiteDimensional

end NLS.ZakharovShabat.BoundaryCondition
