import NLS.ZakharovShabat.BoundarySpectrum
import NLS.ZakharovShabat.RootSpaces
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Boundary root spaces and algebraic multiplicity

For each boundary restriction in Chapter 1, §4, root chains are defined using
its actual domain-to-base pencil. Their inclusion into the periodic base space
identifies them with the corresponding boundary part of the periodic root
space, at every finite level and for the full root space. This gives finite
dimension and stabilization, and splits periodic algebraic multiplicity into
the Dirichlet and Neumann contributions.
-/

open scoped ENNReal
noncomputable section
namespace NLS.ZakharovShabat
namespace BoundaryCondition
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable (b : BoundaryCondition)

theorem inclusion_injective : Function.Injective (inclusion (p := p) b) := by
  intro f g h
  exact Subtype.ext (domainInclusion_injective (congrArg Subtype.val h))

/-- Root chains for the restricted operator require boundary-domain membership at each step. -/
def rootSpace (hp : p ≠ ⊤) (φ : PairSpace p) (hφ : φ ∈ dirichletSubspace) (z : ℂ) :
    ℕ → Submodule ℂ ↥(space (p := p) b)
  | 0 => ⊥
  | n + 1 => ((rootSpace hp φ hφ z n).comap (pencil b hp φ hφ z).toLinearMap).map
      (inclusion b).toLinearMap

@[simp] theorem rootSpace_zero (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) (z : ℂ) : rootSpace b hp φ hφ z 0 = ⊥ := rfl

theorem mem_rootSpace_succ (hp : p ≠ ⊤) (φ : PairSpace p) (hφ : φ ∈ dirichletSubspace)
    (z : ℂ) (n : ℕ) (x : space (p := p) b) : x ∈ rootSpace b hp φ hφ z (n + 1) ↔
    ∃ f : domain (p := p) b, inclusion b f = x ∧ pencil b hp φ hφ z f ∈ rootSpace b hp φ hφ z n := by
  simp only [rootSpace, Submodule.mem_map, Submodule.mem_comap]
  exact exists_congr fun _ => and_comm

/-- The ordinary eigenspace of the boundary restriction, in its weighted domain. -/
def eigenspace (hp : p ≠ ⊤) (φ : PairSpace p) (hφ : φ ∈ dirichletSubspace) (z : ℂ) :
    Submodule ℂ ↥(domain (p := p) b) := (pencil b hp φ hφ z).ker

theorem rootSpace_one (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) (z : ℂ) :
    rootSpace b hp φ hφ z 1 = (eigenspace b hp φ hφ z).map (inclusion b).toLinearMap := rfl

/-- A boundary chain is exactly a periodic chain whose initial vector satisfies the boundary condition. -/
theorem mem_rootSpace_iff_periodic (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) (z : ℂ) (n : ℕ) (x : space (p := p) b) :
    x ∈ rootSpace b hp φ hφ z n ↔ x.val ∈ periodicRootSpace hp φ z n := by
  induction n generalizing x with
  | zero =>
    change x = 0 ↔ x.val = 0
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  | succ n ih =>
    rw [mem_rootSpace_succ, mem_periodicRootSpace_succ]
    constructor
    · rintro ⟨f, hf, hn⟩
      exact ⟨f.val, congrArg Subtype.val hf, (ih _).mp hn⟩
    · rintro ⟨f, hf, hn⟩
      have hd : f ∈ domain b := (inclusion_mem b f).mp (hf ▸ x.property)
      refine ⟨⟨f, hd⟩, Subtype.ext hf, ?_⟩
      exact (ih _).mpr hn

theorem map_rootSpace (hp : p ≠ ⊤) (φ : PairSpace p) (hφ : φ ∈ dirichletSubspace)
    (z : ℂ) (n : ℕ) :
    (rootSpace b hp φ hφ z n).map (space b).subtype = periodicRootSpace hp φ z n ⊓ space b := by
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨(mem_rootSpace_iff_periodic b hp φ hφ z n a).mp ha, a.property⟩
  · rintro ⟨hr, hb⟩
    exact ⟨⟨x, hb⟩, (mem_rootSpace_iff_periodic b hp φ hφ z n _).mpr hr, rfl⟩

theorem rootSpace_mono (hp : p ≠ ⊤) (φ : PairSpace p) (hφ : φ ∈ dirichletSubspace) (z : ℂ) :
    Monotone (rootSpace b hp φ hφ z) := by
  intro m n h x hx
  rw [mem_rootSpace_iff_periodic] at hx ⊢
  exact periodicRootSpace_mono hp φ z h hx

/-- Every boundary root vector has a representative in the boundary operator domain. -/
theorem exists_domain_of_mem_rootSpace (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) (z : ℂ) (n : ℕ) (x : space (p := p) b)
    (hx : x ∈ rootSpace b hp φ hφ z n) : ∃ f : domain (p := p) b, inclusion b f = x := by
  obtain ⟨f, hf⟩ := exists_domain_of_mem_periodicRootSpace hp φ z n x.val
    ((mem_rootSpace_iff_periodic b hp φ hφ z n x).mp hx)
  exact ⟨⟨f, (inclusion_mem b f).mp (hf ▸ x.property)⟩, Subtype.ext hf⟩

/-- The full root space is the union of all finite boundary chains. -/
def rootSpaceTop (hp : p ≠ ⊤) (φ : PairSpace p) (hφ : φ ∈ dirichletSubspace) (z : ℂ) :
    Submodule ℂ ↥(space (p := p) b) := ⨆ n : ℕ, rootSpace b hp φ hφ z n

theorem mem_rootSpaceTop (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) (z : ℂ) (x : space (p := p) b) :
    x ∈ rootSpaceTop b hp φ hφ z ↔ ∃ n, x ∈ rootSpace b hp φ hφ z n :=
  Submodule.mem_iSup_of_directed _ (rootSpace_mono b hp φ hφ z).directed_le

theorem exists_domain_of_mem_rootSpaceTop (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) (z : ℂ) (x : space (p := p) b)
    (hx : x ∈ rootSpaceTop b hp φ hφ z) : ∃ f : domain (p := p) b, inclusion b f = x := by
  obtain ⟨n, hn⟩ := (mem_rootSpaceTop b hp φ hφ z x).mp hx
  exact exists_domain_of_mem_rootSpace b hp φ hφ z n x hn

theorem mem_rootSpaceTop_iff_periodic (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) (z : ℂ) (x : space (p := p) b) :
    x ∈ rootSpaceTop b hp φ hφ z ↔ x.val ∈ periodicRootSpaceTop hp φ z := by
  simp only [mem_rootSpaceTop, mem_periodicRootSpaceTop, mem_rootSpace_iff_periodic]

/-- The full root space of a restriction is the corresponding part of the periodic full root space. -/
theorem map_rootSpaceTop (hp : p ≠ ⊤) (φ : PairSpace p) (hφ : φ ∈ dirichletSubspace) (z : ℂ) :
    (rootSpaceTop b hp φ hφ z).map (space b).subtype = periodicRootSpaceTop hp φ z ⊓ space b := by
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨(mem_rootSpaceTop_iff_periodic b hp φ hφ z a).mp ha, a.property⟩
  · rintro ⟨hr, hb⟩
    exact ⟨⟨x, hb⟩, (mem_rootSpaceTop_iff_periodic b hp φ hφ z _).mpr hr, rfl⟩

theorem finiteDimensional_rootSpaceTop (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) (z : ℂ) : FiniteDimensional ℂ (rootSpaceTop b hp φ hφ z) := by
  let : FiniteDimensional ℂ (periodicRootSpaceTop hp φ z) := finiteDimensional_periodicRootSpaceTop hp φ z
  let F : ↥(rootSpaceTop b hp φ hφ z) →ₗ[ℂ] ↥(periodicRootSpaceTop hp φ z) :=
    { toFun x := ⟨x.val.val, (mem_rootSpaceTop_iff_periodic b hp φ hφ z x.val).mp x.property⟩
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  apply FiniteDimensional.of_injective (V₂ := ↥(periodicRootSpaceTop hp φ z)) F
  intro x y h
  have hv := congrArg (fun a : periodicRootSpaceTop hp φ z => a.val) h
  change x.val.val = y.val.val at hv
  exact Subtype.ext (Subtype.ext hv)

theorem exists_rootSpace_eq_top (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) (z : ℂ) : ∃ n : ℕ, rootSpace b hp φ hφ z n = rootSpaceTop b hp φ hφ z := by
  obtain ⟨n, hn⟩ := exists_periodicRootSpace_eq_top hp φ z
  refine ⟨n, ?_⟩
  ext x
  rw [mem_rootSpace_iff_periodic, mem_rootSpaceTop_iff_periodic, hn]

theorem finiteDimensional_rootSpace (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) (z : ℂ) (n : ℕ) : FiniteDimensional ℂ (rootSpace b hp φ hφ z n) := by
  let : FiniteDimensional ℂ (rootSpaceTop b hp φ hφ z) := finiteDimensional_rootSpaceTop b hp φ hφ z
  have hle : rootSpace b hp φ hφ z n ≤ rootSpaceTop b hp φ hφ z := le_iSup _ n
  exact FiniteDimensional.of_injective (V₂ := ↥(rootSpaceTop b hp φ hφ z))
    (Submodule.inclusion hle) (Submodule.inclusion_injective hle)

theorem isClosed_rootSpaceTop (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) (z : ℂ) :
    IsClosed (rootSpaceTop b hp φ hφ z : Set ↥(space (p := p) b)) := by
  let : FiniteDimensional ℂ (rootSpaceTop b hp φ hφ z) := finiteDimensional_rootSpaceTop b hp φ hφ z
  exact (rootSpaceTop b hp φ hφ z).closed_of_finiteDimensional

theorem rootSpace_eq_bot_of_mem_resolventSet (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) (z : ℂ) (hz : z ∈ resolventSet b hp φ hφ) (n : ℕ) :
    rootSpace b hp φ hφ z n = ⊥ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    apply eq_bot_iff.mpr
    intro x hx
    obtain ⟨f, hf, hn⟩ := (mem_rootSpace_succ b hp φ hφ z n x).mp hx
    rw [ih] at hn
    have hf0 : f = 0 := hz.injective ((show pencil b hp φ hφ z f = 0 from hn).trans (map_zero _).symm)
    simpa [hf0] using hf.symm

theorem rootSpaceTop_eq_bot_of_mem_resolventSet (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) (z : ℂ) (hz : z ∈ resolventSet b hp φ hφ) :
    rootSpaceTop b hp φ hφ z = ⊥ := by
  simp only [rootSpaceTop, rootSpace_eq_bot_of_mem_resolventSet b hp φ hφ z hz, iSup_bot]

theorem rootSpaceTop_ne_bot_iff (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) (z : ℂ) : rootSpaceTop b hp φ hφ z ≠ ⊥ ↔ z ∈ spectrum b hp φ hφ := by
  constructor
  · intro h hz
    exact h (rootSpaceTop_eq_bot_of_mem_resolventSet b hp φ hφ z hz)
  · intro hz hbot
    obtain ⟨f, hf, he⟩ := (mem_spectrum_iff_exists_kernel b hp φ hφ z).mp hz
    have hx : inclusion b f ∈ rootSpace b hp φ hφ z 1 :=
      (mem_rootSpace_succ b hp φ hφ z 0 _).mpr ⟨f, rfl, he⟩
    have ht : inclusion b f ∈ rootSpaceTop b hp φ hφ z := (mem_rootSpaceTop b hp φ hφ z _).mpr ⟨1, hx⟩
    rw [hbot] at ht
    exact hf (inclusion_injective b ((show inclusion b f = 0 from ht).trans (map_zero _).symm))

/-- Algebraic multiplicity counts the full boundary root space, including Jordan chains. -/
def algebraicMultiplicity (hp : p ≠ ⊤) (φ : PairSpace p) (hφ : φ ∈ dirichletSubspace) (z : ℂ) : ℕ :=
  Module.finrank ℂ (rootSpaceTop b hp φ hφ z)

theorem algebraicMultiplicity_pos_iff (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) (z : ℂ) : 0 < algebraicMultiplicity b hp φ hφ z ↔ z ∈ spectrum b hp φ hφ := by
  let : FiniteDimensional ℂ (rootSpaceTop b hp φ hφ z) := finiteDimensional_rootSpaceTop b hp φ hφ z
  rw [algebraicMultiplicity, Nat.pos_iff_ne_zero, Ne, Submodule.finrank_eq_zero]
  exact rootSpaceTop_ne_bot_iff b hp φ hφ z

theorem algebraicMultiplicity_eq_zero_iff (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) (z : ℂ) : algebraicMultiplicity b hp φ hφ z = 0 ↔ z ∈ resolventSet b hp φ hφ := by
  have h := not_congr (algebraicMultiplicity_pos_iff b hp φ hφ z)
  simpa only [Nat.not_lt, Nat.le_zero, spectrum, Set.mem_compl_iff, not_not] using h

/-- Boundary projection preserves every level of a periodic root chain. -/
theorem projection_mem_periodicRootSpace (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) (z : ℂ) (n : ℕ) (x : PairSpace p)
    (hx : x ∈ periodicRootSpace hp φ z n) : projection b x ∈ periodicRootSpace hp φ z n := by
  induction n generalizing x with
  | zero => simpa using congrArg (projection (p := p) b) (show x = 0 from hx)
  | succ n ih =>
    obtain ⟨f, hf, hn⟩ := (mem_periodicRootSpace_succ hp φ z n x).mp hx
    refine (mem_periodicRootSpace_succ hp φ z n _).mpr ⟨domainProjection b f, ?_, ?_⟩
    · rw [inclusion_projection, hf]
    · rw [spectralPencil_projection b hp φ hφ]
      exact ih _ hn

theorem projection_mem_periodicRootSpaceTop (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) (z : ℂ) (x : PairSpace p)
    (hx : x ∈ periodicRootSpaceTop hp φ z) : projection b x ∈ periodicRootSpaceTop hp φ z := by
  obtain ⟨n, hn⟩ := (mem_periodicRootSpaceTop hp φ z x).mp hx
  exact (mem_periodicRootSpaceTop hp φ z _).mpr ⟨n, projection_mem_periodicRootSpace b hp φ hφ z n x hn⟩

/-- Dimension can be computed in the ambient periodic space. -/
theorem finrank_periodicRootSpaceTop_inf (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) (z : ℂ) :
    Module.finrank ℂ ↥(periodicRootSpaceTop hp φ z ⊓ space b) = algebraicMultiplicity b hp φ hφ z := by
  rw [← map_rootSpaceTop b hp φ hφ z, Submodule.finrank_map_subtype_eq]
  rfl

end BoundaryCondition
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Each finite periodic root space is the direct sum of its two boundary parts. -/
theorem periodicRootSpace_boundary_split (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) (z : ℂ) (n : ℕ) :
    (periodicRootSpace hp φ z n ⊓ dirichletSubspace) ⊔
      (periodicRootSpace hp φ z n ⊓ neumannSubspace) = periodicRootSpace hp φ z n := by
  apply le_antisymm (sup_le inf_le_left inf_le_left)
  intro x hx
  rw [← dirichlet_neumann_decomposition x]
  exact Submodule.add_mem_sup
    ⟨BoundaryCondition.projection_mem_periodicRootSpace .dirichlet hp φ hφ z n x hx,
      ReflectionSplit.positiveProjection_mem _ x⟩
    ⟨BoundaryCondition.projection_mem_periodicRootSpace .neumann hp φ hφ z n x hx,
      ReflectionSplit.negativeProjection_mem _ x⟩

/-- The full periodic root space has the same boundary splitting. -/
theorem periodicRootSpaceTop_boundary_split (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) (z : ℂ) :
    (periodicRootSpaceTop hp φ z ⊓ dirichletSubspace) ⊔
      (periodicRootSpaceTop hp φ z ⊓ neumannSubspace) = periodicRootSpaceTop hp φ z := by
  obtain ⟨n, hn⟩ := exists_periodicRootSpace_eq_top hp φ z
  rw [← hn]
  exact periodicRootSpace_boundary_split hp φ hφ z n

/-- Periodic algebraic multiplicity is the sum of the two actual boundary multiplicities. -/
theorem periodicAlgebraicMultiplicity_eq_boundary_sum (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) (z : ℂ) :
    periodicAlgebraicMultiplicity hp φ z =
      BoundaryCondition.algebraicMultiplicity .dirichlet hp φ hφ z +
      BoundaryCondition.algebraicMultiplicity .neumann hp φ hφ z := by
  let M := periodicRootSpaceTop hp φ z
  let D := M ⊓ dirichletSubspace
  let N := M ⊓ neumannSubspace
  let : FiniteDimensional ℂ M := finiteDimensional_periodicRootSpaceTop hp φ z
  let : FiniteDimensional ℂ D := FiniteDimensional.of_injective
    (Submodule.inclusion (show D ≤ M from inf_le_left)) (Submodule.inclusion_injective _)
  let : FiniteDimensional ℂ N := FiniteDimensional.of_injective
    (Submodule.inclusion (show N ≤ M from inf_le_left)) (Submodule.inclusion_injective _)
  have hd : Disjoint D N := isCompl_dirichlet_neumann.disjoint.mono inf_le_right inf_le_right
  have hs : D ⊔ N = M := periodicRootSpaceTop_boundary_split hp φ hφ z
  have h := Submodule.finrank_sup_add_finrank_inf_eq D N
  rw [hs, hd.eq_bot, finrank_bot, add_zero] at h
  change Module.finrank ℂ M = _
  rw [← BoundaryCondition.finrank_periodicRootSpaceTop_inf .dirichlet hp φ hφ z,
    ← BoundaryCondition.finrank_periodicRootSpaceTop_inf .neumann hp φ hφ z]
  exact h

end NLS.ZakharovShabat
