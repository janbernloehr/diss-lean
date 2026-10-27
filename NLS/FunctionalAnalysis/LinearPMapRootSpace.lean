import NLS.FunctionalAnalysis.SymmetricPencilEstimate

/-! # Actual root chains of a partial linear operator -/
noncomputable section
set_option autoImplicit false
namespace NLS.FunctionalAnalysis

section Algebraic
variable {D E D' E' : Type*}
    [AddCommGroup D] [Module ℂ D] [AddCommGroup E] [Module ℂ E]
    [AddCommGroup D'] [Module ℂ D'] [AddCommGroup E'] [Module ℂ E']

/-- Root chains retain a domain representative at every application of the pencil. -/
def pencilRootSpace (ι : D →ₗ[ℂ] E) (P : D →ₗ[ℂ] E) : ℕ → Submodule ℂ E
  | 0 => ⊥
  | n + 1 => ((pencilRootSpace ι P n).comap P).map ι

theorem mem_pencilRootSpace_succ (ι : D →ₗ[ℂ] E) (P : D →ₗ[ℂ] E) (n : ℕ) (x : E) :
    x ∈ pencilRootSpace ι P (n+1) ↔ ∃ a : D, ι a = x ∧ P a ∈ pencilRootSpace ι P n := by
  simp only [pencilRootSpace,Submodule.mem_map,Submodule.mem_comap]
  exact exists_congr fun _ => and_comm

theorem pencilRootSpace_mono (ι : D →ₗ[ℂ] E) (P : D →ₗ[ℂ] E) :
    Monotone (pencilRootSpace ι P) := by
  apply monotone_nat_of_le_succ
  intro n
  induction n with
  | zero => exact bot_le
  | succ n ih => exact Submodule.map_mono (Submodule.comap_mono ih)

/-- Exact base and domain conjugacy transports every chain level, including all domain requirements. -/
theorem pencilRootSpace_equiv (ι : D →ₗ[ℂ] E) (P : D →ₗ[ℂ] E)
    (ι' : D' →ₗ[ℂ] E') (P' : D' →ₗ[ℂ] E') (d : D ≃ₗ[ℂ] D') (e : E ≃ₗ[ℂ] E')
    (hι : ∀ a, ι' (d a) = e (ι a)) (hP : ∀ a, P' (d a) = e (P a))
    (n : ℕ) (x : E) : x ∈ pencilRootSpace ι P n ↔ e x ∈ pencilRootSpace ι' P' n := by
  induction n generalizing x with
  | zero =>
    change x = 0 ↔ e x = 0
    exact e.map_eq_zero_iff.symm
  | succ n ih =>
    rw [mem_pencilRootSpace_succ,mem_pencilRootSpace_succ]
    constructor
    · rintro ⟨a,ha,hprev⟩
      refine ⟨d a,by rw [hι,ha],?_⟩
      rw [hP]
      exact (ih _).mp hprev
    · rintro ⟨b,hb,hprev⟩
      obtain ⟨a,rfl⟩ := d.surjective b
      refine ⟨a,?_,?_⟩
      · apply e.injective
        rwa [hι] at hb
      · apply (ih _).mpr
        rwa [hP] at hprev

/-- The complete root space is the increasing union of all finite chain levels. -/
def pencilRootSpaceTop (ι : D →ₗ[ℂ] E) (P : D →ₗ[ℂ] E) : Submodule ℂ E :=
  ⨆ n : ℕ, pencilRootSpace ι P n

theorem mem_pencilRootSpaceTop (ι : D →ₗ[ℂ] E) (P : D →ₗ[ℂ] E) (x : E) :
    x ∈ pencilRootSpaceTop ι P ↔ ∃ n, x ∈ pencilRootSpace ι P n :=
  Submodule.mem_iSup_of_directed _ (pencilRootSpace_mono ι P).directed_le

theorem pencilRootSpaceTop_equiv (ι : D →ₗ[ℂ] E) (P : D →ₗ[ℂ] E)
    (ι' : D' →ₗ[ℂ] E') (P' : D' →ₗ[ℂ] E') (d : D ≃ₗ[ℂ] D') (e : E ≃ₗ[ℂ] E')
    (hι : ∀ a, ι' (d a) = e (ι a)) (hP : ∀ a, P' (d a) = e (P a)) (x : E) :
    x ∈ pencilRootSpaceTop ι P ↔ e x ∈ pencilRootSpaceTop ι' P' := by
  simp only [mem_pencilRootSpaceTop,pencilRootSpace_equiv ι P ι' P' d e hι hP]

end Algebraic

section Physical
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Actual physical generalized eigenvectors of a partial operator, defined by its own pencil. -/
def linearPMapRootSpace (T : E →ₗ.[ℂ] E) (z : ℂ) : ℕ → Submodule ℂ E :=
  pencilRootSpace T.domain.subtype (linearPMapPencil T z)

theorem mem_linearPMapRootSpace_succ (T : E →ₗ.[ℂ] E) (z : ℂ) (n : ℕ) (x : E) :
    x ∈ linearPMapRootSpace T z (n+1) ↔ ∃ a : T.domain,
      (a : E) = x ∧ linearPMapPencil T z a ∈ linearPMapRootSpace T z n :=
  mem_pencilRootSpace_succ _ _ n x

/-- The full physical root space uses arbitrary finite chains on the unchanged operator domain. -/
def linearPMapRootSpaceTop (T : E →ₗ.[ℂ] E) (z : ℂ) : Submodule ℂ E :=
  pencilRootSpaceTop T.domain.subtype (linearPMapPencil T z)

theorem mem_linearPMapRootSpaceTop (T : E →ₗ.[ℂ] E) (z : ℂ) (x : E) :
    x ∈ linearPMapRootSpaceTop T z ↔ ∃ n, x ∈ linearPMapRootSpace T z n :=
  mem_pencilRootSpaceTop _ _ x

theorem linearPMapRootSpaceTop_le_domain (T : E →ₗ.[ℂ] E) (z : ℂ) :
    linearPMapRootSpaceTop T z ≤ T.domain := by
  intro x hx
  obtain ⟨n,hn⟩ := (mem_linearPMapRootSpaceTop T z x).mp hx
  cases n with
  | zero =>
    have hx0 : x = 0 := hn
    rw [hx0]
    exact T.domain.zero_mem
  | succ n =>
    obtain ⟨a,ha,_⟩ := (mem_linearPMapRootSpace_succ T z n x).mp hn
    exact ha ▸ a.property

end Physical
end NLS.FunctionalAnalysis
