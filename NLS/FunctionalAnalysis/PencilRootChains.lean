import NLS.FunctionalAnalysis.LinearPMapRootSpace
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# Finite domain chains and actual pencil root spaces

A chain is stored in Taylor order: the eigenvector first and the last
generalized vector last. Every coefficient is in the original domain.
For an injective domain inclusion, evaluation of the last coefficient is a
linear equivalence with the corresponding actual root-space level.
-/
noncomputable section
namespace NLS.FunctionalAnalysis
variable {D E : Type*} [AddCommGroup D] [Module ℂ D] [AddCommGroup E] [Module ℂ E]

/-- The last domain vector, included in the base space; the empty chain gives zero. -/
def pencilChainEndpoint (J : D →ₗ[ℂ] E) : (N : ℕ) → (Fin N → D) →ₗ[ℂ] E
  | 0 => 0
  | N+1 =>
    { toFun := fun v => J (v (Fin.last N))
      map_add' := by intro v w; exact J.map_add _ _
      map_smul' := by intro c v; exact J.map_smul c _ }

@[simp] theorem pencilChainEndpoint_zero (J : D →ₗ[ℂ] E) (v : Fin 0 → D) :
    pencilChainEndpoint J 0 v = 0 := rfl

@[simp] theorem pencilChainEndpoint_succ (J : D →ₗ[ℂ] E) (N : ℕ) (v : Fin (N+1) → D) :
    pencilChainEndpoint J (N+1) v = J (v (Fin.last N)) := rfl

/-- Including the last domain coefficient gives the same actual chain endpoint. -/
theorem pencilChainEndpoint_factor (J : D →ₗ[ℂ] E) (N : ℕ) (v : Fin N → D) :
    pencilChainEndpoint J N v = J (pencilChainEndpoint (LinearMap.id : D →ₗ[ℂ] D) N v) := by
  cases N <;> simp

/-- All finite domain-preserving chains. Appending a vector requires its pencil
image to be the included final vector of the preceding chain. -/
def pencilChainSpace (J P : D →ₗ[ℂ] E) : (N : ℕ) → Submodule ℂ (Fin N → D)
  | 0 => ⊤
  | N+1 =>
    { carrier := {v | Fin.init v ∈ pencilChainSpace J P N ∧
        P (v (Fin.last N)) = pencilChainEndpoint J N (Fin.init v)}
      zero_mem' := by
        refine ⟨(pencilChainSpace J P N).zero_mem, ?_⟩
        change P 0 = pencilChainEndpoint J N 0
        simp
      add_mem' := by
        intro v w hv hw
        refine ⟨(pencilChainSpace J P N).add_mem hv.1 hw.1, ?_⟩
        change P (v (Fin.last N) + w (Fin.last N)) =
          pencilChainEndpoint J N (Fin.init v + Fin.init w)
        rw [map_add, map_add, hv.2, hw.2]
      smul_mem' := by
        intro c v hv
        refine ⟨(pencilChainSpace J P N).smul_mem c hv.1, ?_⟩
        change P (c • v (Fin.last N)) = pencilChainEndpoint J N (c • Fin.init v)
        rw [map_smul, map_smul, hv.2] }

/-- The recursive condition includes the zero-length chain without an extra domain premise. -/
theorem mem_pencilChainSpace_succ (J P : D →ₗ[ℂ] E) (N : ℕ) (v : Fin (N+1) → D) :
    v ∈ pencilChainSpace J P (N+1) ↔ Fin.init v ∈ pencilChainSpace J P N ∧
      P (v (Fin.last N)) = pencilChainEndpoint J N (Fin.init v) := Iff.rfl

/-- Every finite domain chain ends in the actual root space of the same length. -/
theorem pencilChainEndpoint_mem (J P : D →ₗ[ℂ] E) (N : ℕ)
    (v : Fin N → D) (hv : v ∈ pencilChainSpace J P N) :
    pencilChainEndpoint J N v ∈ pencilRootSpace J P N := by
  induction N with
  | zero => exact (pencilRootSpace J P 0).zero_mem
  | succ N ih =>
    obtain ⟨ht, he⟩ := (mem_pencilChainSpace_succ J P N v).mp hv
    apply (mem_pencilRootSpace_succ J P N _).mpr
    exact ⟨v (Fin.last N), rfl, he ▸ ih (Fin.init v) ht⟩

/-- Every actual finite root vector has a full chain of original domain representatives. -/
theorem exists_pencilChain_of_mem_rootSpace (J P : D →ₗ[ℂ] E) (N : ℕ)
    (x : E) (hx : x ∈ pencilRootSpace J P N) :
    ∃ v ∈ pencilChainSpace J P N, pencilChainEndpoint J N v = x := by
  induction N generalizing x with
  | zero =>
    have hx0 : x = 0 := hx
    exact ⟨Fin.elim0, Submodule.mem_top, hx0.symm⟩
  | succ N ih =>
    obtain ⟨a, ha, hp⟩ := (mem_pencilRootSpace_succ J P N x).mp hx
    obtain ⟨v, hv, he⟩ := ih (P a) hp
    refine ⟨Fin.snoc v a, ?_, ?_⟩
    · rw [mem_pencilChainSpace_succ, Fin.init_snoc, Fin.snoc_last]
      exact ⟨hv, he.symm⟩
    · simpa only [pencilChainEndpoint_succ, Fin.snoc_last] using ha

/-- For an injective domain inclusion the final root vector determines its entire finite chain. -/
theorem pencilChainEndpoint_injective (J P : D →ₗ[ℂ] E) (hJ : Function.Injective J) (N : ℕ) :
    Function.Injective (fun v : pencilChainSpace J P N => pencilChainEndpoint J N v.val) := by
  induction N with
  | zero =>
    intro v w _
    apply Subtype.ext
    exact funext (fun i => Fin.elim0 i)
  | succ N ih =>
    intro v w he
    have hl : v.val (Fin.last N) = w.val (Fin.last N) := hJ he
    have hv := (mem_pencilChainSpace_succ J P N v.val).mp v.property
    have hw := (mem_pencilChainSpace_succ J P N w.val).mp w.property
    have ht : Fin.init v.val = Fin.init w.val := by
      have hp : pencilChainEndpoint J N (Fin.init v.val) =
          pencilChainEndpoint J N (Fin.init w.val) := by rw [← hv.2, ← hw.2, hl]
      exact congrArg Subtype.val (ih (a₁ := ⟨Fin.init v.val, hv.1⟩)
        (a₂ := ⟨Fin.init w.val, hw.1⟩) hp)
    apply Subtype.ext
    rw [← Fin.snoc_init_self v.val, ← Fin.snoc_init_self w.val, ht, hl]

/-- The endpoint map with its actual finite root-space codomain. -/
def pencilChainToRootSpace (J P : D →ₗ[ℂ] E) (N : ℕ) :
    pencilChainSpace J P N →ₗ[ℂ] pencilRootSpace J P N where
  toFun v := ⟨pencilChainEndpoint J N v.val, pencilChainEndpoint_mem J P N v.val v.property⟩
  map_add' := by intro v w; apply Subtype.ext; exact (pencilChainEndpoint J N).map_add _ _
  map_smul' := by intro c v; apply Subtype.ext; exact (pencilChainEndpoint J N).map_smul c _

/-- Exact linear equivalence of all finite domain chains with actual root-space levels. -/
def pencilChainRootEquiv (J P : D →ₗ[ℂ] E) (hJ : Function.Injective J) (N : ℕ) :
    pencilChainSpace J P N ≃ₗ[ℂ] pencilRootSpace J P N :=
  LinearEquiv.ofBijective (pencilChainToRootSpace J P N) ⟨
    fun _ _ h => pencilChainEndpoint_injective J P hJ N (congrArg Subtype.val h),
    fun x => by
      obtain ⟨v, hv, he⟩ := exists_pencilChain_of_mem_rootSpace J P N x.val x.property
      exact ⟨⟨v,hv⟩, Subtype.ext he⟩⟩

/-- The root-space equivalence evaluates the same original final vector. -/
theorem pencilChainRootEquiv_apply (J P : D →ₗ[ℂ] E) (hJ : Function.Injective J)
    (N : ℕ) (v : pencilChainSpace J P N) :
    (pencilChainRootEquiv J P hJ N v).val = pencilChainEndpoint J N v.val := rfl

/-- Finite physical chain spaces and actual finite root spaces have identical dimensions. -/
theorem finrank_pencilChainSpace (J P : D →ₗ[ℂ] E) (hJ : Function.Injective J) (N : ℕ) :
    Module.finrank ℂ (pencilChainSpace J P N) = Module.finrank ℂ (pencilRootSpace J P N) :=
  (pencilChainRootEquiv J P hJ N).finrank_eq

/-- The domain-valued polynomial whose coefficients are the finite chain. -/
def pencilChainPolynomial (N : ℕ) (v : Fin N → D) (t : ℂ) : D :=
  ∑ j : Fin N, t^j.val • v j

@[simp] theorem pencilChainPolynomial_zero (v : Fin 0 → D) (t : ℂ) :
    pencilChainPolynomial 0 v t = 0 := by simp [pencilChainPolynomial]

/-- Appending the last chain coefficient adds exactly its highest monomial. -/
theorem pencilChainPolynomial_succ (N : ℕ) (v : Fin (N+1) → D) (t : ℂ) :
    pencilChainPolynomial (N+1) v t =
      pencilChainPolynomial N (Fin.init v) t + t^N • v (Fin.last N) := by
  simp only [pencilChainPolynomial, Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last]
  rfl

/-- A domain chain polynomial solves the affine pencil exactly up to its final monomial. -/
theorem pencilChainPolynomial_pencil (J P : D →ₗ[ℂ] E) (N : ℕ)
    (v : Fin N → D) (hv : v ∈ pencilChainSpace J P N) (t : ℂ) :
    (t • J-P) (pencilChainPolynomial N v t) = t^N • pencilChainEndpoint J N v := by
  induction N with
  | zero => simp
  | succ N ih =>
    obtain ⟨ht, he⟩ := (mem_pencilChainSpace_succ J P N v).mp hv
    rw [pencilChainPolynomial_succ, map_add, map_smul, ih (Fin.init v) ht,
      pencilChainEndpoint_succ, ← he]
    change t^N • P (v (Fin.last N)) + t^N • (t • J (v (Fin.last N)) - P (v (Fin.last N))) = _
    rw [smul_sub, smul_smul, ← pow_succ]
    abel

end NLS.FunctionalAnalysis
