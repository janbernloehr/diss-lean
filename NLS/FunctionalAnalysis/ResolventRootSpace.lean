import NLS.FunctionalAnalysis.LinearPMapRootSpace
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-! # Exact root-space transport through a resolvent

A full domain-to-base isomorphism at one parameter transports every actual
pencil root-chain level to a generalized eigenspace of the base resolvent.
All domain representatives are retained. This is an algebraic theorem and
requires no self-adjointness, diagonalization or multiplicity assumption.
-/
noncomputable section
namespace NLS.FunctionalAnalysis
open Module
variable {D E : Type*} [AddCommGroup D] [Module ℂ D]
  [AddCommGroup E] [Module ℂ E]

/-- Finite generalized eigenspaces obey the literal shifted-operator recurrence. -/
theorem mem_genEigenspace_succ_iff (T : Module.End ℂ E) (μ : ℂ) (n : ℕ) (x : E) :
    x ∈ T.genEigenspace μ (n+1:ℕ) ↔ (T-μ • 1) x ∈ T.genEigenspace μ n := by
  simp only [Module.End.mem_genEigenspace_nat, LinearMap.mem_ker, pow_succ,
    Module.End.mul_apply]

/-- At a nonzero value, every generalized eigenvector lies in the actual range of the operator. -/
theorem genEigenspace_le_range_of_ne_zero (T : Module.End ℂ E) (μ : ℂ) (hμ : μ ≠ 0)
    (n : ℕ) : T.genEigenspace μ n ≤ T.range := by
  induction n with
  | zero =>
    intro x hx
    have hx0 : x = 0 := by simpa only [Module.End.mem_genEigenspace_nat,
      pow_zero, LinearMap.mem_ker, Module.End.one_apply] using hx
    exact hx0 ▸ T.range.zero_mem
  | succ n ih =>
    intro x hx
    have hS := ih ((mem_genEigenspace_succ_iff T μ n x).mp hx)
    have hTx : T x ∈ T.range := LinearMap.mem_range_self T x
    have hm : μ • x ∈ T.range := by
      have h := T.range.sub_mem hTx hS
      change T x - (T x-μ • x) ∈ T.range at h
      simpa only [sub_sub_cancel] using h
    have h := T.range.smul_mem μ⁻¹ hm
    simpa only [inv_smul_smul₀ hμ] using h

/-- Applying an injective operator preserves and reflects each generalized eigenspace. -/
theorem mem_genEigenspace_apply_iff_of_injective (T : Module.End ℂ E)
    (hT : Function.Injective T) (μ : ℂ) (n : ℕ) (x : E) :
    T x ∈ T.genEigenspace μ n ↔ x ∈ T.genEigenspace μ n := by
  induction n generalizing x with
  | zero =>
    simp only [Module.End.mem_genEigenspace_nat, pow_zero,
      LinearMap.mem_ker, Module.End.one_apply]
    exact ⟨fun h => hT (h.trans (map_zero T).symm), fun h => by rw [h, map_zero]⟩
  | succ n ih =>
    rw [mem_genEigenspace_succ_iff, mem_genEigenspace_succ_iff]
    have he : (T-μ • 1) (T x) = T ((T-μ • 1) x) := by
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
        map_sub, map_smul]
    rw [he]
    exact ih _

/-- The base-space resolvent associated with an exact domain-to-base isomorphism. -/
def pencilResolvent (J : D →ₗ[ℂ] E) (e : D ≃ₗ[ℂ] E) : Module.End ℂ E :=
  J.comp e.symm.toLinearMap

theorem pencilResolvent_injective (J : D →ₗ[ℂ] E) (hJ : Function.Injective J)
    (e : D ≃ₗ[ℂ] E) : Function.Injective (pencilResolvent J e) :=
  hJ.comp e.symm.injective

/-- The resolvent image is exactly the unchanged original operator domain image. -/
theorem range_pencilResolvent (J : D →ₗ[ℂ] E) (e : D ≃ₗ[ℂ] E) :
    (pencilResolvent J e).range = J.range := by
  ext x
  constructor
  · rintro ⟨y,hy⟩
    exact ⟨e.symm y,hy⟩
  · rintro ⟨f,hf⟩
    exact ⟨e f,by change J (e.symm (e f)) = x; rwa [LinearEquiv.symm_apply_apply]⟩

/-- The actual pencil/resolvent intertwining identity, before taking root chains. -/
theorem pencilResolvent_intertwine (J : D →ₗ[ℂ] E) (e : D ≃ₗ[ℂ] E)
    (c : ℂ) (hc : c ≠ 0) (f : D) :
    pencilResolvent J e ((e.toLinearMap-c • J) f) =
      (-c) • ((pencilResolvent J e-c⁻¹ • 1) (J f)) := by
  change J (e.symm (e f-c • J f)) =
    (-c) • (J (e.symm (J f))-c⁻¹ • J f)
  rw [map_sub, map_smul, LinearEquiv.symm_apply_apply, map_sub, map_smul]
  rw [smul_sub, smul_smul, neg_mul, mul_inv_cancel₀ hc]
  module

/-- Every actual finite pencil root-chain level equals the corresponding resolvent generalized eigenspace. -/
theorem pencilRootSpace_eq_resolvent_genEigenspace (J : D →ₗ[ℂ] E)
    (hJ : Function.Injective J) (e : D ≃ₗ[ℂ] E) (c : ℂ) (hc : c ≠ 0) (n : ℕ) :
    pencilRootSpace J (e.toLinearMap-c • J) n =
      (pencilResolvent J e).genEigenspace c⁻¹ n := by
  induction n with
  | zero =>
    ext x
    simp only [pencilRootSpace, Submodule.mem_bot, Module.End.mem_genEigenspace_nat,
      pow_zero, LinearMap.mem_ker, Module.End.one_apply]
  | succ n ih =>
    ext x
    rw [mem_pencilRootSpace_succ, ih]
    constructor
    · rintro ⟨f,hf,hprev⟩
      apply (mem_genEigenspace_succ_iff _ _ n x).mpr
      have hR := (mem_genEigenspace_apply_iff_of_injective (pencilResolvent J e)
        (pencilResolvent_injective J hJ e) c⁻¹ n _).mpr hprev
      rw [pencilResolvent_intertwine J e c hc f, hf] at hR
      have h := ((pencilResolvent J e).genEigenspace c⁻¹ n).smul_mem (-c)⁻¹ hR
      simpa only [inv_smul_smul₀ (neg_ne_zero.mpr hc)] using h
    · intro hx
      have hdom := genEigenspace_le_range_of_ne_zero (pencilResolvent J e) c⁻¹
        (inv_ne_zero hc) (n+1) hx
      rw [range_pencilResolvent] at hdom
      obtain ⟨f,hf⟩ := hdom
      refine ⟨f,hf,?_⟩
      apply (mem_genEigenspace_apply_iff_of_injective (pencilResolvent J e)
        (pencilResolvent_injective J hJ e) c⁻¹ n _).mp
      rw [pencilResolvent_intertwine J e c hc f, hf]
      exact ((pencilResolvent J e).genEigenspace c⁻¹ n).smul_mem (-c)
        ((mem_genEigenspace_succ_iff _ _ n x).mp hx)

/-- The full physical algebraic root space equals the full resolvent generalized eigenspace. -/
theorem pencilRootSpaceTop_eq_resolvent_genEigenspace (J : D →ₗ[ℂ] E)
    (hJ : Function.Injective J) (e : D ≃ₗ[ℂ] E) (c : ℂ) (hc : c ≠ 0) :
    pencilRootSpaceTop J (e.toLinearMap-c • J) =
      (pencilResolvent J e).genEigenspace c⁻¹ ⊤ := by
  rw [pencilRootSpaceTop, Module.End.genEigenspace_top]
  exact iSup_congr (fun n => pencilRootSpace_eq_resolvent_genEigenspace J hJ e c hc n)

/-- Nonzero scaling of the physical pencil leaves every actual root-chain level unchanged. -/
theorem pencilRootSpace_smul (J P : D →ₗ[ℂ] E) (c : ℂ) (hc : c ≠ 0) (n : ℕ) :
    pencilRootSpace J (c • P) n = pencilRootSpace J P n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    ext x
    rw [mem_pencilRootSpace_succ, mem_pencilRootSpace_succ, ih]
    constructor
    · rintro ⟨f,hf,hP⟩
      refine ⟨f,hf,?_⟩
      have h := (pencilRootSpace J P n).smul_mem c⁻¹ hP
      simpa only [LinearMap.smul_apply, inv_smul_smul₀ hc] using h
    · rintro ⟨f,hf,hP⟩
      exact ⟨f,hf,(pencilRootSpace J P n).smul_mem c hP⟩

/-- Full algebraic root spaces are independent of a nonzero pencil normalization. -/
theorem pencilRootSpaceTop_smul (J P : D →ₗ[ℂ] E) (c : ℂ) (hc : c ≠ 0) :
    pencilRootSpaceTop J (c • P) = pencilRootSpaceTop J P := by
  unfold pencilRootSpaceTop
  exact iSup_congr (fun n => pencilRootSpace_smul J P c hc n)

/-- An injective physical pencil has no nontrivial root chain at any level. -/
theorem pencilRootSpace_eq_bot_of_injective (J P : D →ₗ[ℂ] E)
    (hP : Function.Injective P) (n : ℕ) : pencilRootSpace J P n = ⊥ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    apply le_antisymm _ bot_le
    intro x hx
    obtain ⟨f,hf,hprev⟩ := (mem_pencilRootSpace_succ J P n x).mp hx
    rw [ih] at hprev
    have hf0 : f = 0 := hP ((show P f = 0 from hprev).trans (map_zero P).symm)
    rw [hf0, map_zero] at hf
    exact hf.symm

/-- An injective physical pencil has zero full algebraic root space. -/
theorem pencilRootSpaceTop_eq_bot_of_injective (J P : D →ₗ[ℂ] E)
    (hP : Function.Injective P) : pencilRootSpaceTop J P = ⊥ := by
  unfold pencilRootSpaceTop
  simp only [pencilRootSpace_eq_bot_of_injective J P hP, iSup_bot]

end NLS.FunctionalAnalysis
