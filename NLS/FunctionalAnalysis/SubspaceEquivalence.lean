import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Analysis.Complex.Basic

/-! # Restricting bounded equivalences to corresponding closed forms -/
noncomputable section
namespace NLS.FunctionalAnalysis
/-- Restriction of a complex Banach equivalence between possibly different
spaces, retaining both bounded operators and both inverse identities. -/
def complexEquivReal {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]
    [NormedAddCommGroup B] [NormedSpace ℂ B] (e : A ≃L[ℂ] B) : A ≃L[ℝ] B where
  toLinearEquiv :=
    { toLinearMap := (e.toContinuousLinearMap.restrictScalars ℝ).toLinearMap
      invFun := e.symm
      left_inv := e.symm_apply_apply
      right_inv := e.apply_symm_apply }
  continuous_toFun := e.continuous
  continuous_invFun := e.symm.continuous

@[simp] theorem complexEquivReal_apply {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]
    [NormedAddCommGroup B] [NormedSpace ℂ B] (e : A ≃L[ℂ] B) (a : A) : complexEquivReal e a = e a := rfl

@[simp] theorem complexEquivReal_symm_apply {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]
    [NormedAddCommGroup B] [NormedSpace ℂ B] (e : A ≃L[ℂ] B) (b : B) :
    (complexEquivReal e).symm b = e.symm b := rfl

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

def subspaceEquiv (e : E ≃L[𝕜] F) (R : Submodule 𝕜 E) (S : Submodule 𝕜 F)
    (h : ∀ a, a ∈ R ↔ e a ∈ S) : R ≃L[𝕜] S :=
  e.ofSubmodules R S (by
    ext b
    constructor
    · rintro ⟨a,ha,rfl⟩
      exact (h a).mp ha
    · intro hb
      exact ⟨e.symm b,(h _).mpr (by simpa only [e.apply_symm_apply] using hb),e.apply_symm_apply b⟩)

@[simp] theorem subspaceEquiv_apply (e : E ≃L[𝕜] F) (R : Submodule 𝕜 E) (S : Submodule 𝕜 F)
    (h : ∀ a, a ∈ R ↔ e a ∈ S) (a : R) : (subspaceEquiv e R S h a).val = e a.val := rfl

@[simp] theorem subspaceEquiv_symm_apply (e : E ≃L[𝕜] F) (R : Submodule 𝕜 E) (S : Submodule 𝕜 F)
    (h : ∀ a, a ∈ R ↔ e a ∈ S) (b : S) : ((subspaceEquiv e R S h).symm b).val = e.symm b.val := rfl

theorem prodCongr_refl_snd {A B C : Type*}
    [NormedAddCommGroup A] [NormedSpace 𝕜 A] [NormedAddCommGroup B] [NormedSpace 𝕜 B]
    [NormedAddCommGroup C] [NormedSpace 𝕜 C]
    (L : A ≃L[𝕜] B) (z : A × C) :
    ((L.prodCongr (ContinuousLinearEquiv.refl 𝕜 C)) z).2 = z.2 := rfl

theorem prodMap_id_snd {A B C : Type*}
    [NormedAddCommGroup A] [NormedSpace 𝕜 A] [NormedAddCommGroup B] [NormedSpace 𝕜 B]
    [NormedAddCommGroup C] [NormedSpace 𝕜 C]
    (L : A →L[𝕜] B) (z : A × C) : ((L.prodMap (ContinuousLinearMap.id 𝕜 C)) z).2 = z.2 := rfl

end NLS.FunctionalAnalysis
