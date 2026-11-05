import Mathlib.Analysis.InnerProductSpace.l2Space

noncomputable section
set_option autoImplicit false
open Set Complex
open scoped ENNReal
namespace NLS

/-- The explicit real-linear normalization of a raw positive-index real
pair. The sign keeps the canonical pair as (Re Z,-Im Z). -/
def realNatPairNormalization (w : ℕ → ℝ) : (ℕ → ℝ × ℝ) →ₗ[ℝ] (ℕ → ℂ) where
  toFun a k := (w k : ℂ)*((a k).1-I*(a k).2)
  map_add' a b := by funext k; apply Complex.ext <;> simp <;> ring
  map_smul' r a := by funext k; apply Complex.ext <;> simp [Complex.real_smul] <;> ring

/-- Actual real coordinate pairs with finite prescribed weighted Hilbert
norm, retaining their raw coordinates rather than just a norm value. -/
def realWeightedNatPairSubmodule (w : ℕ → ℝ) : Submodule ℝ (ℕ → ℝ × ℝ) where
  carrier := {a | Memℓp (realNatPairNormalization w a) 2}
  zero_mem' := by
    change Memℓp (realNatPairNormalization w 0) 2
    rw [map_zero]
    exact zero_memℓp
  add_mem' := by
    intro a b ha hb
    change Memℓp (realNatPairNormalization w (a+b)) 2
    rw [map_add]
    exact ha.add hb
  smul_mem' := by
    intro r a ha
    change Memℓp (realNatPairNormalization w (r • a)) 2
    rw [map_smul]
    exact ha.const_smul r

def RealWeightedNatPair (w : ℕ → ℝ) (_hw : ∀ k, 0 < w k) := ↥(realWeightedNatPairSubmodule w)

namespace RealWeightedNatPair
variable (w : ℕ → ℝ) (hw : ∀ k, 0 < w k)

instance : AddCommGroup (RealWeightedNatPair w hw) := inferInstanceAs (AddCommGroup ↥(realWeightedNatPairSubmodule w))
instance : Module ℝ (RealWeightedNatPair w hw) := inferInstanceAs (Module ℝ ↥(realWeightedNatPairSubmodule w))

/-- Positive weighting identifies the full raw real-pair space with the
complex sequence Hilbert space viewed over the reals, in both directions. -/
def normalizationEquiv : RealWeightedNatPair w hw ≃ₗ[ℝ] lp (fun _ : ℕ => ℂ) 2 where
  toFun a := ⟨realNatPairNormalization w a.val,a.property⟩
  invFun z := ⟨fun k => ((z k).re/w k,-(z k).im/w k),by
    change Memℓp (realNatPairNormalization w (fun k => ((z k).re/w k,-(z k).im/w k))) 2
    have he : realNatPairNormalization w (fun k => ((z k).re/w k,-(z k).im/w k)) = (z : ℕ → ℂ) := by
      funext k
      apply Complex.ext <;> simp [realNatPairNormalization] <;> field_simp [(hw k).ne']
    rw [he]
    exact lp.memℓp z⟩
  left_inv a := by
    apply Subtype.ext
    funext k
    apply Prod.ext <;> simp [realNatPairNormalization] <;> field_simp [(hw k).ne']
  right_inv z := by
    ext k
    apply Complex.ext <;> simp [realNatPairNormalization] <;> field_simp [(hw k).ne']
  map_add' a b := by
    ext k
    change realNatPairNormalization w (a.val+b.val) k = _
    rw [map_add]
    rfl
  map_smul' r a := by
    ext k
    change realNatPairNormalization w (r • a.val) k = _
    rw [map_smul]
    rfl

instance : NormedAddCommGroup (RealWeightedNatPair w hw) :=
  NormedAddCommGroup.induced _ _ (normalizationEquiv w hw).toLinearMap (normalizationEquiv w hw).injective

instance : NormedSpace ℝ (RealWeightedNatPair w hw) :=
  NormedSpace.induced ℝ _ _ (normalizationEquiv w hw).toLinearMap

/-- This is exactly the prescribed weighted sum-of-squares norm. -/
def normalizationIsometry : RealWeightedNatPair w hw ≃ₗᵢ[ℝ] lp (fun _ : ℕ => ℂ) 2 where
  toLinearEquiv := normalizationEquiv w hw
  norm_map' _ := rfl

instance : CompleteSpace (RealWeightedNatPair w hw) :=
  (normalizationIsometry w hw).toIsometryEquiv.completeSpace

@[simp] theorem normalization_apply (a : RealWeightedNatPair w hw) (k : ℕ) :
    normalizationEquiv w hw a k = (w k : ℂ)*((a.val k).1-I*(a.val k).2) := rfl

@[simp] theorem normalization_symm_apply (z : lp (fun _ : ℕ => ℂ) 2) (k : ℕ) :
    ((normalizationEquiv w hw).symm z).val k = ((z k).re/w k,-(z k).im/w k) := rfl

/-- Decoding a normalized scalar retains its literal real and imaginary
coordinates with the fixed canonical sign. -/
theorem normalization_symm_apply_of_mul (z : lp (fun _ : ℕ => ℂ) 2) (k : ℕ) (t : ℂ)
    (h : z k = (w k : ℂ)*t) :
    ((normalizationEquiv w hw).symm z).val k = (t.re,-t.im) := by
  rw [normalization_symm_apply,h]
  apply Prod.ext <;> simp only [mul_re,mul_im,ofReal_re,ofReal_im,zero_mul,sub_zero,add_zero] <;>
    field_simp [(hw k).ne']

theorem normalization_coordinate_norm_sq (a : ℕ → ℝ × ℝ) (k : ℕ) :
    ‖realNatPairNormalization w a k‖^2 = (w k)^2*((a k).1^2+(a k).2^2) := by
  change ‖(w k : ℂ)*((a k).1-I*(a k).2)‖^2 = _
  rw [norm_mul,mul_pow,norm_real,Real.norm_eq_abs,sq_abs,Complex.sq_norm,Complex.normSq_apply]
  simp only [sub_re,ofReal_re,mul_re,I_re,I_im,ofReal_im,mul_zero,zero_mul,sub_zero,
    sub_im,mul_im,zero_add,zero_sub]
  ring

theorem summable_weighted_sq (a : RealWeightedNatPair w hw) :
    Summable (fun k => (w k)^2*((a.val k).1^2+(a.val k).2^2)) := by
  have h := (memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)).mp a.property
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two,normalization_coordinate_norm_sq] using h

theorem norm_sq_eq_tsum (a : RealWeightedNatPair w hw) :
    ‖a‖^2 = ∑' k : ℕ, (w k)^2*((a.val k).1^2+(a.val k).2^2) := by
  change ‖normalizationEquiv w hw a‖^2 = _
  calc
    _ = ∑' k : ℕ, ‖normalizationEquiv w hw a k‖^2 := by
      simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using
        lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) (normalizationEquiv w hw a)
    _ = _ := by
      apply tsum_congr
      intro k
      exact normalization_coordinate_norm_sq w a.val k

end RealWeightedNatPair
end NLS
