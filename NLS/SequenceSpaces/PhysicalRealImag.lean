import NLS.SequenceSpaces.ConjugateReflection

/-! # Real and imaginary physical Fourier parts in symmetric weighted spaces

Conjugate frequency reflection is the physical complex conjugation. Its
fixed locus is a real form, and averaging or taking its imaginary part
provides norm contractions and an exact complex decomposition.
-/
noncomputable section
set_option autoImplicit false
open scoped ENNReal ComplexConjugate
namespace NLS.WeightedCoeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

@[simp] theorem conjugateReflection_add (w : Weight) (hw : ∀ k, w (-k) = w k)
    (a b : WeightedCoeff w p) :
    conjugateReflection w hw (a+b) = conjugateReflection w hw a+conjugateReflection w hw b := by
  apply Subtype.ext
  funext k
  simp

@[simp] theorem conjugateReflection_smul (w : Weight) (hw : ∀ k, w (-k) = w k)
    (c : ℂ) (a : WeightedCoeff w p) :
    conjugateReflection w hw (c • a) = conj c • conjugateReflection w hw a := by
  apply Subtype.ext
  funext k
  simp

@[simp] theorem conjugateReflection_sub (w : Weight) (hw : ∀ k, w (-k) = w k)
    (a b : WeightedCoeff w p) :
    conjugateReflection w hw (a-b) = conjugateReflection w hw a-conjugateReflection w hw b := by
  apply Subtype.ext
  funext k
  simp

def physicalRealPart (w : Weight) (hw : ∀ k, w (-k) = w k) (a : WeightedCoeff w p) : WeightedCoeff w p :=
  (1/2 : ℂ) • (a+conjugateReflection w hw a)

def physicalImagPart (w : Weight) (hw : ∀ k, w (-k) = w k) (a : WeightedCoeff w p) : WeightedCoeff w p :=
  (-Complex.I/2 : ℂ) • (a-conjugateReflection w hw a)

theorem conjugateReflection_physicalRealPart (w : Weight) (hw : ∀ k, w (-k) = w k)
    (a : WeightedCoeff w p) :
    conjugateReflection w hw (physicalRealPart w hw a) = physicalRealPart w hw a := by
  simp only [physicalRealPart,conjugateReflection_smul,conjugateReflection_add,
    conjugateReflection_involutive,map_div₀,map_one,map_ofNat]
  congr 1
  exact add_comm _ _

theorem conjugateReflection_physicalImagPart (w : Weight) (hw : ∀ k, w (-k) = w k)
    (a : WeightedCoeff w p) :
    conjugateReflection w hw (physicalImagPart w hw a) = physicalImagPart w hw a := by
  apply Subtype.ext
  funext k
  simp only [physicalImagPart,conjugateReflection_apply,smul_val,sub_val,map_mul,map_div₀,
    map_neg,Complex.conj_I,map_ofNat,map_sub,neg_neg,Complex.conj_conj]
  ring

theorem physicalRealPart_add_I_physicalImagPart (w : Weight) (hw : ∀ k, w (-k) = w k)
    (a : WeightedCoeff w p) :
    physicalRealPart w hw a+Complex.I • physicalImagPart w hw a = a := by
  apply Subtype.ext
  funext k
  simp only [physicalRealPart,physicalImagPart,add_val,smul_val,sub_val,conjugateReflection_apply]
  calc
    _ = a.val k - (Complex.I^2+1)/2*(a.val k-conj (a.val (-k))) := by ring
    _ = a.val k := by rw [Complex.I_sq]; ring

theorem norm_physicalRealPart_le (w : Weight) (hw : ∀ k, w (-k) = w k) (a : WeightedCoeff w p) :
    ‖physicalRealPart w hw a‖ ≤ ‖a‖ := by
  rw [physicalRealPart,norm_smul]
  have h := norm_add_le a (conjugateReflection w hw a)
  rw [norm_conjugateReflection] at h
  norm_num only [norm_div,norm_one,Complex.norm_ofNat] at *
  linarith

theorem norm_physicalImagPart_le (w : Weight) (hw : ∀ k, w (-k) = w k) (a : WeightedCoeff w p) :
    ‖physicalImagPart w hw a‖ ≤ ‖a‖ := by
  rw [physicalImagPart,norm_smul]
  have h := norm_sub_le a (conjugateReflection w hw a)
  rw [norm_conjugateReflection] at h
  norm_num only [norm_div,norm_neg,Complex.norm_I,Complex.norm_ofNat] at *
  linarith

theorem continuous_conjugateReflection (w : Weight) (hw : ∀ k, w (-k) = w k) :
    Continuous (conjugateReflection (p := p) w hw) := by
  apply Isometry.continuous
  apply isometry_iff_dist_eq.mpr
  intro a b
  rw [dist_eq_norm,dist_eq_norm,← conjugateReflection_sub,norm_conjugateReflection]

theorem continuous_physicalRealPart (w : Weight) (hw : ∀ k, w (-k) = w k) :
    Continuous (physicalRealPart (p := p) w hw) := by
  change Continuous (fun a : WeightedCoeff w p => (1/2 : ℂ) • (a+conjugateReflection w hw a))
  exact (continuous_id.add (continuous_conjugateReflection w hw)).const_smul (1/2 : ℂ)

theorem continuous_physicalImagPart (w : Weight) (hw : ∀ k, w (-k) = w k) :
    Continuous (physicalImagPart (p := p) w hw) := by
  change Continuous (fun a : WeightedCoeff w p => (-Complex.I/2 : ℂ) • (a-conjugateReflection w hw a))
  exact (continuous_id.sub (continuous_conjugateReflection w hw)).const_smul (-Complex.I/2 : ℂ)

@[simp] theorem physicalRealPart_zero (w : Weight) (hw : ∀ k, w (-k) = w k) :
    physicalRealPart (p := p) w hw 0 = 0 := by
  apply Subtype.ext
  funext k
  simp [physicalRealPart]

@[simp] theorem physicalImagPart_zero (w : Weight) (hw : ∀ k, w (-k) = w k) :
    physicalImagPart (p := p) w hw 0 = 0 := by
  apply Subtype.ext
  funext k
  simp [physicalImagPart]

end NLS.WeightedCoeff
