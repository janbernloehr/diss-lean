import Mathlib.Data.PNat.Basic
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Analysis.Complex.Basic

/-! # The exact odd signed extension of positive real frequencies -/
noncomputable section
set_option autoImplicit false
namespace NLS

def signedPositiveFrequency (ω : ℕ+ → ℝ) (j : ℤ) : ℝ :=
  if h : 0<j then ω ⟨j.toNat,by omega⟩
  else if h : j<0 then -ω ⟨(-j).toNat,by omega⟩ else 0

@[simp] theorem signedPositiveFrequency_zero (ω : ℕ+ → ℝ) : signedPositiveFrequency ω 0=0 := by
  simp only [signedPositiveFrequency,lt_self_iff_false,↓reduceDIte]

@[simp] theorem signedPositiveFrequency_positive (ω : ℕ+ → ℝ) (n : ℕ+) :
    signedPositiveFrequency ω n=ω n := by
  have hn : (0 : ℤ)<n := by exact_mod_cast n.pos
  rw [signedPositiveFrequency,dif_pos hn]
  apply congrArg ω
  apply Subtype.ext
  exact Int.toNat_natCast n.val

theorem signedPositiveFrequency_neg (ω : ℕ+ → ℝ) (j : ℤ) :
    signedPositiveFrequency ω (-j)= -signedPositiveFrequency ω j := by
  rcases lt_trichotomy 0 j with h|h|h
  · simp only [signedPositiveFrequency,dif_pos h,dif_neg (by omega : ¬0< -j),
      dif_pos (by omega : -j<0),neg_neg]
  · subst j
    simp only [neg_zero,signedPositiveFrequency_zero]
  · simp only [signedPositiveFrequency,dif_neg (by omega : ¬0<j),dif_pos h,
      dif_pos (by omega : 0< -j),neg_neg]

theorem continuous_signedPositiveFrequency {X : Type*} [TopologicalSpace X]
    (ω : X → ℕ+ → ℝ) (hω : ∀ n, Continuous (fun x => ω x n)) (j : ℤ) :
    Continuous (fun x => signedPositiveFrequency (ω x) j) := by
  unfold signedPositiveFrequency
  split_ifs
  · exact hω _
  · exact (hω _).neg
  · exact continuous_const

end NLS
