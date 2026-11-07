import NLS.SequenceSpaces.OddPositiveFrequency
import NLS.SequenceSpaces.Reflection

/-! The literal odd extension of a positive frequency correction is
reflection subtraction. Its cubic free part retains every signed index. -/
noncomputable section
open Set Complex
namespace NLS.LpSequence

theorem positiveScalarExtension_nonpos (f : ℕ+ → ℂ) (k : ℤ) (hk : k ≤ 0) :
    positiveScalarExtension f k=0 := by
  apply positiveScalarExtension_zero_of_not_mem_range
  rintro ⟨n,hn⟩
  have hp : (0:ℤ)<((n:ℕ):ℤ) := by exact_mod_cast n.pos
  change ((n:ℕ):ℤ)=k at hn
  omega

theorem eq_of_odd_positive {f g : ℤ → ℂ}
    (hf : ∀ k, f (-k)= -f k) (hg : ∀ k, g (-k)= -g k)
    (hp : ∀ n : ℕ+, f (n:ℤ)=g (n:ℤ)) : f=g := by
  have hpos (k : ℤ) (hk : 0<k) : f k=g k := by
    let n : ℕ+ := ⟨k.toNat,by omega⟩
    have he : (n:ℤ)=k := Int.toNat_of_nonneg hk.le
    rw [← he]
    exact hp n
  funext k
  rcases lt_trichotomy k 0 with hk | hk | hk
  · have he := hpos (-k) (by omega)
    rw [hf,hg] at he
    exact neg_injective he
  · subst k
    have hF := hf 0
    have hG := hg 0
    simp only [neg_zero] at hF hG
    have hf0 : f 0=0 := by linear_combination (1/2:ℂ)*hF
    have hg0 : g 0=0 := by linear_combination (1/2:ℂ)*hG
    rw [hf0,hg0]
  · exact hpos k hk

theorem positiveScalarExtension_sub_reflection (f : ℕ+ → ℝ) (k : ℤ) :
    positiveScalarExtension (fun n => (f n:ℂ)) k-
      positiveScalarExtension (fun n => (f n:ℂ)) (-k) = (oddPositiveFrequency f k:ℂ) := by
  have he : (fun k => positiveScalarExtension (fun n => (f n:ℂ)) k-
      positiveScalarExtension (fun n => (f n:ℂ)) (-k)) =
        (fun k => (oddPositiveFrequency f k:ℂ)) := by
    apply eq_of_odd_positive
    · intro j
      simp only [neg_neg]
      ring
    · intro j
      rw [oddPositiveFrequency_neg,ofReal_neg]
    · intro n
      rw [positiveScalarExtension_apply,positiveScalarExtension_nonpos _ _ (by
        have hn : (0:ℤ)<(n:ℤ) := by exact_mod_cast n.pos
        omega),sub_zero,oddPositiveFrequency_positive]
  exact congrFun he k

theorem oddPositiveFrequency_sub (f g : ℕ+ → ℝ) (k : ℤ) :
    oddPositiveFrequency (fun n => f n-g n) k = oddPositiveFrequency f k-oddPositiveFrequency g k := by
  by_cases hk : k=0
  · subst k
    simp only [oddPositiveFrequency_zero,sub_zero]
  · simp only [oddPositiveFrequency,dif_neg hk,mul_sub]

theorem oddPositiveFrequency_cubic (c : ℝ) (k : ℤ) :
    oddPositiveFrequency (fun n => c*(n:ℝ)^3) k = c*(k:ℝ)^3 := by
  have he : (fun k => (oddPositiveFrequency (fun n => c*(n:ℝ)^3) k:ℂ)) =
      (fun k : ℤ => ((c*(k:ℝ)^3:ℝ):ℂ)) := by
    apply eq_of_odd_positive
    · intro j
      rw [oddPositiveFrequency_neg,ofReal_neg]
    · intro j
      push_cast
      ring
    · intro n
      rw [oddPositiveFrequency_positive]
      rfl
  exact ofReal_injective (congrFun he k)

theorem positive_cubic_correction_sub_reflection (f : ℕ+ → ℝ) (c : ℝ) (k : ℤ) :
    positiveScalarExtension (fun n => (f n:ℂ)-(c:ℂ)*(n:ℂ)^3) k-
      positiveScalarExtension (fun n => (f n:ℂ)-(c:ℂ)*(n:ℂ)^3) (-k) =
        (oddPositiveFrequency f k:ℂ)-(c:ℂ)*(k:ℂ)^3 := by
  have hf : (fun n : ℕ+ => (f n:ℂ)-(c:ℂ)*(n:ℂ)^3) =
      (fun n => ((f n-c*(n:ℝ)^3:ℝ):ℂ)) := by funext n; push_cast; rfl
  rw [hf,positiveScalarExtension_sub_reflection,oddPositiveFrequency_sub,oddPositiveFrequency_cubic]
  push_cast
  rfl

end NLS.LpSequence
