import NLS.ZakharovShabat.ResonantCubicPerturbation
import NLS.ZakharovShabat.ResonantTwoModeCubic

/-! # Physical Fourier support and finite outer support of the cubic perturbation

These estimates support the unresolved final weighted gap sum on dissertation
p.44. They do not prove the actual counted-root gap asymptotics.
-/
noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

private theorem cubicSupport_tsum_zero (f : ℤ → ℂ) (hf : ∀ k, f k = 0) : (∑' k, f k) = 0 := by
  simp only [hf,tsum_zero]

/-- Positive cubic terms vanish outside the interval forced by physical input supports. -/
theorem resonantCubic_positive_zero_of_support (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n m : ℤ) (z : ℂ)
    (hz : z ∈ resonantStrip m)
    (hfst : ∀ k : ℤ, k < -(2*n) ∨ 0 < k → φ.fst.val k = 0)
    (hsnd : ∀ k : ℤ, k < 0 ∨ 2*n < k → φ.snd.val k = 0)
    (hm : m < -n ∨ 2*n < m) :
    weightedResonantParityTermFunction hp w φ m 2 0 1 0 z = 0 := by
  simp only [weightedResonantParityTermFunction,weightedPotentialExtension_eq hp w φ m z hz,
    pow_zero,pow_two,one_apply_eq_self,mul_apply_eq_comp,resonantCoordinates_one,
    weightedPotentialInverse_sq_snd_apply,weightedResonantSource_zero_snd]
  apply cubicSupport_tsum_zero
  intro l
  apply cubicSupport_tsum_zero
  intro k
  by_cases ha : 0 ≤ m-l ∧ m-l ≤ 2*n
  · by_cases hb : -(2*n) ≤ l-k ∧ l-k ≤ 0
    · by_cases hc : 0 ≤ k+m ∧ k+m ≤ 2*n
      · omega
      · simp [hsnd (k+m) (by omega)]
    · simp [hfst (l-k) (by omega)]
  · simp [hsnd (m-l) (by omega)]

/-- The reflected negative cubic term has the same finite outer support. -/
theorem resonantCubic_negative_zero_of_support (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n m : ℤ) (z : ℂ)
    (hz : z ∈ resonantStrip m)
    (hfst : ∀ k : ℤ, k < -(2*n) ∨ 0 < k → φ.fst.val k = 0)
    (hsnd : ∀ k : ℤ, k < 0 ∨ 2*n < k → φ.snd.val k = 0)
    (hm : m < -n ∨ 2*n < m) :
    weightedResonantParityTermFunction hp w φ m 2 0 0 1 z = 0 := by
  simp only [weightedResonantParityTermFunction,weightedPotentialExtension_eq hp w φ m z hz,
    pow_zero,pow_two,one_apply_eq_self,mul_apply_eq_comp,resonantCoordinates_zero,
    weightedPotentialInverse_sq_fst_apply,weightedResonantSource_one_fst]
  apply cubicSupport_tsum_zero
  intro l
  apply cubicSupport_tsum_zero
  intro k
  by_cases ha : -(2*n) ≤ -m-l ∧ -m-l ≤ 0
  · by_cases hb : 0 ≤ l-k ∧ l-k ≤ 2*n
    · by_cases hc : -(2*n) ≤ k-m ∧ k-m ≤ 0
      · omega
      · simp [hfst (k-m) (by omega)]
    · simp [hsnd (l-k) (by omega)]
  · simp [hfst (-m-l) (by omega)]

/-- First-component support in [-2n,0] and second-component support in [0,2n]. -/
def CubicFourierSupport (w : SpectralWeight) (n : ℤ) (φ : WeightedCoeffPair w.toWeight p) : Prop :=
  (∀ k : ℤ, k < -(2*n) ∨ 0 < k → φ.fst.val k = 0) ∧
  (∀ k : ℤ, k < 0 ∨ 2*n < k → φ.snd.val k = 0)

omit [Fact (1 ≤ p)] in
/-- Addition preserves the specified physical Fourier supports. -/
theorem CubicFourierSupport.add (w : SpectralWeight) (n : ℤ) (A B : WeightedCoeffPair w.toWeight p)
    (hA : CubicFourierSupport w n A) (hB : CubicFourierSupport w n B) : CubicFourierSupport w n (A+B) := by
  constructor
  · intro k hk
    change A.fst.val k+B.fst.val k=0
    simp [hA.1 k hk,hB.1 k hk]
  · intro k hk
    change A.snd.val k+B.snd.val k=0
    simp [hA.2 k hk,hB.2 k hk]

omit [Fact (1 ≤ p)] in
/-- Complex scaling preserves the specified physical Fourier supports. -/
theorem CubicFourierSupport.smul (w : SpectralWeight) (n : ℤ) (A : WeightedCoeffPair w.toWeight p)
    (hA : CubicFourierSupport w n A) (s : ℂ) : CubicFourierSupport w n (s • A) := by
  constructor
  · intro k hk
    change s*A.fst.val k=0
    simp [hA.1 k hk]
  · intro k hk
    change s*A.snd.val k=0
    simp [hA.2 k hk]

/-- The actual cubic perturbation supremum vanishes outside [-n,2n]. -/
theorem resonantCubicPerturbationSup_outside (hp : p ≠ ⊤) (w : SpectralWeight)
    (A B : WeightedCoeffPair w.toWeight p) (n m : ℤ) (s : ℂ) (i j : Fin 2)
    (hA : CubicFourierSupport w n A) (hB : CubicFourierSupport w n B)
    (hi : (i=0 ∧ j=1) ∨ (i=1 ∧ j=0)) (hm : m < -n ∨ 2*n < m) :
    resonantCubicPerturbationSup hp w A B m s i j = 0 := by
  have hS := CubicFourierSupport.smul w n A hA s
  have hC := CubicFourierSupport.add w n _ _ hS (CubicFourierSupport.smul w n B hB (s^3))
  have hb := weightedStripSup_bounds w m
    (fun z => weightedResonantParityTermFunction hp w (s • A+s^3 • B) m 2 0 i j z -
      weightedResonantParityTermFunction hp w (s • A) m 2 0 i j z) 0 (by
        intro z hz
        rcases hi with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · rw [resonantCubic_negative_zero_of_support hp w _ n m z hz hC.1 hC.2 hm,
            resonantCubic_negative_zero_of_support hp w _ n m z hz hS.1 hS.2 hm]
          simp
        · rw [resonantCubic_positive_zero_of_support hp w _ n m z hz hC.1 hC.2 hm,
            resonantCubic_positive_zero_of_support hp w _ n m z hz hS.1 hS.2 hm]
          simp)
  exact le_antisymm hb.2.1 hb.1

/-- Finite outer support makes the signed fourth-power supremum tail summable. -/
theorem resonantCubicPerturbationSup_fourth_summable (hp : p ≠ ⊤) (w : SpectralWeight)
    (A B : WeightedCoeffPair w.toWeight p) (n : ℤ) (s : ℂ) (i j : Fin 2)
    (hA : CubicFourierSupport w n A) (hB : CubicFourierSupport w n B)
    (hi : (i=0 ∧ j=1) ∨ (i=1 ∧ j=0)) (N : ℕ) :
    Summable (fun m : ℤ => if N ≤ m.natAbs then (resonantCubicPerturbationSup hp w A B m s i j)^4 else 0) := by
  apply summable_of_hasFiniteSupport
  apply (Set.finite_Icc (-n) (2*n)).subset
  intro m hm
  by_contra h
  have hz := resonantCubicPerturbationSup_outside hp w A B n m s i j hA hB hi (by
    change ¬(-n ≤ m ∧ m ≤ 2*n) at h
    omega)
  simp [Function.mem_support,hz] at hm

/-- The two-mode background has the required physical support. -/
theorem twoModeResonantPotential_cubicSupport (w : SpectralWeight) (n : ℤ) (hn : 0 < n) (s : ℂ) :
    CubicFourierSupport w n (twoModeResonantPotential (p := p) w n s) := by
  constructor
  · intro k hk
    rw [twoModeResonantPotential_fst w n hn]
    rw [if_neg (by omega)]
  · intro k hk
    rw [twoModeResonantPotential_snd w n hn]
    rw [if_neg (by omega)]

/-- A nonnegative target index places the resonant perturbation in the same support. -/
theorem singleResonantPotential_cubicSupport (w : SpectralWeight) (n : ℤ) (hn : 0 ≤ n) (a b : ℂ) :
    CubicFourierSupport w n (singleResonantPotential (p := p) w n a b) := by
  constructor
  · intro k hk
    rw [singleResonantPotential_fst]
    rw [if_neg (by omega)]
  · intro k hk
    rw [singleResonantPotential_snd]
    rw [if_neg (by omega)]

end NLS.ZakharovShabat
