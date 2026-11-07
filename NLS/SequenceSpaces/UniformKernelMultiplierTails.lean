import NLS.SequenceSpaces.FiniteExponentTail
import NLS.SequenceSpaces.PuncturedLattice

/-! Uniformly small coefficient tails turn bounded kernels with vanishing
columns into uniformly vanishing multipliers. No uniform summable tail
of a separate row majorant is needed. -/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.Coeff

theorem exists_uniform_kernel_multiplier_tail
    {E : Type*} (U : Set E) (b : E → ℤ → ℝ) (M C : ℝ) (hM : 0≤M) (hC : 0≤C)
    (hb : ∀ a∈U, ∀ k, 0≤b a k ∧ b a k≤M)
    (ht : ∀ ε > (0:ℝ), ∃ K : ℕ, ∀ a∈U, ∀ k : ℤ, K≤k.natAbs → b a k≤ε)
    (P : ℤ → ℤ → ℝ) (hP : ∀ n k, 0≤P n k ∧ P n k≤C)
    (hcol : ∀ k : ℤ, ∀ ε > (0:ℝ), ∃ N : ℕ, ∀ n : ℤ, N≤n.natAbs → P n k≤ε) :
    ∀ ε > (0:ℝ), ∃ N : ℕ, ∀ a∈U, ∀ n : ℤ, N≤n.natAbs →
      ∀ k : ℤ, P n k*b a k≤ε := by
  classical
  intro ε hε
  let δ := ε/(C+M+1)
  have hden : 0<C+M+1 := by linarith
  have hδ : 0<δ := div_pos hε hden
  have he : δ*(C+M+1)=ε := div_mul_cancel₀ ε hden.ne'
  have hδM : δ*M≤ε := by nlinarith
  have hδC : C*δ≤ε := by nlinarith
  obtain ⟨K,hK⟩ := ht δ hδ
  choose N hN using fun k => hcol k δ hδ
  let s := Finset.Icc (-(K:ℤ)) (K:ℤ)
  refine ⟨s.sup N,?_⟩
  intro a ha n hn k
  by_cases hk : k∈s
  · exact (mul_le_mul (hN k n ((Finset.le_sup hk).trans hn)) (hb a ha k).2
      (hb a ha k).1 hδ.le).trans hδM
  · have hkK : K≤k.natAbs := by simp only [s,Finset.mem_Icc] at hk;omega
    exact (mul_le_mul (hP n k).2 (hK a ha k hkK) (hb a ha k).1 hC).trans hδC

theorem exists_uniform_punctured_multiplier_tail
    {E : Type*} (U : Set E) (b : E → ℤ → ℝ) (M : ℝ) (hM : 0≤M)
    (hb : ∀ a∈U, ∀ k, 0≤b a k ∧ b a k≤M)
    (ht : ∀ ε > (0:ℝ), ∃ K : ℕ, ∀ a∈U, ∀ k : ℤ, K≤k.natAbs → b a k≤ε) :
    ∀ ε > (0:ℝ), ∃ N : ℕ, ∀ a∈U, ∀ n : ℤ, N≤n.natAbs →
      ∀ k : ℤ, ‖puncturedLattice 2 (by norm_num) (n-k)‖*b a k≤ε := by
  apply exists_uniform_kernel_multiplier_tail U b M 1 hM (by norm_num) hb ht
  · intro n k
    refine ⟨norm_nonneg _,?_⟩
    by_cases h : n-k=0
    · simp [h]
    · simp only [puncturedLattice_apply,if_neg h,norm_inv,Complex.norm_intCast]
      apply inv_le_one_of_one_le₀
      exact_mod_cast Int.one_le_abs h
  · intro k ε hε
    obtain ⟨N,hN⟩ := exists_natAbs_norm_lt (by norm_num : 0<(2:ℝ≥0∞).toReal)
      (shift k (puncturedLattice 2 (by norm_num))) hε
    exact ⟨N,fun n hn => by simpa only [shift_apply] using (hN n hn).le⟩

end NLS.Coeff
