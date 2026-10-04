import NLS.SequenceSpaces.SquareRootLifting
import NLS.ZakharovShabat.SourceBirkhoffInverseChart
import NLS.ZakharovShabat.SourceActionExponentDifferential

/-! # Realizing every nonnegative summable action sequence

Real square roots and the global Hilbert Birkhoff inverse realize every
nonnegative l1 sequence as the original spectral actions. Exponent
compatibility transports the same realization to every finite p >= 2.
-/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Every nonnegative summable sequence is realized by the original
spectral actions of a real Hilbert source, including infinitely many zeros. -/
theorem exists_hilbertSource_of_nonnegative_actions (b : RealCoeff 1) (hb : ∀ n, 0 ≤ b n) :
    ∃ φ : realTypeSourceSubmodule 2,
      ∀ n, sourceComplexAction (by simp) (by norm_num) n φ.val = (b n : ℂ) := by
  let f : ℤ → ℂ := fun n => (Real.sqrt (2*b n) : ℂ)
  have hsq (n : ℤ) : f n ^ 2 = (2:ℂ)*(b n:ℂ) := by
    dsimp only [f]
    exact_mod_cast Real.sq_sqrt (mul_nonneg (by norm_num) (hb n))
  have hmem : Memℓp f 2 := Coeff.memℓp_of_norm_sq_le (by simp)
    ((2:ℂ) • RealCoeff.complexCLM 1 b) f (by
      intro n
      rw [← norm_pow,hsq]
      rfl)
  let a : Coeff 2 := ⟨f,hmem⟩
  let x : RealCoeff 2 := Coeff.reCLM 2 a
  obtain ⟨W₀,B,W,s,D⟩ := exists_sourceBirkhoffMap_complex_analytic (p := 2) (by simp) (by norm_num)
  let φ := (D.realHomeomorph (le_refl 2)).symm (x,0)
  have hr : sourceRealBirkhoffMap (by simp) (by norm_num) s φ = (x,0) :=
    (D.realHomeomorph (le_refl 2)).apply_symm_apply (x,0)
  have hc := D.real_map_complex_inclusion φ
  rw [hr] at hc
  refine ⟨φ,fun n => ?_⟩
  have h := D.action_radius φ.val (D.real_subset φ.property) n
  rw [← hc] at h
  have hx (n : ℤ) : (x n : ℂ) = f n := by simp [x,a,f]
  change (x n : ℂ)^2+(0:ℂ)^2 = 2*sourceComplexAction (by simp) (by norm_num) n φ.val at h
  rw [hx,hsq] at h
  linear_combination -h/2

/-- The Hilbert realization keeps all original actions under exponent
inclusion, without requiring global Birkhoff surjectivity above two. -/
theorem exists_source_of_nonnegative_actions {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : 2 ≤ p)
    (b : RealCoeff 1) (hb : ∀ n, 0 ≤ b n) :
    ∃ φ : realTypeSourceSubmodule p, ∀ n, sourceComplexAction hp hp1 n φ.val = (b n:ℂ) := by
  obtain ⟨φ,hφ⟩ := exists_hilbertSource_of_nonnegative_actions b hb
  refine ⟨realTypeSourceExponentInclusion h2p φ,fun n => ?_⟩
  exact (sourceComplexAction_real_exponent (by simp) hp (by norm_num) hp1 h2p n φ).symm.trans (hφ n)

end NLS.ZakharovShabat
