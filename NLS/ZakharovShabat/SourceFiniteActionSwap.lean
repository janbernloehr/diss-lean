import NLS.ZakharovShabat.SourceComponentSwapPoisson
import NLS.ZakharovShabat.SourceFiniteActionHamiltonian

/-! # Covariance of finite original action Hamiltonian fields -/
noncomputable section
set_option autoImplicit false
open Set NLS.Poisson
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The two reflected minus signs, from frequency covariance and the
anti-Poisson source swap, give covariance of the full finite action field. -/
theorem sourceFiniteActionHamiltonianVector_componentSwap
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : 2 ≤ p)
    (φ : realTypeSourceSubmodule p) (f g : ℤ → ℝ)
    (hfg : ∀ n : ℤ, g n = -f (-n)) (S : Finset ℤ) :
    sourceComponentSwap (sourceFiniteActionHamiltonianVector hp hp1 h2p f S φ.val) =
      sourceFiniteActionHamiltonianVector hp hp1 h2p g (S.image Neg.neg)
        (sourceComponentSwap φ.val) := by
  classical
  unfold sourceFiniteActionHamiltonianVector
  rw [map_sum,Finset.sum_image (fun _ _ _ _ h => neg_injective h)]
  apply Finset.sum_congr rfl
  intro k _
  rw [map_smul,sourceActionHamiltonianVector_componentSwap hp hp1 h2p φ k,hfg (-k),neg_neg]
  simp only [Complex.ofReal_neg,smul_neg,neg_smul]

namespace SourceBirkhoffMapComplexData
variable {hp : p ≠ ⊤} {hp1 : 1 < p}
variable {W₀ B X : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- The actual complex coordinate support reflects under source exchange.
Only original action reflection and closed-gap vanishing are used. -/
theorem complex_support_componentSwap
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X s)
    (φ : realTypeSourceSubmodule p) (S : Finset ℤ)
    (hz : ∀ n ∉ S, (sourceComplexBirkhoffMap hp hp1 s φ.val).1 n = 0 ∧
      (sourceComplexBirkhoffMap hp hp1 s φ.val).2 n = 0) :
    ∀ n ∉ S.image Neg.neg,
      (sourceComplexBirkhoffMap hp hp1 s (sourceComponentSwap φ.val)).1 n = 0 ∧
      (sourceComplexBirkhoffMap hp hp1 s (sourceComponentSwap φ.val)).2 n = 0 := by
  classical
  intro n hn
  have hneg : -n ∉ S := fun h => hn (Finset.mem_image.mpr ⟨-n,h,neg_neg n⟩)
  have hact : sourceComplexAction hp hp1 n (sourceComponentSwap φ.val) = 0 := by
    rw [sourceComplexAction_componentSwap hp hp1 φ n,
      ← D.complex_map_action φ.val (D.real_subset φ.property) (-n),(hz (-n) hneg).1,zero_mul]
  rw [sourceComplexAction_eq_sourceRealAction hp hp1 n _ (sourceComponentSwap_realType φ.val φ.property)] at hact
  have hgap := (sourceRealAction_nonneg_and_eq_zero_iff_gap_zero hp hp1 _
    (sourceComponentSwap_realType φ.val φ.property) n).2.2.mp hact
  have hr := D.real_closed_gap_zero _ (D.real_subset (sourceComponentSwap_realType φ.val φ.property))
    (sourceComponentSwap_realType φ.val φ.property) n hgap
  simp only [sourceComplexBirkhoffMap,Birkhoff.rectangularToComplex_fst,
    Birkhoff.rectangularToComplex_snd,hr.1,hr.2,mul_zero,sub_zero,add_zero,and_self]

end SourceBirkhoffMapComplexData

end NLS.ZakharovShabat
