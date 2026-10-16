import NLS.SequenceSpaces.FiniteModification
import NLS.ZakharovShabat.SourceRealTypeBanachSpace
import NLS.ZakharovShabat.SourceAdaptedClosingMapDerivative
import NLS.ZakharovShabat.SourceResonantCenterGapBound
import NLS.ZakharovShabat.SourceBirkhoffGapNormEquivalence

/-! # Weighted adapted coordinates from weighted gaps

Weighted gap membership implies membership of the actual adapted closing
coordinates, with a cutoff independent of the positive even weight.
The original source is not assumed to carry that weight.
-/

noncomputable section

namespace NLS.ZakharovShabat
open Set Metric
open scoped ENNReal
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Every sufficiently late adapted map inherits any positive even gap weight. -/
theorem sourceAdaptedClosingMap_mem_weighted_of_gap
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceSubmodule p) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ M : ℕ, N ≤ M → ∀ w : Weight,
      (∀ n : ℤ, w (-n) = w n) →
      Memℓp (fun n : ℤ => (w n : ℂ)*sourcePeriodicGapDisplacement hp hp1 φ.val n) p →
      Memℓp (fun n : ℤ => (w n : ℂ)*(sourceAdaptedClosingMap hp φ.val M).fst n) p ∧
        Memℓp (fun n : ℤ => (w n : ℂ)*(sourceAdaptedClosingMap hp φ.val M).snd n) p := by
  obtain ⟨N₁,hN₁,U,_,hφU,hbound⟩ := exists_uniform_sourceResonantCenter_gap_bound hp hp1 φ.val
  obtain ⟨r,hr,N₂,_,hdata⟩ := exists_fixedBall_sourceAdaptedClosingMap_derivative hp hp1 φ.val 1 (by norm_num)
  refine ⟨max N₁ N₂,by omega,?_⟩
  intro M hM w hw hg
  have hmem := ((hdata M (by omega)).2.1 φ.val (mem_ball_self (by positivity))).1
  have hcoord := sourceAdaptedClosingMap_apply_of_mem hp φ.val M hmem
  let g : Coeff p := ⟨_,hg⟩
  let S := Finset.Icc (-(M:ℤ)) M
  have hfst : Memℓp (fun n : ℤ => if M ≤ n.natAbs then
      (w n : ℂ)*(sourceAdaptedClosingMap hp φ.val M).fst n else 0) p := by
    apply ((Coeff.reflection g).property.norm.const_mul (2:ℝ)).mono
    intro n
    by_cases hn : M ≤ n.natAbs
    · rw [if_pos hn,(hcoord n).1,if_pos hn]
      have hb := (hbound φ.val hφU φ.property (-n) (by simpa only [Int.natAbs_neg] using
        (show N₁ ≤ n.natAbs by omega))).2
      simpa only [Coeff.reflection_apply,g,norm_mul,Complex.norm_real,
        Real.norm_eq_abs,abs_of_pos (w.positive _),hw,mul_left_comm (w n) 2] using
          mul_le_mul_of_nonneg_left hb (w.positive n).le
    · simp only [if_neg hn,norm_zero]
      positivity
  have hsnd : Memℓp (fun n : ℤ => if M ≤ n.natAbs then
      (w n : ℂ)*(sourceAdaptedClosingMap hp φ.val M).snd n else 0) p := by
    apply (hg.norm.const_mul (2:ℝ)).mono
    intro n
    by_cases hn : M ≤ n.natAbs
    · rw [if_pos hn,(hcoord n).2,if_pos hn]
      have hb := (hbound φ.val hφU φ.property n (by omega)).1
      simpa only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (w.positive _),
        mul_left_comm (w n) 2] using mul_le_mul_of_nonneg_left hb (w.positive n).le
    · simp only [if_neg hn,norm_zero]
      positivity
  constructor
  · apply memℓp_of_eq_outside_finset hfst S
    intro n hn
    have hnm : M ≤ n.natAbs := by simp only [S,Finset.mem_Icc] at hn; omega
    simp only [if_pos hnm]
  · apply memℓp_of_eq_outside_finset hsnd S
    intro n hn
    have hnm : M ≤ n.natAbs := by simp only [S,Finset.mem_Icc] at hn; omega
    simp only [if_pos hnm]
end NLS.ZakharovShabat

namespace NLS.ZakharovShabat
open scoped ENNReal
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceBirkhoffMapComplexData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}

/-- Weighted real Birkhoff outputs imply weighted adapted closing coordinates.
Recovering weighted regularity of the original source is a further step. -/
theorem adaptedClosingMap_mem_weighted_of_real_map
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (φ : realTypeSourceSubmodule p) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ M : ℕ, N ≤ M → ∀ w : Weight,
      (∀ n : ℤ, w (-n) = w n) →
      (Memℓp (fun n : ℤ => w n * (sourceRealBirkhoffMap hp hp1 s φ).1 n) p ∧
        Memℓp (fun n : ℤ => w n * (sourceRealBirkhoffMap hp hp1 s φ).2 n) p) →
      Memℓp (fun n : ℤ => (w n : ℂ)*(sourceAdaptedClosingMap hp φ.val M).fst n) p ∧
        Memℓp (fun n : ℤ => (w n : ℂ)*(sourceAdaptedClosingMap hp φ.val M).snd n) p := by
  obtain ⟨N,hN,h⟩ := sourceAdaptedClosingMap_mem_weighted_of_gap hp hp1 φ
  exact ⟨N,hN,fun M hM w hw hxy => h M hM w hw
    ((D.weighted_gap_mem_iff_real_map_mem w φ).mpr hxy)⟩
end SourceBirkhoffMapComplexData
end NLS.ZakharovShabat
