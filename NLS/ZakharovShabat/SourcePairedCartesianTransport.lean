import NLS.ZakharovShabat.SourcePairedActionFlow
import NLS.SequenceSpaces.RealPairedActionCoordinates
import NLS.ComplexAnalysis.CartesianPlaneRotation

/-! # Exact complex rectangular transport along the complete paired action flow -/
noncomputable section
open Set Complex NLS.ComplexAnalysis
namespace NLS.ZakharovShabat.SourceBirkhoffMapComplexData
variable {W₀ B W : Set (CoeffPair 2)} {s : (k : ℤ) → CoeffPair 2 → DeletedCoeff 2 k}

theorem hilbertRealHomeomorph_complex_coordinates
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) (m : ℤ) :
    (((D.hilbertRealHomeomorph φ).1 m : ℂ),((D.hilbertRealHomeomorph φ).2 m : ℂ)) =
      ((sourceBirkhoffMap (by simp) (by norm_num) s φ.val).1 m,
       (sourceBirkhoffMap (by simp) (by norm_num) s φ.val).2 m) := by
  exact congrArg (fun z : Coeff 2 × Coeff 2 => (z.1 m,z.2 m)) (D.real_map_complex_inclusion φ)

/-- An unselected second index leaves the literal selected rectangular
pair at its first rotation speed, including when that pair is zero. -/
theorem birkhoff_pairedActionFlow_coordinates_of_ne_second
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) (k l m : ℤ) (hm : m ≠ l) (t : ℝ) :
    ((sourceBirkhoffMap (by simp) (by norm_num) s (D.hilbertPairedActionFlow φ k l t).val).1 m,
     (sourceBirkhoffMap (by simp) (by norm_num) s (D.hilbertPairedActionFlow φ k l t).val).2 m) =
      if m = k then cartesianPlaneRotation (-t)
        ((sourceBirkhoffMap (by simp) (by norm_num) s φ.val).1 m,
         (sourceBirkhoffMap (by simp) (by norm_num) s φ.val).2 m)
      else ((sourceBirkhoffMap (by simp) (by norm_num) s φ.val).1 m,
         (sourceBirkhoffMap (by simp) (by norm_num) s φ.val).2 m) := by
  have he := congrArg (fun z : RealCoeff 2 × RealCoeff 2 => (z.1 m,z.2 m))
    (D.hilbertRealHomeomorph_pairedActionFlow φ k l t)
  have hr := RealCoeff.pairedActionRotation_coordinates_of_ne_second (D.hilbertRealHomeomorph φ) k l m hm t
  have hc := congrArg (fun z : ℝ × ℝ => ((z.1 : ℂ),(z.2 : ℂ))) (he.trans hr)
  have hφ := D.hilbertRealHomeomorph_complex_coordinates φ m
  have hψ := D.hilbertRealHomeomorph_complex_coordinates (D.hilbertPairedActionFlow φ k l t) m
  change (((D.hilbertRealHomeomorph (D.hilbertPairedActionFlow φ k l t)).1 m : ℂ),
    ((D.hilbertRealHomeomorph (D.hilbertPairedActionFlow φ k l t)).2 m : ℂ)) = _ at hc
  rw [hψ] at hc
  by_cases hmk : m = k
  · rw [if_pos hmk] at hc ⊢
    rw [← hφ]
    simpa only [cartesianPlaneRotation,Real.cos_neg,Real.sin_neg,Complex.ofReal_neg,
      Complex.ofReal_sub,Complex.ofReal_add,Complex.ofReal_mul,neg_mul,neg_neg,sub_eq_add_neg] using hc
  · rw [if_neg hmk] at hc ⊢
    exact hc.trans hφ

end NLS.ZakharovShabat.SourceBirkhoffMapComplexData
