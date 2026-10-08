import NLS.ComplexAnalysis.ZeroMultiset
import NLS.ZakharovShabat.LinearWeightZeroCount
import NLS.ZakharovShabat.LinearWeightRootGap

/-! # Lemma 25.4's quantitative determinant roots

There are exactly two roots counted with analytic multiplicity, at the
explicit threshold, with the source radius and factor-six gap bound.
Identification with canonical periodic eigenvalues is a separate theorem.
-/
noncomputable section
open scoped Classical
open NLS.ComplexAnalysis
namespace NLS.ZakharovShabat

/-- The two roots, including repeated roots, with explicit localization and gap control. -/
theorem linearWeight_exists_resonantRoots (w : SpectralWeight) (hw : w.HasLinearFactor)
    (φ : WeightedCoeffPair w.toWeight 2) (n : ℤ) (hn : 8*‖φ‖^2 ≤ 1+|(n:ℝ)|) :
    ∃ x ∈ refinedResonantDisk n, ∃ y ∈ refinedResonantDisk n,
      resonantDeterminantExtension (by simp) w φ n x = 0 ∧
      resonantDeterminantExtension (by simp) w φ n y = 0 ∧
      (∀ z ∈ resonantStrip n, resonantDeterminantExtension (by simp) w φ n z = 0 ↔ z = x ∨ z = y) ∧
      (∀ z ∈ resonantStrip n,
        analyticOrderNatAt (resonantDeterminantExtension (by simp) w φ n) z = ({x,y} : Multiset ℂ).count z) ∧
      ‖x-(Real.pi:ℂ)*n‖ ≤ quadraticLocalizationRadius ‖φ‖ n ∧
      ‖y-(Real.pi:ℂ)*n‖ ≤ quadraticLocalizationRadius ‖φ‖ n ∧
      ‖x-y‖^2 ≤ 6*resonantBProductSup (by simp) w φ n := by
  obtain ⟨ha,_,hfin,horder,_,_,hcount⟩ := linearWeight_determinant_zeroCount w hw φ n hn
  have hsupp := hfin.subset
    (analyticZeroCount_support_subset (resonantDeterminantExtension (by simp) w φ n) (resonantStrip n))
  obtain ⟨x,hx,y,hy,hxz,hyz,hm⟩ := exists_two_analytic_zeros hsupp hcount
  have hlocal := linearWeight_determinant_root_localization w hw φ n hn
  have hxlocal := hlocal x hx hxz
  have hylocal := hlocal y hy hyz
  have hmult : ∀ z ∈ resonantStrip n,
      analyticOrderNatAt (resonantDeterminantExtension (by simp) w φ n) z = ({x,y} : Multiset ℂ).count z := by
    intro z hz
    simpa only [if_pos hz] using hm z
  refine ⟨x,hxlocal.2,y,hylocal.2,hxz,hyz,?_,hmult,hxlocal.1,hylocal.1,?_⟩
  · intro z hz
    constructor
    · intro hfz
      have hpz := analyticOrderNatAt_pos_of_zero (ha z hz) (horder z hz) hfz
      rw [hmult z hz] at hpz
      simpa using Multiset.count_pos.mp hpz
    · rintro (rfl | rfl)
      · exact hxz
      · exact hyz
  · exact linearWeight_determinant_root_gap_le w hw φ n hn x y hx hy hxz hyz

/-- Zero potential has its double root at the strip center, including n=0. -/
theorem linearWeight_zero_determinant_root_iff (w : SpectralWeight) (hw : w.HasLinearFactor)
    (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n) :
    resonantDeterminantExtension (by simp) w (0 : WeightedCoeffPair w.toWeight 2) n z = 0 ↔
      z = (Real.pi:ℂ)*n := by
  have hn : 8*‖(0 : WeightedCoeffPair w.toWeight 2)‖^2 ≤ 1+|(n:ℝ)| := by simp; positivity
  obtain ⟨x,_,_,_,hxz,_,_,_,hxloc,_,_⟩ := linearWeight_exists_resonantRoots w hw 0 n hn
  have hxcenter : x = (Real.pi:ℂ)*n := by
    simpa [quadraticLocalizationRadius, sub_eq_zero] using hxloc
  constructor
  · intro hzero
    have h := (linearWeight_determinant_root_localization w hw 0 n hn z hz hzero).1
    simpa [quadraticLocalizationRadius, sub_eq_zero] using h
  · intro heq
    simpa only [heq, hxcenter] using hxz


/-- The free root has analytic order exactly two, rather than two distinct roots. -/
theorem linearWeight_zero_determinant_order (w : SpectralWeight) (hw : w.HasLinearFactor) (n : ℤ) :
    analyticOrderNatAt (resonantDeterminantExtension (by simp) w
      (0 : WeightedCoeffPair w.toWeight 2) n) ((Real.pi:ℂ)*n) = 2 := by
  have hn : 8*‖(0 : WeightedCoeffPair w.toWeight 2)‖^2 ≤ 1+|(n:ℝ)| := by simp; positivity
  obtain ⟨x,_,y,_,_,_,_,hm,hx,hy,_⟩ := linearWeight_exists_resonantRoots w hw 0 n hn
  have hxcenter : x = (Real.pi:ℂ)*n := by
    simpa [quadraticLocalizationRadius, sub_eq_zero] using hx
  have hycenter : y = (Real.pi:ℂ)*n := by
    simpa [quadraticLocalizationRadius, sub_eq_zero] using hy
  simpa [hxcenter, hycenter] using hm ((Real.pi:ℂ)*n) (center_mem_resonantStrip n)

end NLS.ZakharovShabat
