import NLS.Articles.KdVPseudomeasures.SourceTheorem32
import NLS.KdV.HminusOneDirichletAllGaps

/-! The gap-only bound needed for the Wiener inverse characterization.
It holds for every original real H-minus-one potential, including every
low and collapsed gap. -/
noncomputable section
open Set Complex NLS.KdV NLS.WeightedCoeff
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures

theorem original_cartesianWeight_le_twice_gap (q : OriginalHminusOnePotential) (n : ℕ+) :
    hillHminusCanonicalCartesianWeight n (originalPeriodOneCoefficients q) ≤
      2*‖originalCanonicalGapValues q (n:ℤ)‖ := by
  let Q := originalPeriodOneCoefficients q
  let hQ := originalPeriodOneCoefficients_real q
  have hn0 : (n:ℤ)≠0 := by exact_mod_cast n.ne_zero
  have hg : ‖originalCanonicalGapValues q (n:ℤ)‖=
      hillHminusLabels Q hQ (2*(n:ℕ))-hillHminusLabels Q hQ (2*(n:ℕ)-1) := by
    simp only [originalCanonicalGapValues,if_neg hn0,Int.natAbs_natCast,
      originalHillLabels,Complex.norm_real,Real.norm_eq_abs]
    exact abs_of_nonneg (sub_nonneg.mpr (monotone_hillHminusLabels Q hQ (by omega)))
  obtain ⟨hl,hr⟩ := hillHminusDirichletLabels_mem_gap Q hQ n
  rw [hillHminusCanonicalCartesianWeight_eq_real n Q hQ,hg]
  have ha : |hillHminusDirichletLabels Q hQ n-
      (hillHminusLabels Q hQ (2*(n:ℕ)-1)+hillHminusLabels Q hQ (2*(n:ℕ)))/2| ≤
      hillHminusLabels Q hQ (2*(n:ℕ))-hillHminusLabels Q hQ (2*(n:ℕ)-1) :=
    abs_le.mpr ⟨by linarith,by linarith⟩
  linarith

/-- A single constant precedes all modes in the original real potential.
The native Birkhoff coordinates gain the exact half derivative over gaps. -/
theorem original_native_signed_half_gap_bound (q : OriginalHminusOnePotential) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℤ,
      ‖(Weight.signedSobolev (1/2) k:ℂ)*
        (hillHminusNativeComplexMap (originalPeriodOneCoefficients q)).val k‖ ≤
          C*‖originalCanonicalGapValues q k‖ := by
  let Q := originalPeriodOneCoefficients q
  have hQ := originalPeriodOneCoefficients_real q
  have hN := real_mem_hillHminusActionAngleNativeDomain Q hQ
  obtain ⟨U,_,hqU,_,C,hC,hF⟩ := exists_locally_uniform_actionAngle_original_energy_bound Q
    (real_mem_hillHminusActionAngleEnergyDomain Q hQ)
  have hp (n : ℕ+) :
      ‖(Weight.signedSobolev (1/2) (n:ℤ):ℂ)*(hillHminusNativeComplexMap Q).val (n:ℤ)‖ ≤
        (2*C)*‖originalCanonicalGapValues q (n:ℤ)‖ := by
    have h := hillHminusNativeComplexMap_positive_endpoint_bound 0 (by norm_num) Q hN C
      (hillHminusCanonicalCartesianWeight n Q) hC.le n (hF Q hqU n).2.1 (by simp)
    norm_num only [sub_zero,neg_zero,Real.rpow_zero,one_mul] at h
    exact h.trans (by
      have hb := mul_le_mul_of_nonneg_left (original_cartesianWeight_le_twice_gap q n) hC.le
      simpa only [mul_assoc,mul_left_comm,mul_comm] using hb)
  refine ⟨2*C,by positivity,?_⟩
  intro k
  rcases lt_trichotomy k 0 with hk | rfl | hk
  · let n : ℕ+ := ⟨k.natAbs,Int.natAbs_pos.mpr (ne_of_lt hk)⟩
    have he : -(n:ℤ)=k := by
      change -((k.natAbs:ℕ):ℤ)=k
      rw [Int.natCast_natAbs,abs_of_neg hk,neg_neg]
    have hz : ‖(hillHminusNativeComplexMap Q).val (-(n:ℤ))‖=
        ‖(hillHminusNativeComplexMap Q).val (n:ℤ)‖ := by
      rw [hillHminusNativeComplexMap_real Q hQ,Complex.norm_conj]
    have h := hp n
    rw [← he,Weight.signedSobolev_neg,norm_mul,hz,originalCanonicalGapValues_neg]
    simpa only [norm_mul] using h
  · rw [hillHminusNativeComplexMap_zero_mode,mul_zero,norm_zero,originalCanonicalGapValues_zero,
      norm_zero,mul_zero]
  · let n : ℕ+ := ⟨k.natAbs,Int.natAbs_pos.mpr (ne_of_gt hk)⟩
    have he : (n:ℤ)=k := by
      change ((k.natAbs:ℕ):ℤ)=k
      rw [Int.natCast_natAbs,abs_of_pos hk]
    simpa only [he] using hp n

end NLS.Articles.KdVPseudomeasures
