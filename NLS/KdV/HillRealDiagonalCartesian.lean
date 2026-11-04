import NLS.KdV.HillOnIndexRealPhysicalTerminal
import NLS.KdV.HillCanonicalDiagonalCartesian

/-! Intrinsic diagonal factors on the entire real native source form:
conjugacy and exact ORIGINAL gap modulus, including closed gaps. -/
noncomputable section
open Set Complex
open scoped Classical
namespace NLS.KdV

theorem hillHminusDiagonalCartesian_real_phase (n : ℕ+) (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) (hgap : hillHminusCanonicalGapSquare n q ≠ 0) :
    ∃ a : ℝ,
      hillHminusDiagonalCartesianPlus n q =
        ((hillHminusLabels q hr (2*(n:ℕ))-hillHminusLabels q hr (2*(n:ℕ)-1):ℝ):ℂ)*Complex.exp (I*(a:ℂ)) ∧
      hillHminusDiagonalCartesianMinus n q =
        ((hillHminusLabels q hr (2*(n:ℕ))-hillHminusLabels q hr (2*(n:ℕ)-1):ℝ):ℂ)*Complex.exp (-I*(a:ℂ)) := by
  obtain ⟨P,hq,_⟩ := exists_hillProductEquationPatch q hr
  have he := hillHminusDiagonalCartesian_eq_patch_of_real P n q hq hr
  rw [he.1,he.2]
  exact P.exists_real_original_diagonal_phase n q hq hr hgap

theorem hillHminusDiagonalCartesian_conjugate_of_real (n : ℕ+) (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) :
    hillHminusDiagonalCartesianMinus n q = star (hillHminusDiagonalCartesianPlus n q) := by
  by_cases hg : hillHminusCanonicalGapSquare n q = 0
  · have hz := hillHminusDiagonalCartesian_zero_of_real_closed_gap n q hr hg
    simp only [hz.1,hz.2,star_zero]
  · obtain ⟨a,hp,hm⟩ := hillHminusDiagonalCartesian_real_phase n q hr hg
    rw [hp,hm]
    change _ = (starRingEnd ℂ) _
    rw [map_mul,← Complex.exp_conj]
    simp

theorem norm_hillHminusDiagonalCartesian_of_real_open_gap (n : ℕ+) (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) (hg : hillHminusCanonicalGapSquare n q ≠ 0) :
    ‖hillHminusDiagonalCartesianPlus n q‖ = hillHminusLabels q hr (2*(n:ℕ))-hillHminusLabels q hr (2*(n:ℕ)-1) ∧
    ‖hillHminusDiagonalCartesianMinus n q‖ = hillHminusLabels q hr (2*(n:ℕ))-hillHminusLabels q hr (2*(n:ℕ)-1) := by
  obtain ⟨a,hp,hm⟩ := hillHminusDiagonalCartesian_real_phase n q hr hg
  have hnonneg : 0 ≤ hillHminusLabels q hr (2*(n:ℕ))-hillHminusLabels q hr (2*(n:ℕ)-1) :=
    sub_nonneg.mpr (monotone_hillHminusLabels q hr (by omega))
  rw [hp,hm]
  have hnorm : ‖((hillHminusLabels q hr (2*(n:ℕ))-hillHminusLabels q hr (2*(n:ℕ)-1):ℝ):ℂ)‖ =
      hillHminusLabels q hr (2*(n:ℕ))-hillHminusLabels q hr (2*(n:ℕ)-1) := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hnonneg]
  have heplus : ‖Complex.exp (I*(a:ℂ))‖ = 1 := by simp [Complex.norm_exp,Complex.mul_re]
  have heminus : ‖Complex.exp (-I*(a:ℂ))‖ = 1 := by simp [Complex.norm_exp,Complex.mul_re]
  simp only [norm_mul,hnorm,heplus,heminus,mul_one,and_self]

theorem norm_hillHminusDiagonalCartesian_of_real (n : ℕ+) (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) :
    ‖hillHminusDiagonalCartesianPlus n q‖ = hillHminusLabels q hr (2*(n:ℕ))-hillHminusLabels q hr (2*(n:ℕ)-1) ∧
    ‖hillHminusDiagonalCartesianMinus n q‖ = hillHminusLabels q hr (2*(n:ℕ))-hillHminusLabels q hr (2*(n:ℕ)-1) := by
  by_cases hg : hillHminusCanonicalGapSquare n q = 0
  · have hz := hillHminusDiagonalCartesian_zero_of_real_closed_gap n q hr hg
    have he := hillHminusCanonicalGapSquare_eq_real q hr n
    rw [hg] at he
    have hgap : hillHminusLabels q hr (2*(n:ℕ))-hillHminusLabels q hr (2*(n:ℕ)-1) = 0 := by
      have hs := eq_zero_of_pow_eq_zero he.symm
      exact_mod_cast hs
    simp only [hz.1,hz.2,norm_zero,hgap,and_self]
  · exact norm_hillHminusDiagonalCartesian_of_real_open_gap n q hr hg

theorem norm_hillHminusDiagonalPhaseSquare_of_real (n : ℕ+) (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) (hg : hillHminusCanonicalGapSquare n q ≠ 0) :
    ‖hillHminusDiagonalPhaseSquare n q‖ = 1 := by
  have hn := norm_hillHminusDiagonalCartesian_of_real n q hr
  have hne := (hillHminusDiagonalCartesian_ne_zero_of_gap n q
    (real_mem_hillHminusPhysicalAbelianDomain q hr) hg).1
  have hnormne := norm_ne_zero_iff.mpr hne
  rw [hn.1] at hnormne
  rw [hillHminusDiagonalPhaseSquare,norm_div,hn.1,hn.2,div_self hnormne]

end NLS.KdV
