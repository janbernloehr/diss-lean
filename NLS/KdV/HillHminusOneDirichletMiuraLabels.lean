import NLS.KdV.HillDirichletMiuraZeroIndex
import NLS.KdV.HillHminusOneDirichletSpectrumExhaustion
import Mathlib.Order.WellFounded

/-! # Exact all-index identification with squared canonical NLS Dirichlet roots

Positive source indices give positive frequencies. Squaring and undoing
the fixed real Miura energy shift gives a strictly increasing enumeration
of all actual Hill Dirichlet energies. Exhaustive ordered-enumeration
uniqueness fixes every index, not only a high tail or an unknown offset.
-/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.ZakharovShabat
open scoped ComplexConjugate
namespace NLS.KdV

theorem HillHminusMiuraChart.lift_real_of_profile_real (C : HillHminusMiuraChart)
    (q : PeriodOneHminusOne) (hreal : star (C.physicalProfile q) = C.physicalProfile q) :
    ∀ k : ℤ, C.lift q (-k) = conj (C.lift q k) := by
  intro k
  have he := congrArg (fun v : IntervalL2 => NLS.Fourier.intervalFourierCoefficient 1 v (-k)) hreal
  rw [NLS.Fourier.intervalFourierCoefficient_Lp_star,C.physicalProfile_coefficient,
    C.physicalProfile_coefficient,neg_neg] at he
  exact he.symm

theorem HillHminusMiuraChart.dirichletEnergy_eq_source_root_sq
    (C : HillHminusMiuraChart) (q : PeriodOneHminusOne) (hq : q ∈ C.domain)
    (hr : IsRealPeriodOneHminusOne q) (c : ℝ) (hc : C.energyShift = (c : ℂ)^2)
    (hreal : star (C.physicalProfile q) = C.physicalProfile q) (n : ℕ+) :
    (hillHminusDirichletEnergy q hr n : ℂ) =
      (canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .dirichlet
        (hillDirichletMiuraSource (C.lift q)) (n : ℤ))^2-C.energyShift := by
  let P := hillDirichletMiuraSource (C.lift q)
  let v : ℤ → ℂ := canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .dirichlet P
  have hP : IsRealType (CoeffPair.toMax 2 P) := C.dirichlet_source_real q hreal
  have hu := C.lift_real_of_profile_real q hreal
  have hvreal (k : ℤ) : ((v k).re : ℂ) = v k := by
    apply Complex.ext
    · rfl
    · exact (canonicalPeriodOneBoundaryRoots_im_eq_zero (by simp) (by norm_num) .dirichlet P hP k).symm
  have hvpos (k : ℤ) : 0 < (v k).re ↔ 0 < k := canonicalDirichletMiuraRoot_re_pos_iff _ hu k
  have hvmono : StrictMono (fun k => (v k).re) :=
    strictMono_canonicalPeriodOneBoundaryRoots_re_of_realType (by simp) (by norm_num) .dirichlet P hP
  let F : ℕ+ → ℝ := fun k => (v (k : ℤ)).re^2-c^2
  have hFcast (k : ℕ+) : (F k : ℂ) = v (k : ℤ)^2-C.energyShift := by
    dsimp only [F]
    rw [ofReal_sub,ofReal_pow,ofReal_pow,hvreal,hc]
  have hFmono : StrictMono F := by
    intro j k hjk
    have hJ := (hvpos (j : ℤ)).mpr (by exact_mod_cast j.property)
    have hK := hvmono (show (j : ℤ) < (k : ℤ) by exact_mod_cast hjk)
    dsimp only [F]
    nlinarith
  have hFroot (k : ℕ+) : hillHminusDirichlet q (F k) = 0 := by
    have hkp := (hvpos (k : ℤ)).mpr (by exact_mod_cast k.property)
    have hkn : v (k : ℤ) ≠ 0 := by intro hh; rw [hh,zero_re] at hkp; exact lt_irrefl _ hkp
    have hz : periodOneBoundaryCharacteristic (by simp) (by norm_num) .dirichlet P (v (k : ℤ)) = 0 := by
      apply (periodOneBoundaryCharacteristic_eq_zero_iff (by simp) (by norm_num) .dirichlet P _).mpr
      exact (canonicalPeriodOneBoundaryRoots_exhaustive (by simp) (by norm_num) .dirichlet P _).mpr ⟨(k : ℤ),rfl⟩
    rw [hFcast]
    exact (C.dirichlet_source_zero_iff q hq _ hkn).mp hz
  have hFexhaust (x : ℝ) (hx : hillHminusDirichlet q x = 0) : ∃ k : ℕ+, F k = x := by
    have hlower := C.dirichlet_root_gt_neg_shift_square c hc q hq hreal x hx
    let z : ℝ := Real.sqrt (x+c^2)
    have hzpos : 0 < z := Real.sqrt_pos.mpr (by linarith)
    have hzsq : z^2 = x+c^2 := Real.sq_sqrt (by linarith)
    have he : (z : ℂ)^2-C.energyShift = (x : ℂ) := by
      rw [hc,← ofReal_pow,← ofReal_pow,← ofReal_sub]
      congr 1
      linarith
    have hz : periodOneBoundaryCharacteristic (by simp) (by norm_num) .dirichlet P (z : ℂ) = 0 := by
      rw [C.dirichlet_source_characteristic q hq,he,hx,mul_zero]
    obtain ⟨m,hm⟩ := (canonicalPeriodOneBoundaryRoots_exhaustive (by simp) (by norm_num) .dirichlet P (z : ℂ)).mp
      ((periodOneBoundaryCharacteristic_eq_zero_iff (by simp) (by norm_num) .dirichlet P _).mp hz)
    change v m = (z : ℂ) at hm
    have hmpos : 0 < m := (hvpos m).mp (by change (v m).re > 0; rw [hm,ofReal_re]; exact hzpos)
    let k : ℕ+ := ⟨m.toNat,by omega⟩
    have hk : (k : ℤ) = m := Int.toNat_of_nonneg hmpos.le
    refine ⟨k,?_⟩
    dsimp only [F]
    rw [hk,hm,ofReal_re]
    linarith
  have hEq : F = hillHminusDirichletEnergy q hr := by
    apply (hFmono.range_inj (strictMono_hillHminusDirichletEnergy q hr)).mp
    ext x
    constructor
    · rintro ⟨k,rfl⟩
      obtain ⟨m,hm⟩ := hillHminusDirichlet_real_zero_eq_label q hr (F k) (hFroot k)
      exact ⟨m,hm.symm⟩
    · rintro ⟨k,rfl⟩
      exact hFexhaust _ (hillHminusDirichletEnergy_zero q hr k)
  rw [← hFcast,hEq]

end NLS.KdV
