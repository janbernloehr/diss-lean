import NLS.KdV.HillHminusOneMiuraCriticalResidues
import NLS.ZakharovShabat.SourcePsiCriticalResidueBounds
import NLS.SequenceSpaces.Multiplier
import NLS.SequenceSpaces.Reflection

/-! # Genuine Hilbert coefficients for the descended energy numerator

The signed canonical NLS residue sequence is square summable. A bounded
actual critical-frequency multiplier transfers its antisymmetrization
to the exact energy critical-basis coefficients A_j/(2*pi*j).
-/
noncomputable section
open Set Complex NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV

/-- Positive critical-frequency symbol, retaining the exact pi factor. -/
def hillHminusMiuraPositiveCriticalRatio (C : HillHminusMiuraChart)
    (q : PeriodOneHminusOne) (m : ℤ) : ℂ :=
  if 0 < m then canonicalCriticalPoints (by simp) (by norm_num)
    (periodOnePotential (C.criticalSource q)) (periodOnePotential_mem _) m / ((Real.pi:ℂ)*m) else 0

theorem hillHminusMiuraPositiveCriticalRatio_bound (C : HillHminusMiuraChart)
    (q : PeriodOneHminusOne) (m : ℤ) :
    ‖hillHminusMiuraPositiveCriticalRatio C q m‖ ≤
      (Real.pi+‖canonicalCriticalDisplacement (by simp) (by norm_num)
        (periodOnePotential (C.criticalSource q)) (periodOnePotential_mem _)‖)/Real.pi := by
  let b := canonicalCriticalDisplacement (by simp) (by norm_num)
    (periodOnePotential (C.criticalSource q)) (periodOnePotential_mem _)
  by_cases hm : 0 < m
  · rw [hillHminusMiuraPositiveCriticalRatio,if_pos hm,norm_div,norm_mul,Complex.norm_real,
      Real.norm_of_nonneg Real.pi_pos.le,Complex.norm_intCast,abs_of_pos (by exact_mod_cast hm : (0:ℝ) < m)]
    have hcoord : ‖b m‖ ≤ ‖b‖ := lp.norm_apply_le_norm (by norm_num) b m
    have he : canonicalCriticalPoints (by simp) (by norm_num)
        (periodOnePotential (C.criticalSource q)) (periodOnePotential_mem _) m = (Real.pi:ℂ)*m+b m := by
      simp only [b,canonicalCriticalDisplacement_apply]
      ring
    have hnorm : ‖(Real.pi:ℂ)*m‖ = Real.pi*(m:ℝ) := by
      rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg Real.pi_pos.le,Complex.norm_intCast,
        abs_of_pos (by exact_mod_cast hm : (0:ℝ) < m)]
    have hβ := norm_add_le ((Real.pi:ℂ)*m) (b m)
    rw [← he,hnorm] at hβ
    have hm1 : 1 ≤ (m:ℝ) := by exact_mod_cast hm
    apply (div_le_div_iff₀ (mul_pos Real.pi_pos (by exact_mod_cast hm)) Real.pi_pos).mpr
    change _ ≤ (Real.pi+‖b‖)*(Real.pi*(m:ℝ))
    have hbmul : ‖b m‖ ≤ ‖b‖*(m:ℝ) :=
      hcoord.trans (le_mul_of_one_le_right (norm_nonneg b) hm1)
    have hβbound : ‖canonicalCriticalPoints (by simp) (by norm_num)
        (periodOnePotential (C.criticalSource q)) (periodOnePotential_mem _) m‖ ≤
          (Real.pi+‖b‖)*(m:ℝ) := by nlinarith
    calc
      _ ≤ ((Real.pi+‖b‖)*(m:ℝ))*Real.pi := mul_le_mul_of_nonneg_right hβbound Real.pi_pos.le
      _ = _ := by ring
  · rw [hillHminusMiuraPositiveCriticalRatio,if_neg hm,norm_zero]
    positivity

def hillHminusMiuraPositiveCriticalMultiplier (C : HillHminusMiuraChart)
    (q : PeriodOneHminusOne) : Coeff ⊤ :=
  ⟨hillHminusMiuraPositiveCriticalRatio C q,memℓp_infty ⟨_,by
    rintro _ ⟨m,rfl⟩
    exact hillHminusMiuraPositiveCriticalRatio_bound C q m⟩⟩

/-- Actual signed residue sequence, supported by its proved membership. -/
def hillHminusMiuraSignedResidueHilbert (C : HillHminusMiuraChart)
    (s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n) (n : ℤ)
    (q : PeriodOneHminusOne) (hr : IsRealType (CoeffPair.toMax 2 (C.criticalSource q))) : Coeff 2 :=
  ⟨hillHminusMiuraSignedCriticalResidue C s n q,
    memℓp_sourcePsiCriticalResidue_two (by simp) (by norm_num) n
      (s n (C.criticalSource q) : Coeff 2) (C.criticalSource q) hr⟩

/-- Actual positive energy-basis coefficients, zero at nonpositive indices. -/
def hillHminusMiuraEnergyResidueHilbert (C : HillHminusMiuraChart)
    (s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n) (n : ℤ)
    (q : PeriodOneHminusOne) (hr : IsRealType (CoeffPair.toMax 2 (C.criticalSource q))) : Coeff 2 :=
  let r := hillHminusMiuraSignedResidueHilbert C s n q hr
  Coeff.multiplier (hillHminusMiuraPositiveCriticalMultiplier C q) (r-Coeff.reflection r)

theorem hillHminusMiuraEnergyResidueHilbert_apply_nonpos (C : HillHminusMiuraChart)
    (s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n) (n : ℤ)
    (q : PeriodOneHminusOne) (hr : IsRealType (CoeffPair.toMax 2 (C.criticalSource q)))
    (m : ℤ) (hm : m ≤ 0) : hillHminusMiuraEnergyResidueHilbert C s n q hr m = 0 := by
  change hillHminusMiuraPositiveCriticalRatio C q m * _ = 0
  rw [hillHminusMiuraPositiveCriticalRatio,if_neg (not_lt.mpr hm),zero_mul]

theorem hillHminusMiuraEnergyResidueHilbert_apply_pos (C : HillHminusMiuraChart)
    (s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n) (n : ℤ)
    (q : PeriodOneHminusOne) (hq : q ∈ C.domain)
    (hr : IsRealType (CoeffPair.toMax 2 (C.criticalSource q))) (j : ℕ+) :
    hillHminusMiuraEnergyResidueHilbert C s n q hr (j:ℤ) =
      hillHminusMiuraEnergyCriticalResidue C s n q j / (2*(j:ℂ)*Real.pi) := by
  have hj : (0:ℤ) < j := by exact_mod_cast j.pos
  change hillHminusMiuraPositiveCriticalRatio C q (j:ℤ)*
    (hillHminusMiuraSignedCriticalResidue C s n q (j:ℤ)-
      hillHminusMiuraSignedCriticalResidue C s n q (-(j:ℤ))) = _
  rw [hillHminusMiuraPositiveCriticalRatio,if_pos hj,hillHminusMiuraEnergyCriticalResidue_eq_signed C s n q hq hr j]
  change C.frequencyCritical q j / ((Real.pi:ℂ)*(j:ℂ)) * _ = _
  field_simp

theorem hillHminusMiuraEnergyResidueHilbert_norm_le (C : HillHminusMiuraChart)
    (s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n) (n : ℤ)
    (q : PeriodOneHminusOne) (hr : IsRealType (CoeffPair.toMax 2 (C.criticalSource q))) :
    ‖hillHminusMiuraEnergyResidueHilbert C s n q hr‖ ≤
      2*‖hillHminusMiuraPositiveCriticalMultiplier C q‖*‖hillHminusMiuraSignedResidueHilbert C s n q hr‖ := by
  let r := hillHminusMiuraSignedResidueHilbert C s n q hr
  have h := Coeff.norm_multiplier_le (hillHminusMiuraPositiveCriticalMultiplier C q) (r-Coeff.reflection r)
  have hsub : ‖r-Coeff.reflection r‖ ≤ 2*‖r‖ := by
    calc
      _ ≤ ‖r‖+‖Coeff.reflection r‖ := norm_sub_le _ _
      _ = 2*‖r‖ := by rw [Coeff.reflection.norm_map]; ring
  exact h.trans ((mul_le_mul_of_nonneg_left hsub (norm_nonneg _)).trans_eq (by ring))

/-- Actual normalized NLS data on one common rough-open neighborhood
supply genuine Hilbert energy-basis coefficients before all indices. -/
theorem exists_hillHminus_real_energy_residue_hilbert (q0 : PeriodOneHminusOne)
    (hq0 : periodOneHminusConjugation q0 = q0) :
    ∃ C : HillHminusMiuraChart, ∃ V : Set PeriodOneHminusOne,
      ∃ W₀ W : Set (CoeffPair 2), ∃ s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n,
        IsOpen V ∧ q0 ∈ V ∧ V ⊆ C.domain ∧
        SourceTheorem12_1Data (by simp) (by norm_num) W₀ W s ∧
        (∀ q ∈ V, C.criticalSource q ∈ W) ∧
        ∀ q ∈ V, periodOneHminusConjugation q = q → ∀ n : ℤ,
          ∃ a : Coeff 2, (∀ m : ℤ, m ≤ 0 → a m = 0) ∧
            ∀ j : ℕ+, a (j:ℤ) = hillHminusMiuraEnergyCriticalResidue C s n q j /
              (2*(j:ℂ)*Real.pi) := by
  obtain ⟨C,V,W₀,W,s,hV,hqV,hVC,_,_,_,hr,H,hVW,_,_,_⟩ :=
    exists_hillHminus_real_normalized_energy_pullbacks q0 hq0
  refine ⟨C,V,W₀,W,s,hV,hqV,hVC,H,hVW,?_⟩
  intro q hq hreal n
  have hsource := (hr q (hVC hq) hreal).2
  exact ⟨hillHminusMiuraEnergyResidueHilbert C s n q hsource,
    hillHminusMiuraEnergyResidueHilbert_apply_nonpos C s n q hsource,
    hillHminusMiuraEnergyResidueHilbert_apply_pos C s n q (hVC hq) hsource⟩

end NLS.KdV
