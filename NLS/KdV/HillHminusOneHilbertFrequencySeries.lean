import NLS.KdV.HillHminusOneWeightedMomentVector
import NLS.KdV.HillHminusOneNormalizedFrequencySeries
import NLS.SequenceSpaces.VectorHeadTailSummation

/-! The ACTUAL weighted second moments sum in the full Hilbert norm.
Every coefficient is the same original normalized scalar correction divided
by n. Absolute vector convergence and one common norm bound are proved
before scalar evaluation, including every finite contour head. -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
namespace NLS.KdV

def hillHminusWeightedSecondMomentTerm (C : HillHminusMiuraChart) (N : ℕ)
    (Q : PeriodOneHminusOne → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (q : PeriodOneHminusOne) (j : ℤ) : NLS.Coeff 2 :=
  if hj : 0<j then (j : ℂ) • hillHminusWeightedSecondMomentVector C N Q (positiveIntegerIndex j hj) q else 0

def hillHminusHilbertMomentFrequencyCorrection (C : HillHminusMiuraChart) (N : ℕ)
    (Q : PeriodOneHminusOne → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (q : PeriodOneHminusOne) : NLS.Coeff 2 :=
  (-12 : ℂ) • ∑' j : ℤ, hillHminusWeightedSecondMomentTerm C N Q q j

theorem hillHminusWeightedSecondMomentTerm_nonpositive_coordinate
    (C : HillHminusMiuraChart) (N : ℕ)
    (Q : PeriodOneHminusOne → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (q : PeriodOneHminusOne) (k j : ℤ) (hj : j≤0) :
    hillHminusWeightedSecondMomentTerm C N Q q k j=0 := by
  rw [hillHminusWeightedSecondMomentTerm]
  split_ifs
  · simp only [lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,
      hillHminusWeightedSecondMomentVector_nonpositive C N Q _ q j hj,mul_zero]
  · rfl

namespace HillHminusUniformPeriodData
variable {C : HillHminusMiuraChart} {N M : ℕ} {V U : Set PeriodOneHminusOne} {A r B Bg : ℝ}
variable (D : HillHminusUniformPeriodData C N V A)
include D

/-- Absolute Hilbert summation, with one bound independent of EVERY own
index, follows from the same actual finite head and canonical gap majorant. -/
theorem summable_weightedSecondMomentVector_and_norm_bound
    (H : HillHminusCriticalPrimitiveCutData C N M U r B) (hUV : U⊆V)
    (Q : PeriodOneHminusOne → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (q : PeriodOneHminusOne) (hq : q∈U) (hQ : ‖Q q‖≤2)
    (hgap : ‖C.canonicalFrequencyGapSquares q‖≤Bg)
    (hg : ∀ k : ℕ+, M≤(k : ℕ) → ∀ l u : ℂ, HillHminusHighGapPair q k r l u →
      ‖l-u‖^2/(k : ℕ)^2≤(16*Real.pi^2)*‖C.canonicalFrequencyGapSquares q (k : ℤ)‖) :
    Summable (fun j : ℤ => ‖hillHminusWeightedSecondMomentTerm C N Q q j‖) ∧
    ‖hillHminusHilbertMomentFrequencyCorrection C N Q q‖≤
      12*((∑ j∈Finset.Icc (1 : ℤ) M, ‖(j : ℂ)*(320*A^3)‖)+
        (1376*Real.pi^2*B^3)*(16*Real.pi^2)*Bg) := by
  let f := hillHminusWeightedSecondMomentTerm C N Q q
  let L := (1376*Real.pi^2*B^3)*(16*Real.pi^2)
  have hA := D.amplitude_pos
  have hB := H.bound_pos
  have hL : 0≤L := by dsimp only [L];positivity
  have hconst : ‖(320*A^3 : ℂ)‖=320*A^3 := by
    rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg hA.le]
    norm_num
  have hhead (j : ℤ) (hj : j∈Finset.Icc (1 : ℤ) (M : ℤ)) : ‖f j‖≤‖(j : ℂ)*(320*A^3)‖ := by
    have hjp : 0<j := by have ht := Finset.mem_Icc.mp hj;omega
    let k := positiveIntegerIndex j hjp
    change ‖hillHminusWeightedSecondMomentTerm C N Q q j‖≤_
    rw [hillHminusWeightedSecondMomentTerm,dif_pos hjp,norm_smul,norm_mul,hconst]
    exact mul_le_mul_of_nonneg_left (D.norm_weightedSecondMomentVector_uniform_bound Q q (hUV hq) hQ k) (norm_nonneg _)
  have htail (j : ℤ) (hj : j∉Finset.Icc (1 : ℤ) (M : ℤ)) : ‖f j‖≤L*‖C.canonicalFrequencyGapSquares q j‖ := by
    by_cases hjp : 0<j
    · let k := positiveIntegerIndex j hjp
      have hkj : (k : ℤ)=j := positiveIntegerIndex_int j hjp
      have hkr : (k : ℝ)=(j : ℝ) := by exact_mod_cast hkj
      have hkM : M≤(k : ℕ) := by
        simp only [Finset.mem_Icc] at hj
        have ht : (M : ℤ)<j := by omega
        have ht' : (M : ℤ)<(k : ℤ) := by rwa [hkj]
        exact_mod_cast ht'.le
      obtain ⟨l,u,F,hpair,_⟩ := H.data q hq k hkM
      have hm := D.norm_weightedSecondMomentVector_gap_bound H hUV Q q hq hQ k hkM l u hpair
      have hx := hg k hkM l u hpair
      change ‖hillHminusWeightedSecondMomentTerm C N Q q j‖≤_
      rw [hillHminusWeightedSecondMomentTerm,dif_pos hjp,norm_smul,Complex.norm_intCast,
        abs_of_pos (by exact_mod_cast hjp : (0 : ℝ)<j),←hkr]
      calc
        _≤(k : ℝ)*((1376*Real.pi^2*B^3)*(‖l-u‖^2/(k : ℕ)^2)/(k : ℕ)) := by gcongr
        _=(1376*Real.pi^2*B^3)*(‖l-u‖^2/(k : ℕ)^2) := by field_simp
        _≤(1376*Real.pi^2*B^3)*((16*Real.pi^2)*‖C.canonicalFrequencyGapSquares q (k : ℤ)‖) :=
          mul_le_mul_of_nonneg_left hx (by positivity)
        _=_ := by dsimp only [L];rw [hkj];ring
    · change ‖hillHminusWeightedSecondMomentTerm C N Q q j‖≤_
      rw [hillHminusWeightedSecondMomentTerm,dif_neg hjp,norm_zero]
      positivity
  obtain ⟨hs,hbound⟩ := NLS.Coeff.summable_norm_and_tsum_norm_le_of_head_tail f
    (Finset.Icc (1 : ℤ) M) (fun j => ‖(j : ℂ)*(320*A^3)‖)
    (C.canonicalFrequencyGapSquares q) L hL hhead htail
  refine ⟨hs,?_⟩
  rw [hillHminusHilbertMomentFrequencyCorrection,norm_smul]
  norm_num only [norm_neg,Complex.norm_ofNat]
  apply mul_le_mul_of_nonneg_left ((norm_tsum_le_tsum_norm hs).trans (hbound.trans ?_)) (by norm_num)
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hgap hL)

/-- Positive coefficients of the norm-convergent Hilbert sum equal the
literal convergent original normalized correction divided by n. -/
theorem hilbertMomentFrequencyCorrection_positive
    (R Q : PeriodOneHminusOne → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (q : PeriodOneHminusOne) (hq : q∈V)
    (hs : Summable (fun j : ℤ => ‖hillHminusWeightedSecondMomentTerm C N Q q j‖))
    (hcompat : ∀ j m : ℤ, NLS.Coeff.positiveIndexWeight j*(R q (lp.single 2 m 1)) j=
      NLS.Coeff.positiveIndexWeight m*(Q q (lp.single 2 m 1)) j)
    (n : ℕ+) : hillHminusHilbertMomentFrequencyCorrection C N Q q (n : ℤ)=
      hillHminusMomentFrequencyCorrection C N R n q/(n : ℂ) := by
  have hnc : NLS.Coeff.positiveIndexWeight (n : ℤ)=(n : ℂ) := by
    rw [NLS.Coeff.positiveIndexWeight,if_pos (by exact_mod_cast n.pos : (0 : ℤ)<n),Int.cast_natCast]
  have he (j : ℤ) : hillHminusWeightedSecondMomentTerm C N Q q j (n : ℤ)=
      hillHminusSecondMomentSeriesTerm C N R n q j/(n : ℂ) := by
    by_cases hj : 0<j
    · rw [hillHminusWeightedSecondMomentTerm,dif_pos hj,hillHminusSecondMomentSeriesTerm,dif_pos hj]
      change (j : ℂ)*hillHminusWeightedSecondMomentVector C N Q (positiveIntegerIndex j hj) q (n : ℤ)=_
      rw [D.weightedSecondMomentVector_positive R Q q hq n _ (fun i => by simpa only [hnc] using hcompat i (n : ℤ))]
      ring
    · rw [hillHminusWeightedSecondMomentTerm,dif_neg hj,hillHminusSecondMomentSeriesTerm,dif_neg hj,zero_div]
      rfl
  change (-12 : ℂ)*(∑' j : ℤ, hillHminusWeightedSecondMomentTerm C N Q q j) (n : ℤ)=_
  have hv : (∑' j : ℤ, hillHminusWeightedSecondMomentTerm C N Q q j) (n : ℤ)=
      ∑' j : ℤ, hillHminusWeightedSecondMomentTerm C N Q q j (n : ℤ) :=
    (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 (n : ℤ)).map_tsum hs.of_norm
  rw [hv]
  simp_rw [he]
  rw [tsum_div_const,tsum_eq_positive_of_nonpositive_zero _ (fun j hj => by
    rw [hillHminusSecondMomentSeriesTerm,dif_neg (by omega)])]
  simp_rw [hillHminusSecondMomentSeriesTerm_positive]
  rw [hillHminusMomentFrequencyCorrection]
  ring

end HillHminusUniformPeriodData

theorem hillHminusHilbertMomentFrequencyCorrection_nonpositive
    (C : HillHminusMiuraChart) (N : ℕ)
    (Q : PeriodOneHminusOne → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (q : PeriodOneHminusOne)
    (hs : Summable (fun k : ℤ => ‖hillHminusWeightedSecondMomentTerm C N Q q k‖))
    (j : ℤ) (hj : j≤0) : hillHminusHilbertMomentFrequencyCorrection C N Q q j=0 := by
  change (-12 : ℂ)*(∑' k : ℤ, hillHminusWeightedSecondMomentTerm C N Q q k) j=0
  have hv : (∑' k : ℤ, hillHminusWeightedSecondMomentTerm C N Q q k) j=
      ∑' k : ℤ, hillHminusWeightedSecondMomentTerm C N Q q k j :=
    (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 j).map_tsum hs.of_norm
  rw [hv]
  simp only [hillHminusWeightedSecondMomentTerm_nonpositive_coordinate C N Q q _ j hj,tsum_zero,mul_zero]

end NLS.KdV
