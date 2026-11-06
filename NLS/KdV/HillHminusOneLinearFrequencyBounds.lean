import NLS.KdV.HillHminusOneUniformMomentBounds
import NLS.KdV.HillHminusOneNormalizedFrequencySeries

/-! Linear own-index bounds for the ACTUAL normalized second-moment sum.
A uniform finite contour head and the one-weight tail estimate control the
entire normalized row in ell1 before all own frequency indices. -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
namespace NLS.KdV

namespace HillHminusTwoWeightedNormalizedMomentData
variable {C : HillHminusMiuraChart} {N M : ℕ} {V U : Set PeriodOneHminusOne}
variable {T R S Q : PeriodOneHminusOne → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2)} {r B A Bg : ℝ}
variable (D : HillHminusTwoWeightedNormalizedMomentData C N V T R S Q)
variable (Dr : HillHminusUniformPeriodData C N V A)
include D Dr

theorem exists_normalized_secondMoment_row
    (H : HillHminusCriticalPrimitiveCutData C N M U r B) (hUV : U⊆V)
    (q : PeriodOneHminusOne) (hq : q∈U) (hgap : ‖C.canonicalFrequencyGapSquares q‖≤Bg)
    (hg : ∀ k : ℕ+, M≤(k : ℕ) → ∀ l u : ℂ, HillHminusHighGapPair q k r l u →
      ‖l-u‖^2/(k : ℕ)^2≤(16*Real.pi^2)*‖C.canonicalFrequencyGapSquares q (k : ℤ)‖)
    (n : ℕ+) :
    ∃ b : NLS.Coeff 1,
      (∀ j : ℤ, b j=hillHminusSecondMomentSeriesTerm C N R n q j/(n : ℂ)) ∧
      ‖b‖≤‖NLS.Coeff.finiteHead (p := 1) (Finset.Icc (1 : ℤ) M)
        (fun j => (j : ℂ)*(320*A^3))‖+(1376*Real.pi^2*B^3)*(16*Real.pi^2)*Bg := by
  let f := fun j => hillHminusSecondMomentSeriesTerm C N R n q j/(n : ℂ)
  let L := (1376*Real.pi^2*B^3)*(16*Real.pi^2)
  have hB := H.bound_pos
  have hA := Dr.amplitude_pos
  have hL : 0≤L := by dsimp only [L];positivity
  have hn : (1 : ℝ)≤n := by exact_mod_cast n.pos
  have hn0 : (0 : ℝ)<n := by positivity
  have hR := (D.inverses q (hUV hq)).2.2.2.2.1
  have hQ := (D.inverses q (hUV hq)).2.2.2.2.2
  have hhead (j : ℤ) (hj : j∈Finset.Icc (1 : ℤ) (M : ℤ)) :
      ‖f j‖≤‖(j : ℂ)*(320*A^3)‖ := by
    have hjp : 0<j := by have ht := Finset.mem_Icc.mp hj;omega
    let k := positiveIntegerIndex j hjp
    have hkj : (k : ℤ)=j := positiveIntegerIndex_int j hjp
    rw [←hkj]
    change ‖hillHminusSecondMomentSeriesTerm C N R n q (k : ℤ)/(n : ℂ)‖≤_
    rw [hillHminusSecondMomentSeriesTerm_positive,norm_div,norm_mul,Complex.norm_natCast,
      Complex.norm_natCast,norm_mul,Complex.norm_intCast,Int.cast_natCast,
      abs_of_pos (by positivity : (0 : ℝ)<k)]
    have hm := Dr.normalizedMoment_two_uniform_bound R q (hUV hq) hR n k
    have hconst : ‖(320*A^3 : ℂ)‖=320*A^3 := by
      rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg hA.le]
      norm_num
    rw [hconst]
    apply (div_le_iff₀ hn0).mpr
    exact (mul_le_mul_of_nonneg_left hm (by positivity)).trans
      (le_mul_of_one_le_right (by positivity) hn)
  have htail (j : ℤ) (hj : j∉Finset.Icc (1 : ℤ) (M : ℤ)) :
      ‖f j‖≤L*(‖C.canonicalFrequencyGapSquares q j‖+‖(0 : NLS.Coeff 1) j‖) := by
    by_cases hjp : 0<j
    · let k := positiveIntegerIndex j hjp
      have hkj : (k : ℤ)=j := positiveIntegerIndex_int j hjp
      have hkM : M≤(k : ℕ) := by
        simp only [Finset.mem_Icc] at hj
        have ht : (M : ℤ)<j := by omega
        have ht' : (M : ℤ)<(k : ℤ) := by rwa [hkj]
        exact_mod_cast ht'.le
      obtain ⟨l,u,F,hpair,_⟩ := H.data q hq k hkM
      have hm := Dr.normalizedMoment_two_onceWeighted_bound H hUV R Q q hq n k hkM l u hpair hR hQ
        (fun j => by
          have he := D.compatibility q (hUV hq) j (n : ℤ)
          simpa only [NLS.Coeff.positiveIndexWeight,if_pos (by exact_mod_cast n.pos : (0 : ℤ)<n),Int.cast_natCast] using he)
      have hx := hg k hkM l u hpair
      rw [←hkj]
      change ‖hillHminusSecondMomentSeriesTerm C N R n q (k : ℤ)/(n : ℂ)‖≤_
      rw [hillHminusSecondMomentSeriesTerm_positive,norm_div,norm_mul,Complex.norm_natCast,Complex.norm_natCast]
      simp only [lp.coeFn_zero,Pi.zero_apply,norm_zero,add_zero]
      calc
        _≤(k : ℝ)*((1376*Real.pi^2*B^3)*(n : ℝ)*(‖l-u‖^2/(k : ℕ)^2)/(k : ℕ))/(n : ℝ) := by gcongr
        _=(1376*Real.pi^2*B^3)*(‖l-u‖^2/(k : ℕ)^2) := by field_simp
        _≤(1376*Real.pi^2*B^3)*((16*Real.pi^2)*‖C.canonicalFrequencyGapSquares q (k : ℤ)‖) :=
          mul_le_mul_of_nonneg_left hx (by positivity)
        _=_ := by dsimp only [L];ring
    · change ‖hillHminusSecondMomentSeriesTerm C N R n q j/(n : ℂ)‖≤_
      rw [hillHminusSecondMomentSeriesTerm,dif_neg hjp,zero_div,norm_zero]
      positivity
  obtain ⟨hmem,hbound⟩ := NLS.Coeff.memℓp_and_norm_ofFunctionOrZero_le_of_head_tail_bound
    f (fun j => (j : ℂ)*(320*A^3)) (Finset.Icc (1 : ℤ) M)
    (C.canonicalFrequencyGapSquares q) (0 : NLS.Coeff 1) L hL hhead htail
  refine ⟨NLS.Coeff.ofFunctionOrZero 1 f,fun j => NLS.Coeff.ofFunctionOrZero_apply_of_mem 1 f hmem j,?_⟩
  apply hbound.trans
  simp only [norm_zero,add_zero]
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hgap hL)

/-- The ENTIRE actual second-moment correction, divided by its own index,
has one bound independent of EVERY own mode on the same rough domain. -/
theorem norm_frequencyCorrection_div_index_le
    (H : HillHminusCriticalPrimitiveCutData C N M U r B) (hUV : U⊆V)
    (q : PeriodOneHminusOne) (hq : q∈U) (hgap : ‖C.canonicalFrequencyGapSquares q‖≤Bg)
    (hg : ∀ k : ℕ+, M≤(k : ℕ) → ∀ l u : ℂ, HillHminusHighGapPair q k r l u →
      ‖l-u‖^2/(k : ℕ)^2≤(16*Real.pi^2)*‖C.canonicalFrequencyGapSquares q (k : ℤ)‖)
    (n : ℕ+) :
    ‖hillHminusMomentFrequencyCorrection C N R n q/(n : ℂ)‖≤
      12*(‖NLS.Coeff.finiteHead (p := 1) (Finset.Icc (1 : ℤ) M)
        (fun j => (j : ℂ)*(320*A^3))‖+(1376*Real.pi^2*B^3)*(16*Real.pi^2)*Bg) := by
  obtain ⟨b,hb,hbound⟩ := D.exists_normalized_secondMoment_row Dr H hUV q hq hgap hg n
  have hz (j : ℤ) (hj : j≤0) : b j=0 := by
    rw [hb j,hillHminusSecondMomentSeriesTerm,dif_neg (by omega),zero_div]
  have he : (∑' k : ℕ+, (k : ℂ)*hillHminusNormalizedMoment C N R n k 2 q/(n : ℂ))=
      ∑' j : ℤ, b j := by
    calc
      _=∑' k : ℕ+, b (k : ℤ) := tsum_congr (fun k => by
        rw [hb (k : ℤ),hillHminusSecondMomentSeriesTerm_positive])
      _=_ := (tsum_eq_positive_of_nonpositive_zero (fun j => b j) hz).symm
  have hs : Summable (fun j : ℤ => ‖b j‖) := (lp.memℓp b).norm.summable_of_one
  have hnorm : ‖∑' j : ℤ, b j‖≤‖b‖ := by
    apply (norm_tsum_le_tsum_norm hs).trans_eq
    simpa only [ENNReal.toReal_one,Real.rpow_one] using
      (lp.norm_rpow_eq_tsum (by norm_num : 0<(1 : ENNReal).toReal) b).symm
  rw [hillHminusMomentFrequencyCorrection,mul_div_assoc,←tsum_div_const,he,norm_mul]
  norm_num only [norm_neg,Complex.norm_ofNat]
  exact mul_le_mul_of_nonneg_left (hnorm.trans hbound) (by norm_num)

end HillHminusTwoWeightedNormalizedMomentData
end NLS.KdV
