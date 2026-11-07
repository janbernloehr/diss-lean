import NLS.KdV.HillHminusL2NoncentralBetaDecay
import NLS.SequenceSpaces.ComplexPhaseSmoothing

/-! The ACTUAL noncentral coordinate phase minus one gains one derivative
on a common complex L2 neighborhood, before every positive index. -/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.KdV.HillHminusPsiChart

def positiveNoncentralBeta (P : HillHminusPsiChart) (a : PeriodOneHminusOne) : ℤ → ℂ :=
  Coeff.positiveFamilyCoordinates (fun n => P.sourceNoncentralBeta n a)

theorem positiveNoncentralBeta_bracket_bound (P : HillHminusPsiChart)
    (a : PeriodOneHminusOne) (K : ℝ) (hK : 0≤K)
    (hb : ∀ n : ℕ+, (1+(n:ℝ))*‖P.sourceNoncentralBeta n a‖≤K) :
    ∀ j : ℤ, (1+|(j:ℝ)|)*‖P.positiveNoncentralBeta a j‖≤K := by
  intro j
  by_cases hj : 0<j
  · let n := Coeff.positivePoleIndex j hj
    have hn : (n:ℝ)=(j:ℝ) := Coeff.positivePoleIndex_real j hj
    change (1+|(j:ℝ)|)*‖Coeff.positiveFamilyCoordinates (fun k => P.sourceNoncentralBeta k a) j‖≤K
    rw [Coeff.positiveFamilyCoordinates,dif_pos hj,abs_of_pos (by exact_mod_cast hj)]
    simpa only [hn] using hb n
  · simp only [positiveNoncentralBeta,Coeff.positiveFamilyCoordinates,dif_neg hj,norm_zero,mul_zero]
    exact hK

theorem exists_native_l2_coordinate_phase_smoothing (P : HillHminusPsiChart)
    (H : SourceLemma12_12Data (by norm_num) (by norm_num)
      P.family.originalDomain P.family.domain P.family.roots)
    (hstrong : HasAllNativeMiuraGerms P)
    (q : WeightedCoeff (Weight.sobolev ((1:ℝ)-1)) 2)
    (hq : periodOneSobolevImageInclusion 1 (by norm_num) q∈P.sourceBetaDomain)
    (hr : periodOneL2Conjugation (P.miura.lift (periodOneSobolevImageInclusion 1 (by norm_num) q))=
      P.miura.lift (periodOneSobolevImageInclusion 1 (by norm_num) q)) :
    ∃ U : Set (WeightedCoeff (Weight.sobolev ((1:ℝ)-1)) 2), IsOpen U ∧ q∈U ∧
      (∀ p∈U, periodOneSobolevImageInclusion 1 (by norm_num) p∈P.sourceBetaDomain) ∧
      ∃ K : ℝ, ∃ M : WeightedCoeff (Weight.sobolev ((1:ℝ)-1)) 2 → Coeff ⊤,
        0≤K ∧ AnalyticOnNhd ℂ M U ∧ ∀ p∈U,
          ‖M p‖≤K ∧ (∀ j : ℤ, j≤0 → M p j=0) ∧
          (∀ n : ℕ+, M p (n:ℤ)=(1+(n:ℂ))*(exp (I*P.sourceNoncentralBeta n
            (periodOneSobolevImageInclusion 1 (by norm_num) p))-1)) ∧
          ∀ (v : ℝ≥0∞) (_ : Fact (1≤v)) (r : ℝ),
            ∃ T : WeightedCoeff (Weight.sobolev r) v →L[ℂ] WeightedCoeff (Weight.sobolev (r+1)) v,
              (∀ b j, (T b).val j=(exp (I*P.positiveNoncentralBeta
                (periodOneSobolevImageInclusion 1 (by norm_num) p) j)-1)*b.val j) ∧ ‖T‖≤K := by
  obtain ⟨U,hU,hqU,hUP,C,hC,hb⟩ := P.exists_native_l2_noncentralBeta_decay H hstrong q hq hr
  let L := periodOneSobolevImageInclusion 1 (by norm_num : (0:ℝ)≤1)
  let f : ℕ+ → WeightedCoeff (Weight.sobolev ((1:ℝ)-1)) 2 → ℂ :=
    fun n p => (1+(n:ℂ))*(exp (I*P.sourceNoncentralBeta n (L p))-1)
  have hfa (n : ℕ+) : AnalyticOnNhd ℂ (f n) U := by
    intro p hp
    exact analyticAt_const.mul ((analyticAt_const.mul
      ((P.analytic_sourceNoncentralBeta H n (L p) (hUP p hp)).comp (L.analyticAt p))).cexp'.sub analyticAt_const)
  have hfb (p : WeightedCoeff (Weight.sobolev ((1:ℝ)-1)) 2) (hp : p∈U) (n : ℕ+) :
      ‖f n p‖≤C*Real.exp C := by
    have hn : ‖P.sourceNoncentralBeta n (L p)‖≤C := by
      have h := hb p hp n
      nlinarith [norm_nonneg (P.sourceNoncentralBeta n (L p)),show (0:ℝ)≤n by positivity]
    have he := NLS.ComplexAnalysis.norm_exp_sub_one_le_norm_mul_exp (I*P.sourceNoncentralBeta n (L p))
    simp only [norm_mul,norm_I,one_mul] at he
    have he' := he.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hn) (norm_nonneg _))
    change ‖(1+(n:ℂ))*(exp (I*P.sourceNoncentralBeta n (L p))-1)‖≤_
    rw [norm_mul,show ‖(1+(n:ℂ))‖=1+(n:ℝ) by
      rw [←Nat.cast_one,←Nat.cast_add,Complex.norm_natCast,Nat.cast_add,Nat.cast_one]]
    calc
      _ ≤ (1+(n:ℝ))*(‖P.sourceNoncentralBeta n (L p)‖*Real.exp C) :=
        mul_le_mul_of_nonneg_left he' (by positivity)
      _ = ((1+(n:ℝ))*‖P.sourceNoncentralBeta n (L p)‖)*Real.exp C := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (hb p hp n) (Real.exp_pos C).le
  obtain ⟨M,hMa,hM⟩ := Coeff.exists_positive_bounded_analytic_lift U hU f (C*Real.exp C) (by positivity) hfa hfb
  refine ⟨U,hU,hqU,hUP,C*Real.exp C,M,by positivity,hMa,?_⟩
  intro p hp
  refine ⟨(hM p hp).1,(hM p hp).2.1,(hM p hp).2.2,?_⟩
  intro v hv r
  obtain ⟨T,hT,hTn⟩ := WeightedCoeff.exists_sobolev_complex_phase_gain_multiplier (q := v) r 1
    (P.positiveNoncentralBeta (L p)) C hC (P.positiveNoncentralBeta_bracket_bound (L p) C hC (hb p hp))
  refine ⟨T,?_,?_⟩
  · simpa only [Complex.ofReal_one,one_mul] using hT
  · simpa only [abs_one,one_mul] using hTn

end NLS.KdV.HillHminusPsiChart
