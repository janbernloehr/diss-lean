import NLS.KdV.ClassicalTwoWeightedMomentBounds
import NLS.KdV.ClassicalFrequencyGapMajorant
import NLS.KdV.FrequencySeries
import NLS.SequenceSpaces.AnalyticTailSummation

/-! # The analytic actual normalized second-moment series near zero

The summands are literal original normalized moments. This constructs
an analytic frequency correction candidate; identifying it with the
physical KdV frequency still requires the source Hamiltonian identity.
-/
noncomputable section
open Set Metric Complex Filter Topology NLS.LinearVolterra
namespace NLS.KdV

def classicalHillSecondMomentSeriesTerm (N : ℕ)
    (R : Curve ℂ → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2)) (n : ℕ+)
    (q : Curve ℂ) (j : ℤ) : ℂ :=
  if hj : 0 < j then (j : ℂ)*classicalHillNormalizedMoment N R n (positiveIntegerIndex j hj) 2 q else 0

theorem classicalHillSecondMomentSeriesTerm_positive (N : ℕ)
    (R : Curve ℂ → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2)) (n k : ℕ+) (q : Curve ℂ) :
    classicalHillSecondMomentSeriesTerm N R n q (k : ℤ) =
      (k : ℂ)*classicalHillNormalizedMoment N R n k 2 q := by
  have hk : (0 : ℤ) < k := by exact_mod_cast k.property
  have he : positiveIntegerIndex (k : ℤ) hk = k := by
    apply Subtype.ext
    simp only [positiveIntegerIndex,Int.toNat_natCast]
    rfl
  simp only [classicalHillSecondMomentSeriesTerm,dif_pos hk,he,Int.cast_natCast]

def classicalHillMomentFrequencyCorrection (N : ℕ)
    (R : Curve ℂ → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2)) (n : ℕ+) (q : Curve ℂ) : ℂ :=
  -12*∑' k : ℕ+, (k : ℂ)*classicalHillNormalizedMoment N R n k 2 q

/-- The actual twice-weighted inverse supplies a common local normalized
family with an absolutely convergent analytic second-moment series for
every output index and locally uniform positive partial sums. -/
theorem exists_classicalHill_analytic_normalized_frequency_series :
    ∃ N : ℕ, ∃ U : Set (Curve ℂ),
      ∃ R : Curve ℂ → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2),
        0 < N ∧ IsOpen U ∧ 0 ∈ U ∧ AnalyticOnNhd ℂ R U ∧
        R 0 = ContinuousLinearMap.id ℂ (NLS.Coeff 2) ∧
        (∀ q ∈ U, ‖R q‖ ≤ 2) ∧
        (∀ n k : ℕ+, ∀ m : ℕ, AnalyticOnNhd ℂ (classicalHillNormalizedMoment N R n k m) U) ∧
        (∀ q ∈ U, ∀ n k : ℕ+,
          (2*(Real.pi : ℂ))⁻¹*classicalHillNormalizedMoment N R n k 0 q = if n = k then 1 else 0) ∧
        (∀ q ∈ U, ∀ n k : ℕ+, ∀ l : ℕ, classicalHillNormalizedMoment N R n k (2*l+1) q = 0) ∧
        ∀ n : ℕ+,
          (∀ q ∈ U, Summable (fun k : ℕ+ => ‖(k : ℂ)*classicalHillNormalizedMoment N R n k 2 q‖)) ∧
          AnalyticOnNhd ℂ (classicalHillMomentFrequencyCorrection N R n) U ∧
          TendstoLocallyUniformlyOn
            (fun (L : ℕ) q => ∑ j ∈ Finset.Icc (1 : ℤ) L, classicalHillSecondMomentSeriesTerm N R n q j)
            (fun q => ∑' k : ℕ+, (k : ℂ)*classicalHillNormalizedMoment N R n k 2 q) atTop U := by
  obtain ⟨N,V,T,R,S,Q,hN,hV,h0V,_,hRa,_,_,_,hR0,_,_,hinv,hentry,hcompat,A,D⟩ :=
    exists_classicalHill_twoWeighted_period_inverse
  obtain ⟨Mc,Uc,r,C,_,hUcV,hUc,h0Uc,H⟩ := D.exists_critical_primitive_cut_data 0 h0V
  obtain ⟨Mg,Ug,Bg,_,hUg,h0Ug,_,hg⟩ := exists_classicalHill_frequency_gap_majorant 0
  obtain ⟨Uo,_,hUo,h0Uo,hma,hodd⟩ := D.exists_normalized_all_odd_moments R hRa
  let U := Uc ∩ (Ug ∩ Uo)
  let M := max Mc Mg
  have hU : IsOpen U := hUc.inter (hUg.inter hUo)
  have hUV : U ⊆ V := fun _ hq => hUcV hq.1
  have hC : 0 < C := H.bound_pos
  refine ⟨N,U,R,hN,hU,⟨h0Uc,h0Ug,h0Uo⟩,hRa.mono hUV,hR0,
    fun q hq => (hinv q (hUV hq)).2.2.2.2.1,
    fun n k m => (hma n k m).mono (fun _ hq => hq.2.2),?_,
    fun q hq n k l => hodd q hq.2.2 n k l,?_⟩
  · intro q hq n k
    exact D.normalizedMoment_zero_order R T n k q (hUV hq)
      (fun m j => (hentry q (hUV hq) m j).1) (hinv q (hUV hq)).1
  intro n
  let f := classicalHillSecondMomentSeriesTerm N R n
  have ha (j : ℤ) : AnalyticOnNhd ℂ (fun q => f q j) U := by
    dsimp only [f,classicalHillSecondMomentSeriesTerm]
    split_ifs with hj
    · exact analyticOnNhd_const.mul ((hma n (positiveIntegerIndex j hj) 2).mono (fun _ hq => hq.2.2))
    · exact analyticOnNhd_const
  have hz (q : Curve ℂ) (_ : q ∈ U) (j : ℤ) (hj : j ≤ 0) : f q j = 0 := by
    simp only [f,classicalHillSecondMomentSeriesTerm,dif_neg (by omega : ¬0 < j)]
  let K : ℝ := (1376*Real.pi^2*C^3)*(n : ℝ)^2
  have hK : 0 ≤ K := by dsimp only [K];positivity
  have htail (q : Curve ℂ) (hq : q ∈ U) (j : ℤ) (hj : j ∉ Finset.Icc (1 : ℤ) (M : ℤ)) :
      ‖f q j‖ ≤ (K*(16*Real.pi^2))*‖classicalHillCanonicalFrequencyGapSquares q j‖ := by
    by_cases hjpos : 0 < j
    · let k := positiveIntegerIndex j hjpos
      have hkj : (k : ℤ) = j := positiveIntegerIndex_int j hjpos
      have hkM : M ≤ (k : ℕ) := by
        simp only [Finset.mem_Icc] at hj
        have hh : (M : ℤ) < j := by omega
        have : (M : ℤ) < (k : ℤ) := by rwa [hkj]
        exact_mod_cast this.le
      have hkMc : Mc ≤ (k : ℕ) := (le_max_left _ _).trans hkM
      have hkMg : Mg ≤ (k : ℕ) := (le_max_right _ _).trans hkM
      have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast k.property
      have hnpos : (0 : ℤ) < n := by exact_mod_cast n.property
      have hc (i : ℤ) := hcompat q (hUV hq) i (n : ℤ)
      rw [NLS.Coeff.positiveIndexWeight,if_pos hnpos,Int.cast_natCast] at hc
      have hm := D.normalizedMoment_two_twoWeighted_bound H hUcV R Q q hq.1 n k hkMc
        (hinv q (hUV hq)).2.2.2.2.2 hc
      have hx := (hg q hq.2.1).2 k hkMg
      change ‖classicalHillSecondMomentSeriesTerm N R n q j‖ ≤ _
      rw [← hkj,classicalHillSecondMomentSeriesTerm_positive,norm_mul,Complex.norm_natCast]
      calc
        _ ≤ (k : ℝ)*(K*(‖classicalHillHighSquaredGap q k‖/(k : ℕ)^2)/(k : ℕ)^2) :=
          mul_le_mul_of_nonneg_left hm (by positivity)
        _ ≤ K*(‖classicalHillHighSquaredGap q k‖/(k : ℕ)^2) := by
          rw [← mul_div_assoc]
          apply (div_le_iff₀ (by positivity : (0 : ℝ) < (k : ℕ)^2)).mpr
          nlinarith [mul_le_mul_of_nonneg_left (show (k : ℝ) ≤ (k : ℝ)^2 by nlinarith)
            (show 0 ≤ K*(‖classicalHillHighSquaredGap q k‖/(k : ℕ)^2) by positivity)]
        _ ≤ K*((16*Real.pi^2)*‖classicalHillCanonicalFrequencyGapSquares q (k : ℤ)‖) :=
          mul_le_mul_of_nonneg_left hx hK
        _ = _ := by ring
    · rw [hz q hq j (by omega),norm_zero]
      positivity
  obtain ⟨hs,hsum,hlocal⟩ := NLS.Coeff.analytic_tsum_of_bounded_one_tail f hU ha
    (Finset.Icc (1 : ℤ) (M : ℤ)) classicalHillCanonicalFrequencyGapSquares Bg (K*(16*Real.pi^2))
    (by positivity) (fun q hq => (hg q hq.2.1).1) htail
  obtain ⟨hsp,hsump,hlocalp⟩ := positive_frequency_series_of_integer_series f hz hs hsum hlocal hU
  have he (q : Curve ℂ) (k : ℕ+) : f q (k : ℤ) =
      (k : ℂ)*classicalHillNormalizedMoment N R n k 2 q :=
    classicalHillSecondMomentSeriesTerm_positive N R n k q
  refine ⟨?_,?_,?_⟩
  · intro q hq
    simpa only [he] using hsp q hq
  · exact analyticOnNhd_const.mul (by simpa only [classicalHillMomentFrequencyCorrection,he] using hsump)
  · simpa only [he] using hlocalp

end NLS.KdV
