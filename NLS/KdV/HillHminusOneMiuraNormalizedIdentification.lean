import NLS.KdV.HillHminusOneOriginalNormalizedPeriods
import NLS.KdV.HillHminusOneNormalizedDifferentials
import NLS.KdV.HillHminusOneTwoWeightedPeriodInverse

/-! # Identification of actual Miura numerators with the weighted normalized family

Genuine Hilbert membership and the derived original Kronecker periods
identify the actual coefficient vector through the constructed inverse.
One common ball precedes all real inputs, positive indices and energies.
The current equality is on the physical real slice near zero.
-/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV

/-- The actual original periods determine a genuine Hilbert coefficient vector as the constructed inverse column. -/
theorem hillHminus_inverse_column_of_actual_periods (Dold : HillHminusMiuraChart)
    {N : ℕ} {V : Set PeriodOneHminusOne} {A : ℝ}
    (D : HillHminusUniformPeriodData Dold N V A) (q : PeriodOneHminusOne) (hq : q ∈ V)
    (T R : Coeff 2 →L[ℂ] Coeff 2)
    (hentry : ∀ m j : ℤ, (T (lp.single 2 j 1)) m = hillHminusPeriodMatrix Dold N q m j)
    (hRT : R.comp T = ContinuousLinearMap.id ℂ (Coeff 2))
    (a : Coeff 2) (ha : ∀ m ≤ (0 : ℤ), a m = 0) (n : ℕ+)
    (F : ℂ → ℂ) (hF : ∀ energy, F energy = Coeff.dualPairing a (hillHminusNumeratorHilbert Dold N (energy,q)))
    (hperiod : ∀ k : ℕ+,
      (∮ z in C((Real.pi : ℂ)*(k : ℕ),Real.pi/4), (F (z^2)/hillHminusContinuedRoot (z^2,q))*(2*z)) =
        (2*Real.pi : ℂ)*(if k = n then 1 else 0)) :
    a = R (lp.single 2 (n : ℤ) 1) := by
  have hfac : (2*(Real.pi : ℂ)) ≠ 0 := mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)
  have hpos (k : ℕ+) : (T a) (k : ℤ) = (lp.single 2 (n : ℤ) (1 : ℂ) : Coeff 2) (k : ℤ) := by
    have hi := D.hilbertPeriod_integral k q hq a
    simp_rw [← hF] at hi
    rw [hperiod,← mul_assoc,inv_mul_cancel₀ hfac,one_mul] at hi
    have hrow := congrArg (fun L : Coeff 2 →L[ℂ] ℂ => L a) (D.hilbertPeriod_eq_row k q hq T hentry)
    change hillHminusHilbertPeriod Dold N k q a = (T a) (k : ℤ) at hrow
    rw [← hrow,hi]
    simp only [lp.single_apply,Pi.single_apply]
    by_cases he : k = n
    · subst k
      simp only [ite_true]
    · have hne : (k : ℤ) ≠ (n : ℤ) := by exact_mod_cast he
      simp only [if_neg he,if_neg hne]
  have hTa : T a = lp.single 2 (n : ℤ) 1 := by
    apply lp.ext
    funext m
    by_cases hm : 0 < m
    · let k : ℕ+ := ⟨m.toNat,by omega⟩
      have hk : (k : ℤ) = m := Int.toNat_of_nonneg hm.le
      simpa only [hk] using hpos k
    · have hm0 : m ≤ 0 := le_of_not_gt hm
      have hrow := congrArg (fun L : Coeff 2 →L[ℂ] ℂ => L a)
        (hillHminusPeriodOperator_nonpositive_row Dold N q T hentry m hm0)
      change (T a) m = a m at hrow
      rw [hrow,ha m hm0]
      have hn : (0 : ℤ) < n := by exact_mod_cast n.pos
      simp only [lp.single_apply,Pi.single_apply,if_neg (by omega : m ≠ (n : ℤ))]
  have he := congrArg (fun L : Coeff 2 →L[ℂ] Coeff 2 => L a) hRT
  change R (T a) = a at he
  rw [hTa] at he
  exact he.symm

end NLS.KdV

namespace NLS.KdV

/-- One actual normalized data set and ball identify the actual entire Miura family with any verified constructed period inverse, at every real input and every energy. -/
theorem exists_hillHminus_real_normalized_family_identification (Dold : HillHminusMiuraChart)
    {N : ℕ} {V : Set PeriodOneHminusOne} {A : ℝ}
    (D : HillHminusUniformPeriodData Dold N V A)
    (T R : PeriodOneHminusOne → (Coeff 2 →L[ℂ] Coeff 2))
    (hentry : ∀ q ∈ V, ∀ m j : ℤ, (T q (lp.single 2 j 1)) m = hillHminusPeriodMatrix Dold N q m j)
    (hRT : ∀ q ∈ V, (R q).comp (T q) = ContinuousLinearMap.id ℂ (Coeff 2)) :
    ∃ C : HillHminusMiuraChart, ∃ δ : ℝ, ∃ W₀ W : Set (CoeffPair 2),
      ∃ s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n,
        0 < δ ∧ ball (0 : PeriodOneHminusOne) δ ⊆ V ∧
        ball (0 : PeriodOneHminusOne) δ ⊆ C.domain ∧
        SourceTheorem12_1Data (by simp) (by norm_num) W₀ W s ∧
        (∀ q ∈ ball (0 : PeriodOneHminusOne) δ, C.criticalSource q ∈ W) ∧
        (∀ n : ℤ, AnalyticOnNhd ℂ (hillHminusMiuraEnergyPsi C s n)
          (univ ×ˢ ball (0 : PeriodOneHminusOne) δ)) ∧
        ∀ q ∈ ball (0 : PeriodOneHminusOne) δ, periodOneHminusConjugation q = q →
          ∀ n : ℕ+, ∀ energy : ℂ, hillHminusMiuraEnergyPsi C s (n : ℤ) (energy,q) =
            hillHminusNormalizedNumerator Dold N R n (energy,q) := by
  obtain ⟨C,δP,W₀,W,s,hδP,hPV,hPC,_,hc,hr,H,hW,hpsi,hperiod⟩ :=
    exists_hillHminus_actual_original_periods Dold D.toHillHminusAllContourPeriodData
  have h0C : (0 : PeriodOneHminusOne) ∈ C.domain := hPC (mem_ball_self hδP)
  obtain ⟨δR,hδR,hRV,hrepr⟩ := hillHminus_period_data_actual_numerator_representation C Dold
    D.toHillHminusAllContourPeriodData h0C hc hr
  let δ := min δP δR
  have hδ : 0 < δ := lt_min hδP hδR
  have hp : ball (0 : PeriodOneHminusOne) δ ⊆ ball 0 δP := ball_subset_ball (min_le_left _ _)
  have hb : ball (0 : PeriodOneHminusOne) δ ⊆ ball 0 δR := ball_subset_ball (min_le_right _ _)
  refine ⟨C,δ,W₀,W,s,hδ,hp.trans hPV,hp.trans hPC,H,fun q hq => hW q (hp hq),
    fun n => (hpsi n).mono (fun t ht => ⟨ht.1,hp ht.2⟩),?_⟩
  intro q hq hreal n energy
  obtain ⟨hqC,hrep⟩ := hrepr q (hb hq)
  let a := hillHminusMiuraEnergyResidueHilbert C s (n : ℤ) q (hr q hqC hreal)
  have hF : ∀ e : ℂ, hillHminusMiuraEnergyPsi C s (n : ℤ) (e,q) =
      Coeff.dualPairing a (hillHminusNumeratorHilbert Dold N (e,q)) := hrep hreal s (n : ℤ)
  have ha : a = R q (lp.single 2 (n : ℤ) 1) :=
    hillHminus_inverse_column_of_actual_periods Dold D q (hPV (hp hq)) (T q) (R q)
      (hentry q (hPV (hp hq))) (hRT q (hPV (hp hq))) a
      (hillHminusMiuraEnergyResidueHilbert_apply_nonpos C s (n : ℤ) q (hr q hqC hreal))
      n _ hF (hperiod q (hp hq) hreal n)
  rw [hF,ha]
  rfl

end NLS.KdV

namespace NLS.KdV

/-- The actual two-weighted inverse construction supplies the normalized
family identification, analytic inverse families, uniform inverse bounds and
exact weighted compatibility on one common complex ball. -/
theorem exists_hillHminus_actual_twoWeighted_normalized_identification :
    ∃ Dold : HillHminusMiuraChart, ∃ N : ℕ, ∃ C : HillHminusMiuraChart, ∃ δ : ℝ,
      ∃ W₀ W : Set (CoeffPair 2), ∃ s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n,
      ∃ R Q : PeriodOneHminusOne → (Coeff 2 →L[ℂ] Coeff 2), ∃ A : ℝ,
        0 < δ ∧ HillHminusUniformPeriodData Dold N (ball (0 : PeriodOneHminusOne) δ) A ∧
        ball (0 : PeriodOneHminusOne) δ ⊆ C.domain ∧
        SourceTheorem12_1Data (by simp) (by norm_num) W₀ W s ∧
        (∀ q ∈ ball (0 : PeriodOneHminusOne) δ, C.criticalSource q ∈ W) ∧
        (∀ n : ℤ, AnalyticOnNhd ℂ (hillHminusMiuraEnergyPsi C s n)
          (univ ×ˢ ball (0 : PeriodOneHminusOne) δ)) ∧
        AnalyticOnNhd ℂ R (ball (0 : PeriodOneHminusOne) δ) ∧
        AnalyticOnNhd ℂ Q (ball (0 : PeriodOneHminusOne) δ) ∧
        R 0 = ContinuousLinearMap.id ℂ (Coeff 2) ∧ Q 0 = ContinuousLinearMap.id ℂ (Coeff 2) ∧
        (∀ q ∈ ball (0 : PeriodOneHminusOne) δ, ‖R q‖ ≤ 2 ∧ ‖Q q‖ ≤ 2 ∧
          ∀ m n : ℤ, Coeff.positiveIndexWeight m^2*(R q (lp.single 2 n 1)) m =
            Coeff.positiveIndexWeight n^2*(Q q (lp.single 2 n 1)) m) ∧
        ∀ q ∈ ball (0 : PeriodOneHminusOne) δ, periodOneHminusConjugation q = q →
          ∀ n : ℕ+, ∀ energy : ℂ, hillHminusMiuraEnergyPsi C s (n : ℤ) (energy,q) =
            hillHminusNormalizedNumerator Dold N R n (energy,q) := by
  obtain ⟨Dold,N,V,T,R,S,Q,_,hV,h0V,_,hRa,_,hQa,_,hR0,_,hQ0,hinv,hentry,hweight,A,D⟩ :=
    exists_hillHminus_twoWeighted_period_inverse
  obtain ⟨C,δ,W₀,W,s,hδ,hδV,hδC,H,hW,hpsi,hmatch⟩ :=
    exists_hillHminus_real_normalized_family_identification Dold D T R
      (fun q hq m n => (hentry q hq m n).1) (fun q hq => (hinv q hq).2.1)
  refine ⟨Dold,N,C,δ,W₀,W,s,R,Q,A,hδ,D.mono hδV isOpen_ball (mem_ball_self hδ),
    hδC,H,hW,hpsi,hRa.mono hδV,hQa.mono hδV,hR0,hQ0,?_,hmatch⟩
  intro q hq
  exact ⟨(hinv q (hδV hq)).2.2.2.2.1,(hinv q (hδV hq)).2.2.2.2.2,hweight q (hδV hq)⟩

end NLS.KdV
