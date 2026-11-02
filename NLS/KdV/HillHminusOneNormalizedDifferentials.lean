import NLS.KdV.HillHminusOneHilbertPeriod
import NLS.KdV.FrequencySeries

/-! # Constructed infinite normalized entire Hill differentials near zero

Pair the actual Hilbert numerator basis with the constructed inverse
columns. The sums converge absolutely, are jointly analytic, and their
literal contour periods equal the Kronecker delta for every positive pair.
Canonical products and rough/global spectral compatibility remain separate.
-/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
namespace NLS.KdV

def hillHminusNormalizedNumerator (C : HillHminusMiuraChart) (N : ℕ)
    (R : PeriodOneHminusOne → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2)) (n : ℕ+)
    (t : ℂ × PeriodOneHminusOne) : ℂ :=
  NLS.Coeff.dualPairing (R t.2 (lp.single 2 (n : ℤ) 1)) (hillHminusNumeratorHilbert C N t)

namespace HillHminusUniformPeriodData
variable {C : HillHminusMiuraChart} {N : ℕ} {V : Set (PeriodOneHminusOne)} {A : ℝ}
variable (D : HillHminusUniformPeriodData C N V A)
include D

theorem normalizedNumerator_analytic
    (R : PeriodOneHminusOne → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (hR : AnalyticOnNhd ℂ R V) (n : ℕ+) :
    AnalyticOnNhd ℂ (hillHminusNormalizedNumerator C N R n) (univ ×ˢ V) := by
  intro t ht
  let en : NLS.Coeff 2 := lp.single 2 (n : ℤ) 1
  have hs : AnalyticAt ℂ (fun s : ℂ × PeriodOneHminusOne => R s.2) t :=
    (hR t.2 ht.2).comp (f := fun s : ℂ × PeriodOneHminusOne => s.2) analyticAt_snd
  have hc : AnalyticAt ℂ (fun s : ℂ × PeriodOneHminusOne => R s.2 en) t := by
    simpa only [Function.comp_def] using!
      ((ContinuousLinearMap.apply ℂ (NLS.Coeff 2) en).analyticAt (R t.2)).comp
        (f := fun s : ℂ × PeriodOneHminusOne => R s.2) hs
  have hb := (NLS.Coeff.dualPairing (p := 2) (q := 2)).analyticAt_bilinear
    (R t.2 en,hillHminusNumeratorHilbert C N t)
  simpa only [hillHminusNormalizedNumerator,en,Function.comp_def] using!
    hb.comp (f := fun s : ℂ × PeriodOneHminusOne =>
      (R s.2 en,hillHminusNumeratorHilbert C N s)) (hc.prod (D.numeratorHilbert_spec.2 t ht))

theorem normalizedNumerator_entire
    (R : PeriodOneHminusOne → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (hR : AnalyticOnNhd ℂ R V) (n : ℕ+) (q : PeriodOneHminusOne) (hq : q ∈ V) :
    AnalyticOnNhd ℂ (fun z : ℂ => hillHminusNormalizedNumerator C N R n (z,q)) univ := by
  intro z _
  simpa only [Function.comp_def] using!
    (D.normalizedNumerator_analytic R hR n (z,q) ⟨mem_univ _,hq⟩).comp
      (f := fun w : ℂ => (w,q)) (analyticAt_id.prod analyticAt_const)

theorem normalizedNumerator_series
    (R : PeriodOneHminusOne → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2)) (n : ℕ+)
    (t : ℂ × PeriodOneHminusOne) (ht : t ∈ univ ×ˢ V) :
    Summable (fun m : ℤ => ‖(R t.2 (lp.single 2 (n : ℤ) 1)) m*
      hillHminusNumeratorCoordinates C N t m‖) ∧
    hillHminusNormalizedNumerator C N R n t = ∑' m : ℤ,
      (R t.2 (lp.single 2 (n : ℤ) 1)) m*hillHminusNumeratorCoordinates C N t m := by
  have he := D.numeratorHilbert_spec.1 t ht
  constructor
  · simpa only [he] using NLS.Coeff.summable_norm_dualPairing
      (R t.2 (lp.single 2 (n : ℤ) 1)) (hillHminusNumeratorHilbert C N t)
  · simp only [hillHminusNormalizedNumerator,NLS.Coeff.dualPairing_apply,he]

theorem normalizedNumerator_positive_series
    (R : PeriodOneHminusOne → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2)) (n : ℕ+)
    (t : ℂ × PeriodOneHminusOne) (ht : t ∈ univ ×ˢ V) :
    Summable (fun m : ℕ+ => ‖(R t.2 (lp.single 2 (n : ℤ) 1)) (m : ℤ)*
      hillHminusUniformNumerator C N m t‖) ∧
    hillHminusNormalizedNumerator C N R n t = ∑' m : ℕ+,
      (R t.2 (lp.single 2 (n : ℤ) 1)) (m : ℤ)*hillHminusUniformNumerator C N m t := by
  let c := R t.2 (lp.single 2 (n : ℤ) 1)
  have hi : Function.Injective (fun m : ℕ+ => (m : ℤ)) := by
    intro i j hij
    apply Subtype.ext
    exact Int.ofNat_inj.mp hij
  constructor
  · simpa only [Function.comp_def,c,D.numeratorHilbert_positive t ht] using!
      (NLS.Coeff.summable_norm_dualPairing c (hillHminusNumeratorHilbert C N t)).comp_injective hi
  change NLS.Coeff.dualPairing c (hillHminusNumeratorHilbert C N t) = _
  rw [NLS.Coeff.dualPairing_apply]
  have hz (m : ℤ) (hm : m ≤ 0) : c m*hillHminusNumeratorHilbert C N t m = 0 := by
    rw [D.numeratorHilbert_spec.1 t ht m,hillHminusNumeratorCoordinates,dif_neg (by omega),mul_zero]
  rw [tsum_eq_positive_of_nonpositive_zero _ hz]
  simp_rw [D.numeratorHilbert_positive t ht]
  rfl

theorem normalizedNumerator_free
    (R : PeriodOneHminusOne → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (hR0 : R 0 = ContinuousLinearMap.id ℂ (NLS.Coeff 2)) (n : ℕ+) (z : ℂ) :
    hillHminusNormalizedNumerator C N R n (z,0) = classicalHillFreePsi n z := by
  simp only [hillHminusNormalizedNumerator,hR0,ContinuousLinearMap.id_apply,NLS.Coeff.dualPairing_apply]
  have he : (∑' m : ℤ, (lp.single 2 (n : ℤ) (1 : ℂ) : NLS.Coeff 2) m*
      hillHminusNumeratorHilbert C N (z,0) m) = hillHminusNumeratorHilbert C N (z,0) (n : ℤ) := by
    simp [lp.single_apply,Pi.single_apply]
  rw [he,D.numeratorHilbert_positive (z,0) ⟨mem_univ _,D.zero_mem⟩,D.numerator_free]

theorem normalizedNumerator_period (n k : ℕ+) (q : PeriodOneHminusOne) (hq : q ∈ V)
    (T R : PeriodOneHminusOne → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (hentry : ∀ m j : ℤ, (T q (lp.single 2 j 1)) m = hillHminusPeriodMatrix C N q m j)
    (hTR : (T q).comp (R q) = ContinuousLinearMap.id ℂ (NLS.Coeff 2)) :
    (2*(Real.pi : ℂ))⁻¹ * ∮ z in C((Real.pi : ℂ)*(k : ℕ),Real.pi/4),
      hillHminusNormalizedNumerator C N R n (z^2,q)/hillHminusContinuedRoot (z^2,q)*(2*z) =
        if n = k then 1 else 0 := by
  change (2*(Real.pi : ℂ))⁻¹ * (∮ z in C((Real.pi : ℂ)*(k : ℕ),Real.pi/4),
    NLS.Coeff.dualPairing (R q (lp.single 2 (n : ℤ) 1)) (hillHminusNumeratorHilbert C N (z^2,q))/
      hillHminusContinuedRoot (z^2,q)*(2*z)) = _
  rw [← D.hilbertPeriod_integral k q hq,D.hilbertPeriod_eq_row k q hq (T q) hentry]
  have he := congrArg (fun L : NLS.Coeff 2 →L[ℂ] NLS.Coeff 2 => L (lp.single 2 (n : ℤ) 1)) hTR
  change T q (R q (lp.single 2 (n : ℤ) 1)) = lp.single 2 (n : ℤ) 1 at he
  change (T q (R q (lp.single 2 (n : ℤ) 1))) (k : ℤ) = _
  rw [he]
  simp only [lp.single_apply,Pi.single_apply]
  by_cases hnk : n = k
  · subst n
    simp only [ite_true]
  · have hkn : (k : ℤ) ≠ (n : ℤ) := by exact_mod_cast Ne.symm hnk
    simp only [if_neg hkn,if_neg hnk]

theorem normalizedNumerator_energy_period (n k : ℕ+) (q : PeriodOneHminusOne) (hq : q ∈ V)
    (T R : PeriodOneHminusOne → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (hentry : ∀ m j : ℤ, (T q (lp.single 2 j 1)) m = hillHminusPeriodMatrix C N q m j)
    (hTR : (T q).comp (R q) = ContinuousLinearMap.id ℂ (NLS.Coeff 2)) :
    (2*(Real.pi : ℂ))⁻¹ * ∫ᶜ z in classicalHillHighEnergyContour k,
      holomorphicOneForm (fun z => hillHminusNormalizedNumerator C N R n (z,q)/
        hillHminusContinuedRoot (z,q)) z = if n = k then 1 else 0 := by
  let f : ℂ → ℂ := fun z => hillHminusNormalizedNumerator C N R n (z,q)/hillHminusContinuedRoot (z,q)
  have hsq (z : ℂ) : HasDerivAt (fun w : ℂ => w^2) (2*z) z := by
    simpa using! (hasDerivAt_id z).pow 2
  have hp := (holomorphicPathPullback_integral_and_integrability f
    (fun z => f (z^2)*(2*z)) (fun z : ℂ => z^2) (fun z : ℂ => 2*z) (continuous_id.pow 2)
    (circlePath ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4))
    ((circlePath_contDiffOn _ _).of_le (by norm_num))
    (fun _ _ => hsq _) (fun _ _ => rfl)).2
  rw [curveIntegral_circlePath] at hp
  change (2*(Real.pi : ℂ))⁻¹ * (∫ᶜ z in classicalHillHighEnergyContour k, holomorphicOneForm f z) = _
  rw [classicalHillHighEnergyContour,hp]
  exact D.normalizedNumerator_period n k q hq T R hentry hTR

end HillHminusUniformPeriodData

theorem hillHminusPeriodOperator_nonpositive_row (C : HillHminusMiuraChart) (N : ℕ) (q : PeriodOneHminusOne)
    (T : NLS.Coeff 2 →L[ℂ] NLS.Coeff 2)
    (hentry : ∀ m j : ℤ, (T (lp.single 2 j 1)) m = hillHminusPeriodMatrix C N q m j)
    (m : ℤ) (hm : m ≤ 0) :
    (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 m).comp T = lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 m := by
  apply NLS.Coeff.continuousLinearMap_eq_of_single (by norm_num : (2 : ENNReal) ≠ ⊤)
  intro j
  change (T (lp.single 2 j 1)) m = (lp.single 2 j (1 : ℂ) : NLS.Coeff 2) m
  rw [hentry,hillHminusPeriodMatrix,dif_neg (by omega : ¬ 0 < m)]
  simp only [lp.single_apply,Pi.single_apply]

theorem hillHminusPeriodInverse_positive_column (C : HillHminusMiuraChart) (N : ℕ) (q : PeriodOneHminusOne)
    (T R : NLS.Coeff 2 →L[ℂ] NLS.Coeff 2)
    (hentry : ∀ m j : ℤ, (T (lp.single 2 j 1)) m = hillHminusPeriodMatrix C N q m j)
    (hTR : T.comp R = ContinuousLinearMap.id ℂ (NLS.Coeff 2)) (n : ℕ+) :
    ∀ m ≤ (0 : ℤ), (R (lp.single 2 (n : ℤ) 1)) m = 0 := by
  intro m hm
  have hrow := congrArg (fun L : NLS.Coeff 2 →L[ℂ] ℂ => L (R (lp.single 2 (n : ℤ) 1)))
    (hillHminusPeriodOperator_nonpositive_row C N q T hentry m hm)
  have he := congrArg (fun L : NLS.Coeff 2 →L[ℂ] NLS.Coeff 2 => L (lp.single 2 (n : ℤ) 1)) hTR
  change T (R (lp.single 2 (n : ℤ) 1)) = lp.single 2 (n : ℤ) 1 at he
  change (T (R (lp.single 2 (n : ℤ) 1))) m = (R (lp.single 2 (n : ℤ) 1)) m at hrow
  rw [he] at hrow
  rw [← hrow]
  have hn : (0 : ℤ) < n := by exact_mod_cast n.pos
  simp only [lp.single_apply,Pi.single_apply,if_neg (by omega : m ≠ (n : ℤ))]

/-- The actual infinite entire family is constructed on one neighborhood,
with every contour normalization and the exact entire free slice. -/
theorem exists_hillHminus_infinite_normalized_differentials :
    ∃ C : HillHminusMiuraChart, ∃ N : ℕ, ∃ V : Set (PeriodOneHminusOne),
      ∃ R : PeriodOneHminusOne → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2),
        0 < N ∧ IsOpen V ∧ 0 ∈ V ∧ AnalyticOnNhd ℂ R V ∧
        R 0 = ContinuousLinearMap.id ℂ (NLS.Coeff 2) ∧ (∀ q ∈ V, ‖R q‖ ≤ 2) ∧
        (∀ n : ℕ+, AnalyticOnNhd ℂ (hillHminusNormalizedNumerator C N R n) (univ ×ˢ V)) ∧
        (∀ n : ℕ+, ∀ z : ℂ, hillHminusNormalizedNumerator C N R n (z,0) = classicalHillFreePsi n z) ∧
        (∀ n k : ℕ+, ∀ q ∈ V,
          (2*(Real.pi : ℂ))⁻¹ * ∮ z in C((Real.pi : ℂ)*(k : ℕ),Real.pi/4),
            hillHminusNormalizedNumerator C N R n (z^2,q)/hillHminusContinuedRoot (z^2,q)*(2*z) =
              if n = k then 1 else 0) ∧
        ∃ A : ℝ, HillHminusUniformPeriodData C N V A := by
  obtain ⟨C,N,V,T,R,hN,hV,h0V,hTa,hRa,hT0,hR0,hinv,hentry,A,D⟩ :=
    exists_hillHminus_analytic_period_inverse
  exact ⟨C,N,V,R,hN,hV,h0V,hRa,hR0,fun q hq => (hinv q hq).2.2,
    D.normalizedNumerator_analytic R hRa,D.normalizedNumerator_free R hR0,
    fun n k q hq => D.normalizedNumerator_period n k q hq T R (hentry q hq) (hinv q hq).1,A,D⟩

end NLS.KdV
