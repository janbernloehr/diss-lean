import NLS.KdV.HillHminusOnePeriodInverse
import NLS.SequenceSpaces.AnalyticReciprocalTail

/-! # An actual jointly analytic Hilbert-valued entire numerator basis

Quadratic critical energy growth and the actual filled factor identity
give locally uniform reciprocal tails. Finite analytic heads then supply
genuine l2 membership and joint Banach analyticity.
-/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
namespace NLS.KdV

def hillHminusNumeratorCoordinates (C : HillHminusMiuraChart) (N : ℕ) (t : ℂ × PeriodOneHminusOne) (k : ℤ) : ℂ :=
  if hk : 0 < k then hillHminusUniformNumerator C N (positiveIntegerIndex k hk) t else 0

def hillHminusNumeratorHilbert (C : HillHminusMiuraChart) (N : ℕ) (t : ℂ × PeriodOneHminusOne) : NLS.Coeff 2 :=
  NLS.Coeff.ofFunctionOrZero 2 (hillHminusNumeratorCoordinates C N t)

namespace HillHminusUniformPeriodData
variable {C : HillHminusMiuraChart} {N : ℕ} {V : Set (PeriodOneHminusOne)} {A : ℝ}
variable (D : HillHminusUniformPeriodData C N V A)
include D

theorem critical_energy_growth (n : ℕ+) (q : PeriodOneHminusOne) (hq : q ∈ V) :
    Real.pi^2/4*(n : ℝ)^2 ≤ ‖hillHminusUniformCriticalPoint C N n q‖ := by
  let w := Complex.sqrt (hillHminusUniformCriticalPoint C N n q)
  have hc := D.critical_close n q hq
  have ht := norm_sub_norm_le ((Real.pi : ℂ)*(n : ℕ)) w
  rw [norm_sub_rev] at ht
  have hcn : ‖(Real.pi : ℂ)*(n : ℕ)‖ = Real.pi*(n : ℝ) := by
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos,Complex.norm_natCast]
  rw [hcn] at ht
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast n.property
  have hw : Real.pi/2*(n : ℝ) ≤ ‖w‖ := by nlinarith [Real.pi_pos]
  have he : ‖w‖^2 = ‖hillHminusUniformCriticalPoint C N n q‖ := by
    rw [← norm_pow,sq_sqrt]
  nlinarith [mul_le_mul hw hw (by positivity) (norm_nonneg w)]

theorem exists_local_numerator_reciprocal_tail (t : ℂ × PeriodOneHminusOne)
    (ht : t ∈ univ ×ˢ V) :
    ∃ U : Set (ℂ × PeriodOneHminusOne), IsOpen U ∧ t ∈ U ∧ U ⊆ univ ×ˢ V ∧
      ∃ M : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ s ∈ U, ∀ n : ℕ+, M < (n : ℕ) →
        ‖hillHminusUniformNumerator C N n s‖ ≤ K/(n : ℝ) := by
  let B : ℝ := ‖hillHminusDiscriminantDerivative t‖+1
  let R : ℝ := ‖t.1‖+1
  have hB : 0 < B := by dsimp only [B]; positivity
  have hR : 0 < R := by dsimp only [R]; positivity
  let U := ((univ ×ˢ V) ∩ ball t 1) ∩ {s | ‖hillHminusDiscriminantDerivative s‖ < B}
  have hU : IsOpen U := ((isOpen_univ.prod D.isOpen).inter isOpen_ball).inter
    (isOpen_lt analyticOnNhd_hillHminusDiscriminantDerivative.continuous.norm continuous_const)
  have htU : t ∈ U := ⟨⟨ht,mem_ball_self (by norm_num)⟩,by change ‖hillHminusDiscriminantDerivative t‖ < B; dsimp only [B]; linarith⟩
  obtain ⟨M,hM⟩ := exists_nat_gt (8*R/Real.pi^2+1)
  refine ⟨U,hU,htU,fun _ hs => hs.1.1,M,16*B/Real.pi,by positivity,?_⟩
  intro s hs n hn
  have hsR : ‖s.1‖ ≤ R := by
    have hnprod : ‖s-t‖ < 1 := by simpa only [mem_ball,dist_eq_norm] using hs.1.2
    have hdiff : ‖s.1-t.1‖ < 1 := (norm_fst_le (s-t)).trans_lt hnprod
    have hb := norm_le_norm_sub_add s.1 t.1
    dsimp only [R]
    linarith
  have hmn : (M : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.property
  have hRtail : R ≤ Real.pi^2/8*(n : ℝ)^2 := by
    have hp : (0 : ℝ) < Real.pi^2 := by positivity
    have he := (div_lt_iff₀ hp).mp (show 8*R/Real.pi^2 < (n : ℝ) by linarith)
    nlinarith [mul_nonneg hp.le (show (0 : ℝ) ≤ (n : ℝ)^2-(n : ℝ) by nlinarith)]
  have hg := D.critical_energy_growth n s.2 hs.1.1.2
  have hden : Real.pi^2/8*(n : ℝ)^2 ≤ ‖s.1-hillHminusUniformCriticalPoint C N n s.2‖ := by
    have he := norm_sub_norm_le (hillHminusUniformCriticalPoint C N n s.2) s.1
    rw [norm_sub_rev] at he
    linarith
  have hdenpos : (0 : ℝ) < Real.pi^2/8*(n : ℝ)^2 := by positivity
  have hne : s.1-hillHminusUniformCriticalPoint C N n s.2 ≠ 0 :=
    norm_pos_iff.mp (hdenpos.trans_le hden)
  have hfactor := D.numerator_factor n s.2 hs.1.1.2 s.1
  have he : hillHminusUniformNumerator C N n s =
      (2*(n : ℂ)*Real.pi)*hillHminusDiscriminantDerivative s/
        (s.1-hillHminusUniformCriticalPoint C N n s.2) := by
    apply (eq_div_iff hne).mpr
    exact (mul_comm _ _).trans hfactor
  rw [he,norm_div,norm_mul,norm_mul,norm_mul]
  simp only [norm_ofNat,Complex.norm_natCast,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  calc
    _ ≤ (2*(n : ℝ)*Real.pi)*B/(Real.pi^2/8*(n : ℝ)^2) := by
      gcongr
      exact hs.2.le
    _ = _ := by field_simp; ring

theorem numeratorHilbert_spec :
    (∀ t ∈ univ ×ˢ V, ∀ k : ℤ,
      hillHminusNumeratorHilbert C N t k = hillHminusNumeratorCoordinates C N t k) ∧
      AnalyticOnNhd ℂ (hillHminusNumeratorHilbert C N) (univ ×ˢ V) := by
  apply NLS.Coeff.analytic_l2_realization_of_local_reciprocal_tail _ _ (isOpen_univ.prod D.isOpen)
  · intro k
    by_cases hk : 0 < k
    · simpa only [hillHminusNumeratorCoordinates,dif_pos hk] using
        D.numerator_analytic (positiveIntegerIndex k hk)
    · simpa only [hillHminusNumeratorCoordinates,dif_neg hk] using
        (analyticOnNhd_const : AnalyticOnNhd ℂ (fun _ : ℂ × PeriodOneHminusOne => (0 : ℂ)) (univ ×ˢ V))
  intro t ht
  obtain ⟨U,hU,htU,hUV,M,K,hK,hbound⟩ := D.exists_local_numerator_reciprocal_tail t ht
  refine ⟨U,hU,htU,hUV,M,K,hK,?_⟩
  intro s hs k hk
  by_cases hk0 : 0 < k
  · rw [hillHminusNumeratorCoordinates,dif_pos hk0]
    have hn : M < (positiveIntegerIndex k hk0 : ℕ) := by
      change M < k.toNat
      omega
    have he := hbound s hs (positiveIntegerIndex k hk0) hn
    simpa only [positiveIntegerIndex_real,abs_of_pos (by exact_mod_cast hk0 : (0 : ℝ) < k)] using he
  · rw [hillHminusNumeratorCoordinates,dif_neg hk0,norm_zero]
    positivity

theorem numeratorHilbert_positive (t : ℂ × PeriodOneHminusOne) (ht : t ∈ univ ×ˢ V)
    (n : ℕ+) : hillHminusNumeratorHilbert C N t (n : ℤ) = hillHminusUniformNumerator C N n t := by
  rw [D.numeratorHilbert_spec.1 t ht,hillHminusNumeratorCoordinates,dif_pos (by exact_mod_cast n.pos)]
  congr 1

end HillHminusUniformPeriodData
end NLS.KdV
