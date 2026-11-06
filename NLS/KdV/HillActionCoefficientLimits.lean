import NLS.KdV.HillMiuraCriticalActions
import NLS.SequenceSpaces.PeriodOneRealMiuraProperness
import NLS.SequenceSpaces.CoefficientCompactness
import NLS.ZakharovShabat.SourceHigherActionCoefficientContinuity

/-! # Closedness of Hill action prescriptions under bounded factor limits -/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.KdV

/-- Subtract the exact zero-mode energy from the actual real Miura image. -/
def hillNormalizedMiuraSource (u : PeriodOneRealL2) : PeriodOneHminusOne :=
  periodOneMiura u.val-periodOneL2Inclusion (lp.single 2 0 (‖u.val‖^2 : ℝ))

theorem hillNormalizedMiuraSource_real (u : PeriodOneRealL2) :
    IsRealPeriodOneHminusOne (hillNormalizedMiuraSource u) :=
  (periodOneMiura_real u.val u.property).sub
    (periodOneL2Inclusion_single_zero_real _)

theorem hillNormalizedMiuraSource_zero (u : PeriodOneRealL2) :
    (hillNormalizedMiuraSource u).val 0 = 0 := by
  simp only [hillNormalizedMiuraSource, WeightedCoeff.sub_val,
    periodOneMiura_zero_eq_norm_sq u.val u.property, periodOneL2Inclusion_apply,
    lp.single_apply_self, sub_self]

theorem hillNormalizedMiuraSource_action (u : PeriodOneRealL2)
    (hu : u.val 0 = 0) (n : ℕ+) :
    hillHminusRealGapContourMoment (hillNormalizedMiuraSource u)
      (hillNormalizedMiuraSource_real u) n 0 =
      ((2*sourceRealHigherAction (by simp) (by norm_num)
        (hillMiuraRealSource u) (n : ℤ) 1 : ℝ) : ℂ) :=
  hillHminusRealGapContourMoment_eq_twice_critical_Dirac_action _ _ u (‖u.val‖^2) hu
    (by simp only [hillNormalizedMiuraSource, sub_add_cancel]) n

/-- Bounded normalized real factors suffice to realize any coefficientwise
limit of their actual Hill actions. No strong factor convergence or norm
conservation hypothesis is used. -/
theorem exists_hillSource_of_bounded_factor_action_limits
    (u : ℕ → PeriodOneRealL2) (hu : ∀ j, (u j).val 0 = 0)
    (hb : Bornology.IsBounded (range (fun j => (u j).val)))
    (a : ℕ+ → ℂ)
    (ha : ∀ n : ℕ+, Tendsto (fun j =>
      hillHminusRealGapContourMoment (hillNormalizedMiuraSource (u j))
        (hillNormalizedMiuraSource_real (u j)) n 0) atTop (𝓝 (a n))) :
    ∃ q : PeriodOneHminusOne, ∃ hr : IsRealPeriodOneHminusOne q,
      q.val 0 = 0 ∧ ∀ n : ℕ+, hillHminusRealGapContourMoment q hr n 0 = a n := by
  obtain ⟨v,σ,hσ,ht⟩ := Coeff.exists_coefficientwise_tendsto_subseq_of_bounded
    (fun j => (u j).val) hb
  have hv : ∀ k : ℤ, v (-k) = conj (v k) := by
    intro k
    apply tendsto_nhds_unique (ht (-k))
    have he : (fun j => (u (σ j)).val (-k)) =
        (fun j => conj ((u (σ j)).val k)) := funext fun j => (u (σ j)).property k
    rw [he]
    exact Complex.continuous_conj.continuousAt.tendsto.comp (ht k)
  let w : PeriodOneRealL2 := ⟨v,hv⟩
  have hw : w.val 0 = 0 := by
    apply tendsto_nhds_unique (ht 0)
    simpa only [hu] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0))
  refine ⟨hillNormalizedMiuraSource w,hillNormalizedMiuraSource_real w,
    hillNormalizedMiuraSource_zero w,?_⟩
  have hbs : Bornology.IsBounded (range (fun j => (u (σ j)).val)) :=
    hb.subset (by rintro _ ⟨j,rfl⟩; exact ⟨σ j,rfl⟩)
  have hbd : Bornology.IsBounded (range (fun j => hillMiuraDiagonal (u (σ j)).val)) := by
    obtain ⟨B,hB⟩ := hbs.exists_norm_le
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨‖hillMiuraDiagonal‖*B,?_⟩
    rintro _ ⟨j,rfl⟩
    exact (hillMiuraDiagonal.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (hB _ ⟨j,rfl⟩) (norm_nonneg _))
  intro n
  apply tendsto_nhds_unique _ ((ha n).comp hσ.tendsto_atTop)
  simp only [hillNormalizedMiuraSource_action _ (hu _) n,
    hillNormalizedMiuraSource_action w hw n]
  have h := tendsto_sourceRealHigherAction_of_bounded_coefficientwise
    (fun j => hillMiuraDiagonal (u (σ j)).val) (hillMiuraDiagonal w.val) hbd
    (fun j => isRealType_hillMiuraDiagonal (u (σ j))) (isRealType_hillMiuraDiagonal w)
    (by simpa only [hillMiuraDiagonal_fst] using ht) (n : ℤ) 1
  exact Complex.continuous_ofReal.continuousAt.tendsto.comp (h.const_mul 2)

end NLS.KdV
