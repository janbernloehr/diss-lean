import NLS.KdV.HillFiniteAbelianPhase

/-! # Actual Abelian terminal bounds and a convergence criterion

The selected real terminal lies in [-pi,pi]. Off the selected mode,
its regular correction is bounded by 2*pi times an actual angular
differential bound. Summable differential tails therefore give a
summable series of the original correction terms.
-/
noncomputable section
open Set Complex Filter Topology MeasureTheory
open NLS.ZakharovShabat
namespace NLS.KdV

theorem norm_regularTerm_le_of_differential_bound
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1 ≤ n) (k : ℕ) (hk : 1 ≤ k)
    (hkn : k ≠ n) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ θ ∈ Icc (-Real.pi) Real.pi,
      ‖hillAbelianCosineDifferential q.val q.property.1 q.property.2 n hn k (θ : ℂ)‖ ≤ M) :
    ‖hillDirichletRegularAbelianTerm q n hn k hk‖ ≤ 2*Real.pi*M := by
  by_cases hc : hillRealGapHalfLength q.val q.property.1 q.property.2 k = 0
  · rw [hillDirichletRegularAbelianTerm_closed q n hn k hk hc,norm_zero]
    positivity
  · let θ := hillSelectedDirichletAngle q k hk hc
    have hs := hillSelectedDirichletAngle_spec q k hk hc
    have hθ : θ ∈ Icc (-Real.pi) Real.pi := hs.1
    rw [hillDirichletRegularAbelianTerm_eq_terminal q n hn k hk hc θ hs.2.1 hs.2.2.2,
      hillRegularAbelianPrimitive,if_neg hkn,zero_mul,sub_zero,
      hillAbelianCosinePrimitive_real_eq_intervalIntegral]
    have hpoint : ∀ t ∈ uIoc Real.pi θ,
        ‖hillAbelianCosineDifferential q.val q.property.1 q.property.2 n hn k (t : ℂ)‖ ≤ M := by
      intro t ht
      rw [uIoc_of_ge hθ.2] at ht
      exact hbound t ⟨hθ.1.trans ht.1.le,ht.2⟩
    have hlen : |θ-Real.pi| ≤ 2*Real.pi := by
      rw [abs_of_nonpos (sub_nonpos.mpr hθ.2)]
      linarith [hθ.1]
    exact (intervalIntegral.norm_integral_le_of_norm_le_const hpoint).trans
      ((mul_le_mul_of_nonneg_left hlen hM).trans_eq (by ring))

theorem summable_regularTerms_of_summable_differential_tail
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1 ≤ n) (M : ℕ → ℝ) (hM : Summable M)
    (hbound : ∀ᶠ k : ℕ in atTop, 0 ≤ M k ∧ ∀ θ ∈ Icc (-Real.pi) Real.pi,
      ‖hillAbelianCosineDifferential q.val q.property.1 q.property.2 n hn (k+1) (θ : ℂ)‖ ≤ M k) :
    Summable (fun k : ℕ => hillDirichletRegularAbelianTerm q n hn (k+1) (by omega)) := by
  apply (hM.mul_left (2*Real.pi)).of_norm_bounded_eventually_nat
  filter_upwards [hbound,eventually_gt_atTop n] with k hk hkn
  exact norm_regularTerm_le_of_differential_bound q n hn (k+1) (by omega) (by omega) (M k) hk.1 hk.2

end NLS.KdV
