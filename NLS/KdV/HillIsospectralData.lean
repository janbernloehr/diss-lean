import NLS.KdV.HillOriginalQuadraticTrace

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.LinearVolterra NLS.FunctionalAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



private def highPair_of_radicand_eq (q p : Coeff 2)
    (he : hillL2Radicand q=hillL2Radicand p) (n : ℕ) (r : HillRealHighGapPair q n) :
    HillRealHighGapPair p n where
  left := r.left
  right := r.right
  ordered := r.ordered
  left_mem := r.left_mem
  right_mem := r.right_mem
  left_zero := by rw [←he];exact r.left_zero
  right_zero := by rw [←he];exact r.right_zero
  zeros_iff := by rw [←he];exact r.zeros_iff
  orders := by rw [←he];exact r.orders

/-- Equality of the actual entire discriminants fixes every original
ordered periodic energy label, including all analytic multiplicities. -/
theorem hillRealLabels_eq_of_discriminant_eq
    (q p : RealPeriodOneHillPotential)
    (hΔ : ∀ E : ℂ, hillL2Discriminant (SpectralWeight.one.toCoeff q.val) E=
      hillL2Discriminant (SpectralWeight.one.toCoeff p.val) E) :
    hillRealLabels q.val q.property.1 q.property.2=
      hillRealLabels p.val p.property.1 p.property.2 := by
  have he : hillL2Radicand (SpectralWeight.one.toCoeff q.val)=
      hillL2Radicand (SpectralWeight.one.toCoeff p.val) := by
    funext E
    simp only [hillL2Radicand,hΔ E]
  let N := max (hillRealLabelCutoff q.val) (hillRealLabelCutoff p.val)
  have hN : 2≤N := (hillRealLabelCutoff_ge_two q.val).trans (le_max_left _ _)
  have hqN : 8*‖q.val‖≤(N : ℝ) := (hillRealLabelCutoff_bound q.val).trans (by
    exact_mod_cast (le_max_left (hillRealLabelCutoff q.val) (hillRealLabelCutoff p.val)))
  have hpN : 8*‖p.val‖≤(N : ℝ) := (hillRealLabelCutoff_bound p.val).trans (by
    exact_mod_cast (le_max_right (hillRealLabelCutoff q.val) (hillRealLabelCutoff p.val)))
  have hq := hillRealLabels_spec_at q.val q.property.1 q.property.2 N hN hqN
  have ht : HillRealCharacteristicLabeling p.val N
      (hillRealLabels q.val q.property.1 q.property.2) := by
    refine ⟨hN,hpN,hq.monotone,?_,?_,?_,hq.central_mem⟩
    · rw [←he]
      exact hq.roots
    · intro n hn
      obtain ⟨r,hr⟩ := hq.high_pair n hn
      exact ⟨highPair_of_radicand_eq _ _ he n r,hr⟩
    · rw [←he]
      exact hq.central_counts
  exact ht.unique (hillRealLabels_spec p.val p.property.1 p.property.2) p.property.1

/-- Every actual gap moment, in its original physical integral normalization,
is fixed by equality of the actual energy discriminants. -/
theorem hillRealGapIntegral_eq_of_discriminant_eq
    (q p : RealPeriodOneHillPotential)
    (hΔ : ∀ E : ℂ, hillL2Discriminant (SpectralWeight.one.toCoeff q.val) E=
      hillL2Discriminant (SpectralWeight.one.toCoeff p.val) E) (n m : ℕ) :
    hillRealGapIntegral q.val q.property.1 q.property.2 n m=
      hillRealGapIntegral p.val p.property.1 p.property.2 n m := by
  simp only [hillRealGapIntegral,hillRealLabels_eq_of_discriminant_eq q p hΔ,
    hillRealGapProfile,hΔ]

/-- On the actual mean-zero physical Hill space the full discriminant fixes
the original rough source norm by the exact quadratic action trace. -/
theorem hillSource_norm_eq_of_discriminant_eq
    (q p : RealPeriodOneHillPotential) (hq : q.val.val 0=0) (hp : p.val.val 0=0)
    (hΔ : ∀ E : ℂ, hillL2Discriminant (SpectralWeight.one.toCoeff q.val) E=
      hillL2Discriminant (SpectralWeight.one.toCoeff p.val) E) :
    ‖q.val‖=‖p.val‖ :=
  hillSource_norm_eq_of_actions_eq q p hq hp
    (fun n _ => hillRealGapIntegral_eq_of_discriminant_eq q p hΔ n 0)

end NLS.KdV
