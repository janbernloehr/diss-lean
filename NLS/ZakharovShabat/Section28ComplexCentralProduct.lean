import NLS.ZakharovShabat.SourceStandardRootNorm
import NLS.ZakharovShabat.Section28AdjacentDistance
import NLS.ZakharovShabat.SourceCanonicalRootGapIsolation
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite

/-! # Exact telescoping of the finite complex central product -/
noncomputable section
open Set Complex
open scoped ENNReal BigOperators
namespace NLS.ZakharovShabat

/-- The predecessor-root ratios telescope, without any numerator nonvanishing assumption. -/
theorem section28_product_predecessor (f : ℤ → ℂ) (a b : ℤ) (hab : a < b)
    (hf : ∀ m ∈ Finset.Ioo a b, f m ≠ 0) (hb : f (b-1) ≠ 0) :
    (∏ m ∈ Finset.Ioo a b, f (m-1)/f m) = f a/f (b-1) := by
  have hs : Finset.Ioo a b = Finset.Ico (a+1) b := by
    ext m
    simp only [Finset.mem_Ioo,Finset.mem_Ico]
    omega
  have hshift : (∏ m ∈ Finset.Ioo a b, f (m-1)) =
      ∏ m ∈ Finset.Ico a (b-1), f m := by
    rw [hs]
    simpa only [sub_eq_add_neg,add_neg_cancel_right] using
      Finset.prod_Ico_add' f (a+1) b (-1)
  have ht := Finset.prod_Ico_mul_eq_prod_Ico_add_one (by omega : a ≤ b-1) f
  have he : b-1+1 = b := by omega
  rw [he] at ht
  have hl := Finset.prod_Ioo_mul_eq_prod_Ico (f := f) hab
  rw [Finset.prod_div_distrib]
  apply (div_eq_div_iff (Finset.prod_ne_zero_iff.mpr hf) hb).mpr
  rw [hshift,ht,← hl,mul_comm]

/-- Norm control of each adjacent numerator gives the exact enclosing-root ratio. -/
theorem section28_central_product_bound (a w : ℤ → ℂ) (N : ℕ) (hN : 1 ≤ N)
    (hw : ∀ m ∈ Finset.Ioo (-(N:ℤ)) (N:ℤ), w m ≠ 0)
    (ha : ∀ m ∈ Finset.Ioo (-(N:ℤ)) (N:ℤ), ‖a m‖ ≤ ‖w (m-1)‖) :
    ‖∏ m ∈ Finset.Ioo (-(N:ℤ)) (N:ℤ), a m/w m‖ ≤
      ‖w (-(N:ℤ))/w ((N:ℤ)-1)‖ := by
  have ht := section28_product_predecessor w (-(N:ℤ)) (N:ℤ) (by omega) hw
    (hw ((N:ℤ)-1) (by simp only [Finset.mem_Ioo]; omega))
  calc
    ‖∏ m ∈ Finset.Ioo (-(N:ℤ)) (N:ℤ), a m/w m‖ =
        ∏ m ∈ Finset.Ioo (-(N:ℤ)) (N:ℤ), ‖a m/w m‖ := norm_prod _ _
    _ ≤ ∏ m ∈ Finset.Ioo (-(N:ℤ)) (N:ℤ), ‖w (m-1)/w m‖ := by
      apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
      intro m hm
      simp only [norm_div]
      exact div_le_div_of_nonneg_right (ha m hm) (norm_nonneg _)
    _ = ‖w (-(N:ℤ))/w ((N:ℤ)-1)‖ := by rw [← norm_prod,ht]

/-- Reversing the finite symmetric index set does not reflect the source potential. -/
theorem section28_central_product_reflection (f : ℤ → ℂ) (N : ℕ) :
    (∏ m ∈ Finset.Ioo (-(N:ℤ)) (N:ℤ), f (-m)) =
      ∏ m ∈ Finset.Ioo (-(N:ℤ)) (N:ℤ), f m := by
  apply Finset.prod_bij (fun m _ => -m)
  · intro m hm
    simp only [Finset.mem_Ioo] at hm ⊢
    omega
  · intro a _ b _ hab
    omega
  · intro b hb
    refine ⟨-b,?_,by omega⟩
    simp only [Finset.mem_Ioo] at hb ⊢
    omega
  · intro m _
    rfl

/-- The negative-index central product telescopes in the opposite direction. -/
theorem section28_central_product_bound_negative (a w : ℤ → ℂ) (N : ℕ) (hN : 1 ≤ N)
    (hw : ∀ m ∈ Finset.Ioo (-(N:ℤ)) (N:ℤ), w m ≠ 0)
    (ha : ∀ m ∈ Finset.Ioo (-(N:ℤ)) (N:ℤ), ‖a m‖ ≤ ‖w (m+1)‖) :
    ‖∏ m ∈ Finset.Ioo (-(N:ℤ)) (N:ℤ), a m/w m‖ ≤
      ‖w (N:ℤ)/w (-(N:ℤ)+1)‖ := by
  have hmem (m : ℤ) (hm : m ∈ Finset.Ioo (-(N:ℤ)) (N:ℤ)) :
      -m ∈ Finset.Ioo (-(N:ℤ)) (N:ℤ) := by
    simp only [Finset.mem_Ioo] at hm ⊢
    omega
  have hidx (m : ℤ) : -(m-1) = -m+1 := by omega
  have h := section28_central_product_bound (fun m => a (-m)) (fun m => w (-m)) N hN
    (fun m hm => hw (-m) (hmem m hm)) (fun m hm => by
      simpa only [hidx] using ha (-m) (hmem m hm))
  rw [section28_central_product_reflection (fun m => a m/w m) N] at h
  simpa only [neg_neg,hidx] using h

/-- Both endpoint-distance comparisons give the needed adjacent standard-root bound. -/
theorem section28_critical_le_adjacent_root
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (m k : ℤ) (z : ℂ) (hz : z ∉ sourcePeriodicSegment hp hp1 ψ k)
    (hl : ‖canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m-z‖ ≤
      ‖canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) k-z‖)
    (hr : ‖canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m-z‖ ≤
      ‖canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) k-z‖) :
    ‖canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m-z‖ ≤
      ‖sourceStandardRoot hp hp1 ψ k z‖ := by
  have hs := sourceStandardRoot_norm_sq hp hp1 ψ k z hz
  have hm := mul_le_mul hl hr (norm_nonneg _) (norm_nonneg _)
  nlinarith [norm_nonneg (sourceStandardRoot hp hp1 ψ k z)]

/-- The actual complex central products telescope on one connected source
neighborhood, for both signs and including equality at the cutoff. -/
theorem section28_complex_central_product_neighborhood
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hp1 : 1 < p)
    (W : Set (CoeffPair p)) (hW : IsOpen W) (hrealW : realTypeSourceLocus p ⊆ W) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ IsConnected U ∧ realTypeSourceLocus p ⊆ U ∧ U ⊆ W ∧
      ∀ ψ ∈ U, ∀ N : ℕ, 1 ≤ N → ∀ n : ℤ, ∀ z ∈ sourcePeriodicSegment hp hp1 ψ n,
        ((N:ℤ) ≤ n →
          ‖∏ m ∈ Finset.Ioo (-(N:ℤ)) (N:ℤ),
            (canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m-z)/
              sourceStandardRoot hp hp1 ψ m z‖ ≤
                ‖sourceStandardRoot hp hp1 ψ (-(N:ℤ)) z/sourceStandardRoot hp hp1 ψ ((N:ℤ)-1) z‖) ∧
        (n ≤ -(N:ℤ) →
          ‖∏ m ∈ Finset.Ioo (-(N:ℤ)) (N:ℤ),
            (canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m-z)/
              sourceStandardRoot hp hp1 ψ m z‖ ≤
                ‖sourceStandardRoot hp hp1 ψ (N:ℤ) z/sourceStandardRoot hp hp1 ψ (-(N:ℤ)+1) z‖) := by
  obtain ⟨D,hD,_,hrD,hdisjoint⟩ := exists_global_source_disjoint_periodicSegments hp hp1
  obtain ⟨U,hU,hUc,hrU,hsub,hadj⟩ := section28_adjacent_distance_neighborhood_within hp hp1
    (W ∩ D) (hW.inter hD) (fun ψ hψ => ⟨hrealW hψ,hrD hψ⟩)
  refine ⟨U,hU,hUc,hrU,fun ψ hψ => (hsub hψ).1,?_⟩
  intro ψ hψ N hN n z hz
  have hnot (k : ℤ) (hk : k ≠ n) : z ∉ sourcePeriodicSegment hp hp1 ψ k :=
    Set.disjoint_left.mp (hdisjoint ψ (hsub hψ).2 n k hk.symm) hz
  have hroot (k : ℤ) (hk : k ≠ n) : sourceStandardRoot hp hp1 ψ k z ≠ 0 :=
    sourceStandardRoot_ne_zero_off_segment hp hp1 ψ k z (hnot k hk)
  constructor
  · intro hn
    apply section28_central_product_bound _ _ N hN
    · intro m hm
      apply hroot m
      simp only [Finset.mem_Ioo] at hm
      omega
    · intro m hm
      simp only [Finset.mem_Ioo] at hm
      have hc := (hadj ψ hψ m n z hz).1 (by omega)
      exact section28_critical_le_adjacent_root hp hp1 ψ m (m-1) z
        (hnot (m-1) (by omega)) hc.1.le hc.2.le
  · intro hn
    apply section28_central_product_bound_negative _ _ N hN
    · intro m hm
      apply hroot m
      simp only [Finset.mem_Ioo] at hm
      omega
    · intro m hm
      simp only [Finset.mem_Ioo] at hm
      have hc := (hadj ψ hψ m n z hz).2 (by omega)
      exact section28_critical_le_adjacent_root hp hp1 ψ m (m+1) z
        (hnot (m+1) (by omega)) hc.1.le hc.2.le

end NLS.ZakharovShabat
