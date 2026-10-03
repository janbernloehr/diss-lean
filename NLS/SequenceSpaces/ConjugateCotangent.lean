import NLS.SequenceSpaces.SourceCotangentNormBound

/-! # Recovering conjugate Fourier coefficients from a bounded functional

Finite dual tests control every truncation of the unit-mode values of a
functional on ℓp. A bounded pointwise limit therefore belongs to the
conjugate ℓq space, with norm bounded by the original operator norm.
-/

noncomputable section
open Filter
open scoped ENNReal Topology
namespace NLS.Coeff
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [q.HolderConjugate p]

/-- Scalar multiplication of a unit mode gives its arbitrary coefficient. -/
theorem apply_single_eq_mul (L : Coeff p →L[ℂ] ℂ) (n : ℤ) (z : ℂ) :
    L (lp.single p n z) = L (lp.single p n 1)*z := by
  have hz : (lp.single p n z : Coeff p) = z • lp.single p n (1 : ℂ) := by
    simpa only [smul_eq_mul,mul_one] using (lp.single_smul (E := fun _ : ℤ => ℂ) p n z (1 : ℂ))
  rw [hz,map_smul,smul_eq_mul,mul_comm]

/-- Finite-exponent bounded functionals have conjugate coefficient
representatives, with a sharp one-sided norm bound. -/
theorem exists_conjugate_cotangent (hp : p ≠ ⊤) (hq : q ≠ ⊤) (L : Coeff p →L[ℂ] ℂ) :
    ∃ a : Coeff q, (∀ n : ℤ, a n = L (lp.single p n 1)) ∧ ‖a‖ ≤ ‖L‖ := by
  classical
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (show 1 ≤ p from Fact.out)).ne'
  have hq0 : q ≠ 0 := (zero_lt_one.trans_le (show 1 ≤ q from Fact.out)).ne'
  have hpR : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have hqR : 0 < q.toReal := ENNReal.toReal_pos hq0 hq
  let A (s : Finset ℤ) : Coeff q := ∑ n ∈ s, lp.single q n (L (lp.single p n 1))
  have hA (s : Finset ℤ) (n : ℤ) : A s n = if n ∈ s then L (lp.single p n 1) else 0 := by
    change (lp.evalₗ (𝕜 := ℂ) (fun _ : ℤ => ℂ) q n) (∑ i ∈ s, lp.single q i (L (lp.single p i 1))) = _
    rw [map_sum]
    simp [lp.evalₗ_apply,lp.single_apply,Pi.single_apply]
  have hpair (s : Finset ℤ) (b : Coeff p) : dualPairing (A s) b = L (truncate s b) := by
    have hsingle (n : ℤ) (z : ℂ) : dualPairing (lp.single q n z) b = z*b n := by
      simp [dualPairing_apply,lp.single_apply,Pi.single_apply]
    simp only [A,truncate,map_sum,sum_apply]
    apply Finset.sum_congr rfl
    intro n hn
    rw [hsingle,apply_single_eq_mul L n (b n)]
  have hbound (s : Finset ℤ) : ‖A s‖ ≤ ‖L‖ := by
    apply norm_le_of_finite_dual (p := q) (q := p) hqR hpR hq (A s) (norm_nonneg L)
    intro b
    rw [← dualPairing_finite_right (p := q) (q := p),hpair]
    exact (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left (norm_truncate_le hp0 s _) (norm_nonneg L))
  have hlim : Tendsto (fun s : Finset ℤ => (A s : ℤ → ℂ)) atTop
      (𝓝 (fun n => L (lp.single p n 1))) := by
    rw [tendsto_pi_nhds]
    intro n
    apply tendsto_nhds_of_eventually_eq
    filter_upwards [eventually_ge_atTop ({n} : Finset ℤ)] with s hs
    exact (hA s n).trans (if_pos (hs (by simp)))
  have hbounded : Bornology.IsBounded (Set.range A) := by
    apply isBounded_iff_forall_norm_le.mpr
    exact ⟨‖L‖,by rintro _ ⟨s,rfl⟩; exact hbound s⟩
  let a : Coeff q := ⟨_,lp.memℓp_of_tendsto hbounded hlim⟩
  exact ⟨a,fun _ => rfl,lp.norm_le_of_tendsto (Eventually.of_forall hbound) hlim⟩

/-- The canonical conjugate coefficient representative of a source functional. -/
def conjugateCotangent (hp : p ≠ ⊤) (hq : q ≠ ⊤) (L : Coeff p →L[ℂ] ℂ) : Coeff q :=
  (exists_conjugate_cotangent hp hq L).choose

@[simp] theorem conjugateCotangent_apply (hp : p ≠ ⊤) (hq : q ≠ ⊤)
    (L : Coeff p →L[ℂ] ℂ) (n : ℤ) : conjugateCotangent hp hq L n = L (lp.single p n 1) :=
  (exists_conjugate_cotangent hp hq L).choose_spec.1 n

theorem norm_conjugateCotangent_le (hp : p ≠ ⊤) (hq : q ≠ ⊤) (L : Coeff p →L[ℂ] ℂ) :
    ‖conjugateCotangent hp hq L‖ ≤ ‖L‖ :=
  (exists_conjugate_cotangent hp hq L).choose_spec.2

/-- The recovered coefficients represent the entire functional, by finite-mode density. -/
theorem dualPairing_conjugateCotangent (hp : p ≠ ⊤) (hq : q ≠ ⊤) (L : Coeff p →L[ℂ] ℂ) :
    dualPairing (conjugateCotangent hp hq L) = L :=
  (eq_dualPairing_of_single hp L _ (fun n => (conjugateCotangent_apply hp hq L n).symm)).symm

/-- The scalar coefficient representative has exactly the original operator norm. -/
theorem norm_conjugateCotangent (hp : p ≠ ⊤) (hq : q ≠ ⊤) (L : Coeff p →L[ℂ] ℂ) :
    ‖conjugateCotangent hp hq L‖ = ‖L‖ := by
  apply le_antisymm (norm_conjugateCotangent_le hp hq L)
  calc
    ‖L‖ = ‖dualPairing (conjugateCotangent hp hq L)‖ :=
      congrArg norm (dualPairing_conjugateCotangent hp hq L).symm
    _ ≤ ‖conjugateCotangent hp hq L‖ := by
      apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
      exact norm_dualPairing_le (p := q) (q := p) _

end NLS.Coeff
