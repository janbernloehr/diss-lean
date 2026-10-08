import NLS.ZakharovShabat.SobolevNLSHamiltonianHierarchy
import NLS.Fourier.SmoothPeriodOneCoefficientAlgebra

/-! # The Sobolev Riccati hierarchy is the classical physical hierarchy

For arbitrary smooth periodic functions, the constructed densities have
exactly the Fourier integrals of the classical differential recurrence.
Bilinear Parseval then identifies every Hamiltonian, with no spectral input.
-/
noncomputable section
open Set NLS.Fourier
open scoped ContDiff
namespace NLS.ZakharovShabat

private theorem scalarSobolev_sum_val {ι : Type*} (s : ℕ) (S : Finset ι)
    (f : ι → ScalarSobolev s) (j : ℤ) :
    (∑ i ∈ S, f i).val j = ∑ i ∈ S, (f i).val j := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [Finset.sum_empty,WeightedCoeff.zero_val]
  | @insert a S ha ih => simp only [Finset.sum_insert ha,WeightedCoeff.add_val,ih]

/-- Every Sobolev density has the actual Fourier coefficients of the classical
smooth differential polynomial, at all admissible orders. -/
theorem sobolevRiccatiDensity_eq_classical_coefficients
    (s : ℕ) (ab : SobolevSource s) (f g : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hpf : Function.Periodic f 1) (hpg : Function.Periodic g 1)
    (ha : ∀ j, ab.1.val j = periodOneCoefficient f j)
    (hb : ∀ j, ab.2.val j = periodOneCoefficient g j)
    (n : ℕ) (hn : n ≤ s) (j : ℤ) :
    (sobolevRiccatiDensity s ab n hn).val j = periodOneCoefficient (nlsRiccatiDensity f g n) j := by
  have hd (m : ℕ) := contDiff_nlsRiccatiDensity f g hf hg m
  have hp (m : ℕ) := periodic_nlsRiccatiDensity f g 1 hpf hpg m
  induction n using Nat.strong_induction_on generalizing j with
  | h n ih =>
    rcases n with _ | _ | n
    · simp only [sobolevRiccatiDensity_zero,nlsRiccatiDensity_zero,WeightedCoeff.neg_val,
        periodOneCoefficient_neg,hb]
    · have he := congrArg (fun a : ScalarSobolev (s-1) => a.val j)
        (sobolevRiccatiDensity_one s ab hn)
      simp only [WeightedCoeff.neg_val,hierarchySobolevDerivative_apply,hb] at he
      exact he.trans (by
        rw [nlsRiccatiDensity_one,periodOneCoefficient_neg,
          periodOneCoefficient_deriv_of_smooth_periodic g hg hpg])
    · change (sobolevRiccatiDensity s ab (n+2) hn).val j =
          periodOneCoefficient (nlsRiccatiDensity f g (n+2)) j
      let F : {ij : ℕ × ℕ // ij ∈ Finset.antidiagonal n} → ℝ → ℂ :=
        fun ij => f * (nlsRiccatiDensity f g ij.val.1 * nlsRiccatiDensity f g ij.val.2)
      have hF (ij) : Continuous (F ij) :=
        hf.continuous.mul ((hd ij.val.1).continuous.mul (hd ij.val.2).continuous)
      have hsum : Continuous (∑ ij ∈ (Finset.antidiagonal n).attach, F ij) := by
        change Continuous (fun x => (∑ ij ∈ (Finset.antidiagonal n).attach, F ij) x)
        simp only [Finset.sum_apply]
        exact continuous_finsetSum _ (fun ij _ => hF ij)
      rw [sobolevRiccatiDensity_succ_succ,nlsRiccatiDensity]
      simp only [Finset.mul_sum]
      rw [periodOneCoefficient_add _ (∑ ij ∈ (Finset.antidiagonal n).attach, F ij)
        ((contDiff_infty_iff_deriv.mp (hd (n+1))).2.continuous) hsum,
        periodOneCoefficient_sum _ F (fun ij _ => hF ij)]
      simp only [WeightedCoeff.add_val,hierarchySobolevDerivative_apply,scalarSobolev_sum_val]
      congr 1
      · rw [ih (n+1) (by omega) (by omega) j,
          periodOneCoefficient_deriv_of_smooth_periodic _ (hd (n+1)) (hp (n+1))]
      · apply Finset.sum_congr rfl
        intro ij _
        have hij := Finset.mem_antidiagonal.mp ij.property
        dsimp only [F]
        rw [hierarchySobolevTriple_apply,
          periodOneCoefficient_mul_of_smooth_periodic f
            (nlsRiccatiDensity f g ij.val.1 * nlsRiccatiDensity f g ij.val.2)
            hf ((hd ij.val.1).mul (hd ij.val.2))
            hpf ((hp ij.val.1).mul (hp ij.val.2))]
        simp only [hierarchySobolevInclusion_apply]
        apply tsum_congr
        intro l
        rw [ha]
        congr 1
        rw [periodOneCoefficient_mul_of_smooth_periodic _ _ (hd ij.val.1) (hd ij.val.2)
          (hp ij.val.1) (hp ij.val.2)]
        apply tsum_congr
        intro m
        rw [ih ij.val.1 (by omega) (by omega) (l-m),ih ij.val.2 (by omega) (by omega) m]

/-- The analytic Sobolev construction equals the independently defined
classical physical Hamiltonian for every smooth periodic source and order. -/
theorem sobolevNLSHamiltonian_eq_classical
    (s : ℕ) (ab : SobolevSource s) (f g : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hpf : Function.Periodic f 1) (hpg : Function.Periodic g 1)
    (ha : ∀ j, ab.1.val j = periodOneCoefficient f j)
    (hb : ∀ j, ab.2.val j = periodOneCoefficient g j)
    (k : ℕ) (hk : k ≤ s+1) :
    sobolevNLSHamiltonian s ab k hk = classicalNLSHamiltonian f g k := by
  rcases k with _ | n
  · rfl
  · rw [sobolevNLSHamiltonian_succ_eq_tsum s n (by omega)]
    simp_rw [ha,sobolevRiccatiDensity_eq_classical_coefficients s ab f g hf hg hpf hpg ha hb]
    have h := tsum_bilinear_unitFourierCoefficient hf.continuous (contDiff_nlsRiccatiDensity f g hf hg n).continuous
    have he (u : ℝ → ℂ) (j : ℤ) : unitFourierCoefficient u j = periodOneCoefficient u j :=
      unitFourierCoefficient_eq_fourierCoeffOn u j
    simp only [he] at h
    rw [h]
    rfl

end NLS.ZakharovShabat
