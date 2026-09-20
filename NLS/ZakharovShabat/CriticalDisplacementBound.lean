import NLS.ZakharovShabat.FreeSineDisplacementBound
import NLS.ZakharovShabat.SampledDiscriminantLp

/-!
# Uniform lp bounds for complete critical-point displacements

A common derivative-error majorant controls the distant critical roots through
the inverse sine estimate. A bounded finite central replacement preserves the
original exponent and supplies an explicit full-sequence norm bound.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A derivative error majorant bounds a critical root's displacement in its free disc. -/
theorem norm_critical_displacement_le {C : ℝ}
    (hC : 0 ≤ C)
    (hs : ∀ (n : ℤ) (z : ℂ), ‖z-(Real.pi : ℂ)*n‖ ≤ Real.pi/4 → ‖z-(Real.pi : ℂ)*n‖ ≤ C*‖sin z‖)
    (hp : p ≠ ⊤) (φ : PairSpace p) (A : Coeff p) (n : ℤ) (z : ℂ)
    (hz : ‖z-(Real.pi : ℂ)*n‖ ≤ Real.pi/4)
    (hcrit : deriv (canonicalDiscriminant hp φ) z = 0)
    (hb : ‖deriv (canonicalDiscriminant hp φ) z+2*sin z‖ ≤ (4/Real.pi)*‖A n‖) :
    ‖z-(Real.pi : ℂ)*n‖ ≤ (C*2/Real.pi)*‖A n‖ := by
  rw [hcrit, zero_add, norm_mul, Complex.norm_ofNat] at hb
  have hsin : ‖sin z‖ ≤ (2/Real.pi)*‖A n‖ := by
    rw [show (4 : ℝ)/Real.pi = 2*(2/Real.pi) by ring] at hb
    linarith
  exact (hs n z hz).trans ((mul_le_mul_of_nonneg_left hsin hC).trans_eq (by ring))

/-- Finite central bounds and a derivative majorant give the full lp displacement sequence. -/
theorem exists_criticalDisplacementCoeff_le {C B : ℝ} (hC : 0 ≤ C)
    (hs : ∀ (n : ℤ) (z : ℂ), ‖z-(Real.pi : ℂ)*n‖ ≤ Real.pi/4 → ‖z-(Real.pi : ℂ)*n‖ ≤ C*‖sin z‖)
    (hp : p ≠ ⊤) (φ : PairSpace p) (A : Coeff p) (N : ℕ) (ξ : ℤ → ℂ)
    (hhead : ∀ n : ℤ, n.natAbs ≤ N → ‖ξ n-(Real.pi : ℂ)*n‖ ≤ B)
    (hdisc : ∀ n : ℤ, N < n.natAbs → ‖ξ n-(Real.pi : ℂ)*n‖ ≤ Real.pi/4)
    (hcrit : ∀ n : ℤ, N < n.natAbs → deriv (canonicalDiscriminant hp φ) (ξ n) = 0)
    (hbound : ∀ (n : ℤ) (z : ℂ), ‖z-(Real.pi : ℂ)*n‖ ≤ Real.pi/4 →
      ‖deriv (canonicalDiscriminant hp φ) z+2*sin z‖ ≤ (4/Real.pi)*‖A n‖) :
    ∃ a : Coeff p, (∀ n, a n = ξ n-(Real.pi : ℂ)*n) ∧
      ‖a‖ ≤ (Finset.Icc (-(N : ℤ)) N).card*B+(C*2/Real.pi)*‖A‖ := by
  let d : ℤ → ℂ := fun n => if N < n.natAbs then ξ n-(Real.pi : ℂ)*n else 0
  let E : Coeff p := ((C*2/Real.pi : ℝ) : ℂ) • A
  have hd (n : ℤ) : ‖d n‖ ≤ ‖E n‖ := by
    by_cases hn : N < n.natAbs
    · have h := norm_critical_displacement_le hC hs hp φ A n (ξ n) (hdisc n hn) (hcrit n hn)
        (hbound n (ξ n) (hdisc n hn))
      simpa only [d, if_pos hn, E, lp.coeFn_smul, Pi.smul_apply, norm_smul, Complex.norm_real,
        Real.norm_of_nonneg (by positivity : 0 ≤ C*2/Real.pi)] using h
    · simp only [d, if_neg hn, norm_zero]
      exact norm_nonneg _
  let b : Coeff p := ⟨d, (lp.memℓp E).mono' hd⟩
  have hb : ‖b‖ ≤ (C*2/Real.pi)*‖A‖ := by
    have h := lp.norm_mono (x := b) (y := E) (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' hd
    simpa only [E, norm_smul, Complex.norm_real,
      Real.norm_of_nonneg (by positivity : 0 ≤ C*2/Real.pi)] using h
  let ζ : ℤ → ℂ := fun n => (Real.pi : ℂ)*n+b n
  have hζ : Memℓp (fun n => ζ n-(Real.pi : ℂ)*n) p := by
    simpa [ζ] using (show Memℓp (fun n => b n) p from lp.memℓp b)
  have he : spliceCentralRoots N ξ ζ = ξ := by
    funext n
    by_cases hn : N < n.natAbs <;> simp [spliceCentralRoots, hn, ζ, b, d]
  have hm := memℓp_spliceCentralRoots N ξ ζ hζ
  rw [he] at hm
  let a : Coeff p := ⟨_, hm⟩
  refine ⟨a, fun _ => rfl, ?_⟩
  apply (Coeff.norm_le_of_eq_outside_finset a b (Finset.Icc (-(N : ℤ)) N) B
    (fun n hn => hhead n (by simp only [Finset.mem_Icc] at hn; omega)) (fun n hn => ?_)).trans
    (add_le_add le_rfl hb)
  have hn' : N < n.natAbs := by simp only [Finset.mem_Icc] at hn; omega
  simp only [a, b, d, hn', if_true]

end NLS.ZakharovShabat
