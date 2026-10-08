import NLS.ZakharovShabat.SobolevHierarchyOperations

/-! # The physical Riccati recurrence on the full integer Sobolev scale

The n-th density maps Hˢ pairs analytically into H^(s-n), for n ≤ s.
The definition differentiates original Fourier coefficients with frequency
2π and multiplies them by actual convolutions; no spectral action is used.
-/
noncomputable section
namespace NLS.ZakharovShabat

/-- Appendix H's Riccati densities in the original period-one Sobolev spaces. -/
def sobolevRiccatiDensity (s : ℕ) (ab : SobolevSource s) :
    (n : ℕ) → n ≤ s → ScalarSobolev (s-n)
  | 0, _ => -ab.2
  | 1, hn => -hierarchySobolevDerivative s (s-1) (by omega) ab.2
  | n+2, hn =>
      hierarchySobolevDerivative (s-(n+1)) (s-(n+2)) (by omega)
        (sobolevRiccatiDensity s ab (n+1) (by omega)) +
      ∑ ij ∈ (Finset.antidiagonal n).attach,
        hierarchySobolevTriple (s-(n+2))
          (hierarchySobolevInclusion s (s-(n+2)+1) (by omega) ab.1)
          (hierarchySobolevInclusion (s-ij.val.1) (s-(n+2)+1)
            (by have he := Finset.mem_antidiagonal.mp ij.property; omega)
            (sobolevRiccatiDensity s ab ij.val.1
              (by have he := Finset.mem_antidiagonal.mp ij.property; omega)))
          (hierarchySobolevInclusion (s-ij.val.2) (s-(n+2)+1)
            (by have he := Finset.mem_antidiagonal.mp ij.property; omega)
            (sobolevRiccatiDensity s ab ij.val.2
              (by have he := Finset.mem_antidiagonal.mp ij.property; omega)))
termination_by n => n
decreasing_by
  all_goals first | omega | (have he := Finset.mem_antidiagonal.mp ij.property; omega)

@[simp] theorem sobolevRiccatiDensity_zero (s : ℕ) (ab : SobolevSource s) :
    sobolevRiccatiDensity s ab 0 (Nat.zero_le s) = -ab.2 := by rw [sobolevRiccatiDensity]

@[simp] theorem sobolevRiccatiDensity_one (s : ℕ) (ab : SobolevSource s) (hs : 1 ≤ s) :
    sobolevRiccatiDensity s ab 1 hs = -hierarchySobolevDerivative s (s-1) (by omega) ab.2 := by rw [sobolevRiccatiDensity]

/-- Each derivative is taken before adding the cubic terms of lower Riccati order. -/
theorem sobolevRiccatiDensity_succ_succ (s : ℕ) (ab : SobolevSource s) (n : ℕ) (hn : n+2 ≤ s) :
    sobolevRiccatiDensity s ab (n+2) hn =
      hierarchySobolevDerivative (s-(n+1)) (s-(n+2)) (by omega)
        (sobolevRiccatiDensity s ab (n+1) (by omega)) +
      ∑ ij ∈ (Finset.antidiagonal n).attach,
        hierarchySobolevTriple (s-(n+2))
          (hierarchySobolevInclusion s (s-(n+2)+1) (by omega) ab.1)
          (hierarchySobolevInclusion (s-ij.val.1) (s-(n+2)+1)
            (by have he := Finset.mem_antidiagonal.mp ij.property; omega)
            (sobolevRiccatiDensity s ab ij.val.1
              (by have he := Finset.mem_antidiagonal.mp ij.property; omega)))
          (hierarchySobolevInclusion (s-ij.val.2) (s-(n+2)+1)
            (by have he := Finset.mem_antidiagonal.mp ij.property; omega)
            (sobolevRiccatiDensity s ab ij.val.2
              (by have he := Finset.mem_antidiagonal.mp ij.property; omega))) := by rw [sobolevRiccatiDensity]

/-- Every Riccati density is an entire analytic map into its actual lower
Sobolev space, including the highest derivative at the H⁰ endpoint. -/
theorem analyticAt_sobolevRiccatiDensity (s n : ℕ) (hn : n ≤ s) (ab : SobolevSource s) :
    AnalyticAt ℂ (fun cd => sobolevRiccatiDensity s cd n hn) ab := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | n
    · simpa only [Nat.sub_zero,sobolevRiccatiDensity_zero] using!
        ((ContinuousLinearMap.snd ℂ (ScalarSobolev s) (ScalarSobolev s)).analyticAt ab).neg
    · have he : (fun cd : SobolevSource s => sobolevRiccatiDensity s cd (0+1) hn) =
          (fun cd => -hierarchySobolevDerivative s (s-1) (by omega) cd.2) := by
        funext cd
        exact sobolevRiccatiDensity_one s cd hn
      rw [he]
      exact (((hierarchySobolevDerivative s (s-1) (by omega)).analyticAt ab.2).comp
        ((ContinuousLinearMap.snd ℂ (ScalarSobolev s) (ScalarSobolev s)).analyticAt ab)).neg
    · simp only [sobolevRiccatiDensity_succ_succ]
      apply AnalyticAt.add
      · exact ((hierarchySobolevDerivative (s-(n+1)) (s-(n+2)) (by omega)).analyticAt _).comp
          (ih (n+1) (by omega) (by omega))
      · apply Finset.analyticAt_fun_sum
        intro ij _
        have he := Finset.mem_antidiagonal.mp ij.property
        apply analyticAt_hierarchySobolevTriple
        · exact ((hierarchySobolevInclusion s (s-(n+2)+1) (by omega)).analyticAt ab.1).comp
            ((ContinuousLinearMap.fst ℂ (ScalarSobolev s) (ScalarSobolev s)).analyticAt ab)
        · exact ((hierarchySobolevInclusion (s-ij.val.1) (s-(n+2)+1) (by omega)).analyticAt _).comp
            (ih ij.val.1 (by omega) (by omega))
        · exact ((hierarchySobolevInclusion (s-ij.val.2) (s-(n+2)+1) (by omega)).analyticAt _).comp
            (ih ij.val.2 (by omega) (by omega))

/-- The first nonlinear density is exactly `-b'' + a*b²` in original
Fourier coefficients, with period-one frequency `2π`. -/
theorem sobolevRiccatiDensity_two_apply (s : ℕ) (hs : 2 ≤ s) (ab : SobolevSource s) (j : ℤ) :
    (sobolevRiccatiDensity s ab 2 hs).val j =
      -(2*Complex.I*(Real.pi:ℂ)*j)^2*ab.2.val j +
        ∑' l : ℤ, ab.1.val (j-l) * ∑' m : ℤ, ab.2.val (l-m)*ab.2.val m := by
  have hattach : (Finset.antidiagonal 0).attach = {⟨(0,0),by simp⟩} := by
    ext ⟨⟨u,v⟩,huv⟩
    have he := Finset.mem_antidiagonal.mp huv
    have hu : u = 0 := by omega
    have hv : v = 0 := by omega
    subst u
    subst v
    exact iff_of_true (Finset.mem_attach _ _) (Finset.mem_singleton.mpr rfl)
  rw [sobolevRiccatiDensity_succ_succ s ab 0 hs,hattach,Finset.sum_singleton]
  simp only [WeightedCoeff.add_val,hierarchySobolevDerivative_apply,
    hierarchySobolevTriple_apply,hierarchySobolevInclusion_apply,
    sobolevRiccatiDensity_zero,WeightedCoeff.neg_val,
    neg_mul_neg]
  have h1 : (sobolevRiccatiDensity s ab (0+1) (by omega)).val j =
      -(2*Complex.I*(Real.pi:ℂ)*j*ab.2.val j) := by
    have he := congrArg (fun a : ScalarSobolev (s-1) => a.val j)
      (sobolevRiccatiDensity_one s ab (by omega))
    simpa only [WeightedCoeff.neg_val,hierarchySobolevDerivative_apply] using he
  rw [h1]
  ring

end NLS.ZakharovShabat
