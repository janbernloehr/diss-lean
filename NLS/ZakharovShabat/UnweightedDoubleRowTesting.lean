import NLS.ZakharovShabat.WeightedDoubleRow

/-!
# Unweighted testing of a double resolvent row

The outer coefficient can have any origin; only its conjugate sequence
norm enters. This permits a Young-convolution row in place of a potential.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {q r : ℝ≥0∞} [Fact (1 ≤ q)] [Fact (1 ≤ r)] [q.HolderConjugate r]

/-- Two actual complementary symbols have the same full-strip double-row bound. -/
theorem norm_tsum_resolvent_double_le (hr : 1 < r) (d a f : Coeff q)
    (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n) :
    ‖∑' l : ℤ, ∑' k : ℤ, d l*a (l+k)*complementarySymbol n z l*
      complementarySymbol n z k*f k‖ ≤ ‖d‖*‖f‖*‖doubleReciprocalRow hr a n‖ := by
  let D := Coeff.reindex (Equiv.subLeft n) d
  let F := Coeff.reindex (Equiv.subLeft n) f
  let K := Coeff.puncturedLattice r hr
  let t := fun j k : ℤ => d (n-j)*a (2*n-j-k)*complementarySymbol n z (n-j)*
    complementarySymbol n z (n-k)*f (n-k)
  have hdom (j k : ℤ) : ‖t j k‖ ≤ ‖D j*a (2*n-j-k)*K k*K j*F k‖ := by
    simp only [t,D,F,Coeff.reindex_apply,Equiv.subLeft_apply,norm_mul]
    calc
      _ ≤ ‖d (n-j)‖*‖a (2*n-j-k)‖*‖K j‖*‖K k‖*‖f (n-k)‖ := by
        gcongr
        · exact norm_complementarySymbol_centered_le hr n z hz j
        · exact norm_complementarySymbol_centered_le hr n z hz k
      _ = _ := by ring
  have hs := Coeff.summable_iteratedRowTest_prod a D F K K (2*n)
  have ht : Summable (fun jk : ℤ × ℤ => ‖t jk.1 jk.2‖) :=
    hs.of_nonneg_of_le (fun _ => norm_nonneg _) (fun jk => hdom jk.1 jk.2)
  have he : (∑' l : ℤ, ∑' k : ℤ, d l*a (l+k)*complementarySymbol n z l*
      complementarySymbol n z k*f k) = ∑' j : ℤ, ∑' k : ℤ, t j k := by
    rw [← (Equiv.subLeft n).tsum_eq]
    apply tsum_congr
    intro j
    rw [← (Equiv.subLeft n).tsum_eq]
    apply tsum_congr
    intro k
    simp only [Equiv.subLeft_apply,t,show n-j+(n-k)=2*n-j-k by ring]
  rw [he,← ht.of_norm.tsum_prod]
  calc
    _ ≤ ∑' jk : ℤ × ℤ, ‖t jk.1 jk.2‖ := norm_tsum_le_tsum_norm ht
    _ ≤ ∑' jk : ℤ × ℤ, ‖D jk.1*a (2*n-jk.1-jk.2)*K jk.2*K jk.1*F jk.2‖ :=
      ht.tsum_le_tsum (fun jk => hdom jk.1 jk.2) hs
    _ = _ := hs.tsum_prod
    _ ≤ ‖D‖*‖F‖*‖Coeff.iteratedConvolutionRow a K K (2*n)‖ :=
      Coeff.tsum_norm_iteratedRowTest_le a D F K K (2*n)
    _ = _ := by rw [Coeff.norm_reindex,Coeff.norm_reindex]; rfl

end NLS.ZakharovShabat
