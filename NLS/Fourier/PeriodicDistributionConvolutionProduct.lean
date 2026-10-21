import NLS.Fourier.PeriodicDistributionFourierGrowth
import NLS.Fourier.PeriodicFourierLebesgueProduct
import Mathlib.Order.Filter.AtTopBot.Interval

/-! # Appendix A's coefficient criterion for a distributional product

The product is a relation on the actual smooth-test dual. Every coefficient
is required to be a genuine convergent convolution; totalized sums alone
do not define a product. Polynomial growth is exactly the remaining
existence condition, and the resulting original distribution is unique.
-/
noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped ENNReal
namespace NLS.Fourier
namespace SmoothPeriodicTest.Distribution
variable {L : ℝ} [Fact (0 < L)]

/-- The original distribution has the genuinely summed Fourier convolutions. -/
def HasFourierProduct (u v w : Distribution L) : Prop :=
  ∀ n : ℤ, HasSum (fun k : ℤ => u (mode (-(n-k)))*v (mode (-k))) (w (mode (-n)))

/-- A convergent Fourier product is unique on every original smooth test. -/
theorem HasFourierProduct.unique {u v w w' : Distribution L}
    (h : HasFourierProduct u v w) (h' : HasFourierProduct u v w') : w = w' := by
  apply ext_coefficients
  intro n
  exact (h n).unique (h' n)

/-- The unnumbered criterion preceding A.7: every convolution converges and
its value has polynomial growth if and only if a unique original product exists. -/
theorem exists_unique_fourierProduct_iff (u v : Distribution L) :
    (∃! w : Distribution L, HasFourierProduct u v w) ↔
      (∀ n : ℤ, Summable (fun k : ℤ => u (mode (-(n-k)))*v (mode (-k)))) ∧
      ∃ N : ℕ, Asymptotics.IsBigO cofinite
        (fun n : ℤ => ∑' k : ℤ, u (mode (-(n-k)))*v (mode (-k)))
        (fun n : ℤ => |(n:ℝ)|^N) := by
  constructor
  · rintro ⟨w,hw,_⟩
    refine ⟨fun n => (hw n).summable,w.order,?_⟩
    have he (n : ℤ) := (hw n).tsum_eq
    simpa only [he] using w.coefficients_isBigO
  · rintro ⟨hs,N,hN⟩
    obtain ⟨w,hw,_⟩ := existsUnique_of_polynomial_isBigO (L := L) _ N hN
    have hp : HasFourierProduct u v w := fun n => (hw n).symm ▸ (hs n).hasSum
    exact ⟨w,hp,fun w' hw' => hw'.unique hp⟩

/-- Construct the original product only when both source conditions hold. -/
def fourierProduct (u v : Distribution L)
    (hs : ∀ n : ℤ, Summable (fun k : ℤ => u (mode (-(n-k)))*v (mode (-k))))
    (hp : ∃ N : ℕ, Asymptotics.IsBigO cofinite
      (fun n : ℤ => ∑' k : ℤ, u (mode (-(n-k)))*v (mode (-k)))
      (fun n : ℤ => |(n:ℝ)|^N)) : Distribution L :=
  Classical.choose ((exists_unique_fourierProduct_iff u v).mpr ⟨hs,hp⟩)

theorem hasFourierProduct_fourierProduct (u v : Distribution L)
    (hs : ∀ n : ℤ, Summable (fun k : ℤ => u (mode (-(n-k)))*v (mode (-k))))
    (hp : ∃ N : ℕ, Asymptotics.IsBigO cofinite
      (fun n : ℤ => ∑' k : ℤ, u (mode (-(n-k)))*v (mode (-k)))
      (fun n : ℤ => |(n:ℝ)|^N)) : HasFourierProduct u v (fourierProduct u v hs hp) :=
  (Classical.choose_spec ((exists_unique_fourierProduct_iff u v).mpr ⟨hs,hp⟩)).1

/-- Every already constructed Young product satisfies the general original criterion. -/
theorem hasFourierProduct_youngProduct {p q r : ℝ≥0∞}
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ r)] (h : YoungRelation p q r)
    (u : PeriodicFourierLebesgue L Weight.one p)
    (v : PeriodicFourierLebesgue L Weight.one q) :
    HasFourierProduct u.val v.val (PeriodicFourierLebesgue.youngProduct h u v).val := by
  intro n
  rw [PeriodicFourierLebesgue.youngProduct_coefficient]
  exact (PeriodicFourierLebesgue.summable_norm_youngProduct_terms h u v n).of_norm.hasSum

/-- Point evaluation at zero cannot be multiplied by itself by this criterion. -/
theorem not_hasFourierProduct_evaluation_zero (w : Distribution L) :
    ¬ HasFourierProduct (evaluation (L := L) 0) (evaluation (L := L) 0) w := by
  intro h
  have hs := (h 0).summable
  simp only [evaluation_zero_coefficient,one_mul] at hs
  have hz : Tendsto (fun _ : ℤ => (1:ℂ)) cofinite (𝓝 0) := hs.tendsto_cofinite_zero
  have he : (1:ℂ) = 0 := tendsto_nhds_unique tendsto_const_nhds hz
  norm_num at he

/-- Symmetric partial sums provide the ordered interpretation of convergence. -/
def HasSymmetricFourierProduct (u v w : Distribution L) : Prop :=
  ∀ n : ℤ, Tendsto (fun M : ℕ => ∑ k ∈ Finset.Icc (-(M:ℤ)) M,
    u (mode (-(n-k)))*v (mode (-k))) atTop (𝓝 (w (mode (-n))))

theorem HasSymmetricFourierProduct.unique {u v w w' : Distribution L}
    (h : HasSymmetricFourierProduct u v w) (h' : HasSymmetricFourierProduct u v w') : w = w' := by
  apply ext_coefficients
  intro n
  exact tendsto_nhds_unique (h n) (h' n)

/-- The polynomial-growth criterion also covers convergent symmetric sums,
without adding an absolute-convergence premise. -/
theorem exists_unique_symmetricFourierProduct_iff (u v : Distribution L) :
    (∃! w : Distribution L, HasSymmetricFourierProduct u v w) ↔
      ∃ α : ℤ → ℂ,
        (∀ n : ℤ, Tendsto (fun M : ℕ => ∑ k ∈ Finset.Icc (-(M:ℤ)) M,
          u (mode (-(n-k)))*v (mode (-k))) atTop (𝓝 (α n))) ∧
        ∃ N : ℕ, Asymptotics.IsBigO cofinite α (fun n : ℤ => |(n:ℝ)|^N) := by
  constructor
  · rintro ⟨w,hw,_⟩
    exact ⟨fun n => w (mode (-n)),hw,w.order,w.coefficients_isBigO⟩
  · rintro ⟨α,hα,N,hN⟩
    obtain ⟨w,hw,_⟩ := existsUnique_of_polynomial_isBigO (L := L) α N hN
    have hp : HasSymmetricFourierProduct u v w := fun n => (hw n).symm ▸ hα n
    exact ⟨w,hp,fun w' hw' => hw'.unique hp⟩

/-- Absolutely convergent convolution and symmetric cutoffs yield the same product. -/
theorem HasFourierProduct.symmetric {u v w : Distribution L}
    (h : HasFourierProduct u v w) : HasSymmetricFourierProduct u v w :=
  fun n => (h n).comp Finset.tendsto_Icc_neg

end SmoothPeriodicTest.Distribution
end NLS.Fourier
