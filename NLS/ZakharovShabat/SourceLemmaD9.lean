import NLS.ZakharovShabat.SourceLemmaD8
import NLS.ZakharovShabat.BoundaryCharacteristicDiscLp

/-! # Lemma D.9: the full sine-product error at arbitrary disc samples

The literal negative product has the same normalization as the entire
boundary product. Its disc majorants give actual supremum and sampled
error sequences, with one bound on every displacement norm ball.
-/
noncomputable section
open Set Metric
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

omit [Fact (1 ≤ p)] in
/-- The Appendix D product is exactly the normalized entire boundary product. -/
theorem appendixDProduct_eq_displacedBoundaryProduct (a : Coeff p) (z : ℂ) :
    appendixDProduct (z,a) = displacedBoundaryProduct a z := by
  unfold appendixDProduct jointSingleSpectralProduct displacedBoundaryProduct boundaryCharacteristicProduct
  change -(1/2:ℂ)*entireSingleSpectralProduct (displacedRoots a) z =
    (-1/2:ℂ)*entireSingleSpectralProduct (displacedRoots a) z
  ring

/-- Restoring D.8's omitted factor gives exactly the error identity used in D.9's proof. -/
theorem appendixDProduct_sub_sin_eq_relative_error (hp1 : 1 < p) (hp : p ≠ ⊤)
    (a : Coeff p) (n : ℤ) (z : ℂ) (hz : z ∈ refinedResonantDisk n) :
    appendixDProduct (z,a)-Complex.sin z =
      -freeSineQuotient n z*(a n+(displacedRoots a n-z)*sourceLemmaD8RelativeError a n z) := by
  rw [appendixDProduct_eq_deleted hp n,appendixDDeletedProduct,
    appendixDDeletedProduct_eq_free_mul_relative hp1 hp a n z hz]
  rw [← freeSineQuotient_mul_sub n z]
  unfold sourceLemmaD8RelativeError displacedRoots
  field_simp
  ring

/-- The actual supremum of the full-product error on a source disc. -/
def sourceLemmaD9Sup (a : Coeff p) (n : ℤ) : ℝ :=
  sSup ((fun z => ‖appendixDProduct (z,a)-Complex.sin z‖) '' refinedResonantDisk n)

/-- D.9's error suprema lie in ell-p, uniformly on each displacement norm ball. -/
theorem sourceLemmaD9_uniform (hp1 : 1 < p) (hp : p ≠ ⊤) {R : ℝ} (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : Coeff p, ‖a‖ ≤ R →
      ∃ b : Coeff p,
        (∀ n, b n = ((sourceLemmaD9Sup a n):ℂ)) ∧
        (∀ n : ℤ, ∀ z ∈ refinedResonantDisk n,
          ‖appendixDProduct (z,a)-Complex.sin z‖ ≤ ‖b n‖) ∧ ‖b‖ ≤ C := by
  obtain ⟨K,hK,hbound⟩ := exists_uniform_displacedBoundaryProduct_majorants hp1 hp hR
  refine ⟨K+1,by linarith,?_⟩
  intro a ha
  obtain ⟨A,hA,hvalue,_⟩ := hbound a ha
  have hD (n : ℤ) : (refinedResonantDisk n).Nonempty := by
    refine ⟨(Real.pi:ℂ)*n,?_⟩
    simp only [refinedResonantDisk,mem_ball,dist_self]
    positivity
  have hmajor (n : ℤ) (z : ℂ) (hz : z ∈ refinedResonantDisk n) :
      ‖appendixDProduct (z,a)-Complex.sin z‖ ≤ ‖A n‖ := by
    rw [appendixDProduct_eq_displacedBoundaryProduct]
    apply hvalue n z
    have hz' : ‖z-(Real.pi:ℂ)*n‖ < Real.pi/4 := by
      simpa only [refinedResonantDisk,mem_ball,dist_eq_norm] using hz
    linarith [Real.pi_pos]
  obtain ⟨b,hb,hbp,hbn⟩ := exists_coordinateNormSup (zero_lt_one.trans hp1).ne'
    refinedResonantDisk hD (fun n z => appendixDProduct (z,a)-Complex.sin z) A hmajor
  exact ⟨b,hb,hbp,by linarith⟩

/-- The literal D.9 sampled asymptotic, with one norm bound for every independent sampling sequence. -/
theorem sourceLemmaD9 (hp1 : 1 < p) (hp : p ≠ ⊤) {R : ℝ} (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : Coeff p, ‖a‖ ≤ R →
      ∀ z : ℤ → ℂ, (∀ n, z n ∈ refinedResonantDisk n) →
      ∃ e : Coeff p,
        (∀ n : ℤ, appendixDProduct (z n,a) = Complex.sin (z n)+e n) ∧ ‖e‖ ≤ C := by
  obtain ⟨C,hC,hbound⟩ := sourceLemmaD9_uniform hp1 hp hR
  refine ⟨C,hC,?_⟩
  intro a ha z hz
  obtain ⟨b,_,hb,hbn⟩ := hbound a ha
  let e : Coeff p := ⟨fun n => appendixDProduct (z n,a)-Complex.sin (z n),
    (lp.memℓp b).mono' (fun n => hb n (z n) (hz n))⟩
  refine ⟨e,?_,(lp.norm_mono (zero_lt_one.trans hp1).ne' (fun n => hb n (z n) (hz n))).trans hbn⟩
  intro n
  change appendixDProduct (z n,a) = Complex.sin (z n)+(appendixDProduct (z n,a)-Complex.sin (z n))
  ring

/-- Direct membership of the source's actual sampled error function. -/
theorem sourceLemmaD9_mem (hp1 : 1 < p) (hp : p ≠ ⊤) (a : Coeff p)
    (z : ℤ → ℂ) (hz : ∀ n, z n ∈ refinedResonantDisk n) :
    Memℓp (fun n => appendixDProduct (z n,a)-Complex.sin (z n)) p := by
  obtain ⟨_,_,hbound⟩ := sourceLemmaD9 hp1 hp (norm_nonneg a)
  obtain ⟨e,he,_⟩ := hbound a le_rfl z hz
  have heq : (fun n => appendixDProduct (z n,a)-Complex.sin (z n)) = ⇑e := by
    funext n
    rw [he n]
    ring
  rw [heq]
  exact lp.memℓp e

/-- The same conclusion for a function specified by the literal negative-product cutoffs. -/
theorem sourceLemmaD9_of_cutoff_limits (hp1 : 1 < p) (hp : p ≠ ⊤)
    (a : Coeff p) (f : ℂ → ℂ)
    (hf : ∀ w : ℂ, Filter.Tendsto (fun M : ℕ =>
      -∏ m ∈ Finset.Icc (-(M:ℤ)) (M:ℤ),
        (displacedRoots a m-w)/singleSpectralDenominator m)
      Filter.atTop (nhds (f w)))
    (z : ℤ → ℂ) (hz : ∀ n, z n ∈ refinedResonantDisk n) :
    Memℓp (fun n => f (z n)-Complex.sin (z n)) p := by
  have he (w : ℂ) : f w = appendixDProduct (w,a) :=
    tendsto_nhds_unique (hf w) (tendsto_appendixDProduct hp (w,a))
  simpa only [he] using sourceLemmaD9_mem hp1 hp a z hz

/-- A single constant works throughout a neighborhood of every displacement, as required in D.9. -/
theorem sourceLemmaD9_locally_uniform (hp1 : 1 < p) (hp : p ≠ ⊤) (a₀ : Coeff p) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : Coeff p, ‖a-a₀‖ < 1 →
      ∀ z : ℤ → ℂ, (∀ n, z n ∈ refinedResonantDisk n) →
      ∃ e : Coeff p,
        (∀ n : ℤ, appendixDProduct (z n,a) = Complex.sin (z n)+e n) ∧ ‖e‖ ≤ C := by
  obtain ⟨C,hC,hbound⟩ := sourceLemmaD9 hp1 hp (R := ‖a₀‖+1) (by positivity)
  refine ⟨C,hC,?_⟩
  intro a ha
  have hnorm : ‖a‖ ≤ ‖a₀‖+1 := by
    have h := norm_le_norm_sub_add a a₀
    linarith
  exact hbound a hnorm

end NLS.ZakharovShabat
