import NLS.ZakharovShabat.AppendixDDeletedRelativeProduct
import NLS.SequenceSpaces.CoordinateNormSup

/-! # Lemma D.8: both deleted sine-product asymptotics

Both multiplicative and additive errors have literal disc suprema in ell-p,
uniformly on every displacement norm ball. The filled sine quotient handles
the free centers; away from them it is precisely the quotient in the source.
-/
noncomputable section
open Set Metric
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- D.8's multiplicative error, defined even at the free center. -/
def sourceLemmaD8RelativeError (a : Coeff p) (n : ℤ) (z : ℂ) : ℂ :=
  appendixDRelativeProductError (0:Coeff ⊤) a n z

/-- D.8's additive error after filling the removable sine quotient. -/
def sourceLemmaD8AdditiveError (a : Coeff p) (n : ℤ) (z : ℂ) : ℂ :=
  jointDeletedSingleSpectralProduct n (z,a)-freeSineQuotient n z

/-- The multiplicative error's literal supremum on the full source disc. -/
def sourceLemmaD8RelativeSup (a : Coeff p) (n : ℤ) : ℝ :=
  sSup ((fun z => ‖sourceLemmaD8RelativeError a n z‖) '' refinedResonantDisk n)

/-- The additive error's literal supremum on the full source disc. -/
def sourceLemmaD8AdditiveSup (a : Coeff p) (n : ℤ) : ℝ :=
  sSup ((fun z => ‖sourceLemmaD8AdditiveError a n z‖) '' refinedResonantDisk n)

/-- One constant controls both actual supremum sequences throughout any displacement norm ball. -/
theorem sourceLemmaD8_uniform (hp1 : 1 < p) (hp : p ≠ ⊤) {R : ℝ} (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : Coeff p, ‖a‖ ≤ R →
      ∃ u v : Coeff p,
        (∀ n, u n = ((sourceLemmaD8RelativeSup a n):ℂ)) ∧
        (∀ n, v n = ((sourceLemmaD8AdditiveSup a n):ℂ)) ∧
        (∀ n : ℤ, ∀ z ∈ refinedResonantDisk n,
          jointDeletedSingleSpectralProduct n (z,a) = freeSineQuotient n z*(1+sourceLemmaD8RelativeError a n z) ∧
          jointDeletedSingleSpectralProduct n (z,a) = freeSineQuotient n z+sourceLemmaD8AdditiveError a n z ∧
          ‖sourceLemmaD8RelativeError a n z‖ ≤ ‖u n‖ ∧
          ‖sourceLemmaD8AdditiveError a n z‖ ≤ ‖v n‖) ∧
        ‖u‖ ≤ C*‖a‖ ∧ ‖v‖ ≤ C*‖a‖ := by
  obtain ⟨C,hC,hrelative⟩ := exists_appendixDRelativeProductSup_normBall hp1 hp
    (c := 1) (B := 0) (by norm_num) le_rfl hR
  obtain ⟨S,hS,hSbound⟩ := exists_bound_freeSineQuotient (Real.pi/4)
  refine ⟨(1+S)*C,by positivity,?_⟩
  intro a ha
  obtain ⟨b,hb,_,_,hbn⟩ := hrelative (0:Coeff ⊤) a 0 (by simp) ha appendixD_freeReferenceSeparated
  have hD (n : ℤ) : (refinedResonantDisk n).Nonempty := by
    refine ⟨(Real.pi:ℂ)*n,?_⟩
    simp only [refinedResonantDisk,mem_ball,dist_self]
    positivity
  have hrel (n : ℤ) (z : ℂ) (hz : z ∈ refinedResonantDisk n) :
      ‖sourceLemmaD8RelativeError a n z‖ ≤ ‖b n‖ := hb n (Nat.zero_le _) z hz
  have hadd (n : ℤ) (z : ℂ) (hz : z ∈ refinedResonantDisk n) :
      ‖sourceLemmaD8AdditiveError a n z‖ ≤ ‖((S:ℂ) • b) n‖ := by
    change ‖jointDeletedSingleSpectralProduct n (z,a)-freeSineQuotient n z‖ ≤ _
    rw [appendixDDeletedProduct_sub_free_eq hp1 hp a n z hz,norm_mul,
      lp.coeFn_smul,Pi.smul_apply,norm_smul,Complex.norm_real,Real.norm_of_nonneg hS]
    have hz' : ‖z-(Real.pi:ℂ)*n‖ ≤ Real.pi/4 := by
      exact (show ‖z-(Real.pi:ℂ)*n‖ < Real.pi/4 by
        simpa only [refinedResonantDisk,mem_ball,dist_eq_norm] using hz).le
    exact mul_le_mul (hSbound n z hz') (hrel n z hz) (norm_nonneg _) hS
  have hp0 : p ≠ 0 := (zero_lt_one.trans hp1).ne'
  obtain ⟨u,hu,hup,hun⟩ := exists_coordinateNormSup hp0 refinedResonantDisk hD
    (sourceLemmaD8RelativeError a) b hrel
  obtain ⟨v,hv,hvp,hvn⟩ := exists_coordinateNormSup hp0 refinedResonantDisk hD
    (sourceLemmaD8AdditiveError a) ((S:ℂ) • b) hadd
  refine ⟨u,v,hu,hv,?_,?_,?_⟩
  · intro n z hz
    exact ⟨appendixDDeletedProduct_eq_free_mul_relative hp1 hp a n z hz,
      (by unfold sourceLemmaD8AdditiveError; ring),hup n z hz,hvp n z hz⟩
  · apply (hun.trans hbn).trans
    have h : 0 ≤ S*C*‖a‖ := by positivity
    nlinarith
  · rw [norm_smul,Complex.norm_real,Real.norm_of_nonneg hS] at hvn
    apply (hvn.trans (mul_le_mul_of_nonneg_left hbn hS)).trans
    have h : 0 ≤ C*‖a‖ := by positivity
    nlinarith

/-- The two errors in the displayed asymptotics are actual ell-p sequences for arbitrary samples. -/
theorem sourceLemmaD8 (hp1 : 1 < p) (hp : p ≠ ⊤) {R : ℝ} (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : Coeff p, ‖a‖ ≤ R →
      ∀ z : ℤ → ℂ, (∀ n, z n ∈ refinedResonantDisk n) →
      ∃ e d : Coeff p,
        (∀ n : ℤ,
          jointDeletedSingleSpectralProduct n (z n,a) = freeSineQuotient n (z n)*(1+e n) ∧
          jointDeletedSingleSpectralProduct n (z n,a) = freeSineQuotient n (z n)+d n) ∧
        ‖e‖ ≤ C*‖a‖ ∧ ‖d‖ ≤ C*‖a‖ := by
  obtain ⟨C,hC,hbound⟩ := sourceLemmaD8_uniform hp1 hp hR
  refine ⟨C,hC,?_⟩
  intro a ha z hz
  obtain ⟨u,v,_,_,hpoint,hu,hv⟩ := hbound a ha
  let e : Coeff p := ⟨fun n => sourceLemmaD8RelativeError a n (z n),
    (lp.memℓp u).mono' (fun n => (hpoint n (z n) (hz n)).2.2.1)⟩
  let d : Coeff p := ⟨fun n => sourceLemmaD8AdditiveError a n (z n),
    (lp.memℓp v).mono' (fun n => (hpoint n (z n) (hz n)).2.2.2)⟩
  have hp0 : p ≠ 0 := (zero_lt_one.trans hp1).ne'
  exact ⟨e,d,(fun n => ⟨(hpoint n (z n) (hz n)).1,(hpoint n (z n) (hz n)).2.1⟩),
    (lp.norm_mono hp0 (fun n => (hpoint n (z n) (hz n)).2.2.1)).trans hu,
    (lp.norm_mono hp0 (fun n => (hpoint n (z n) (hz n)).2.2.2)).trans hv⟩

/-- The source's local uniformity follows with a single constant on a whole unit neighborhood. -/
theorem sourceLemmaD8_locally_uniform (hp1 : 1 < p) (hp : p ≠ ⊤) (a₀ : Coeff p) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : Coeff p, ‖a-a₀‖ < 1 →
      ∀ z : ℤ → ℂ, (∀ n, z n ∈ refinedResonantDisk n) →
      ∃ e d : Coeff p,
        (∀ n : ℤ,
          jointDeletedSingleSpectralProduct n (z n,a) = freeSineQuotient n (z n)*(1+e n) ∧
          jointDeletedSingleSpectralProduct n (z n,a) = freeSineQuotient n (z n)+d n) ∧
        ‖e‖ ≤ C*‖a‖ ∧ ‖d‖ ≤ C*‖a‖ := by
  obtain ⟨C,hC,hbound⟩ := sourceLemmaD8 hp1 hp (R := ‖a₀‖+1) (by positivity)
  refine ⟨C,hC,?_⟩
  intro a ha
  have hnorm : ‖a‖ ≤ ‖a₀‖+1 := by
    have h := norm_le_norm_sub_add a a₀
    linarith
  exact hbound a hnorm

/-- Away from the free center this is the sine quotient exactly as printed. -/
theorem sourceLemmaD8_off_center (hp1 : 1 < p) (hp : p ≠ ⊤)
    (a : Coeff p) (n : ℤ) (z : ℂ) (hz : z ∈ refinedResonantDisk n)
    (hne : z ≠ (Real.pi:ℂ)*n) :
    jointDeletedSingleSpectralProduct n (z,a) =
      (Complex.sin z/(z-(Real.pi:ℂ)*n))*(1+sourceLemmaD8RelativeError a n z) := by
  rw [appendixDDeletedProduct_eq_free_mul_relative hp1 hp a n z hz,
    freeSineQuotient_eq_div n z hne]
  rfl

/-- The omitted-center value uses the removable quotient's derivative, retaining its sign. -/
theorem sourceLemmaD8_center (hp1 : 1 < p) (hp : p ≠ ⊤) (a : Coeff p) (n : ℤ) :
    jointDeletedSingleSpectralProduct n ((Real.pi:ℂ)*n,a) =
      Complex.cos ((Real.pi:ℂ)*n)*(1+sourceLemmaD8RelativeError a n ((Real.pi:ℂ)*n)) := by
  have hz : (Real.pi:ℂ)*n ∈ refinedResonantDisk n := by
    simp only [refinedResonantDisk,mem_ball,dist_self]
    positivity
  rw [appendixDDeletedProduct_eq_free_mul_relative hp1 hp a n _ hz,freeSineQuotient_center]
  rfl

end NLS.ZakharovShabat
