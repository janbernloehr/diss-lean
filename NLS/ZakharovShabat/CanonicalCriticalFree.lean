import NLS.ZakharovShabat.UniformCanonicalCriticalPoints

/-!
# The canonical critical coordinates at zero potential

The free centers form a valid ordered complete labeling already at cutoff
zero. Uniqueness therefore fixes every canonical coordinate to pi times
its signed index, with exactly zero displacement.
-/

noncomputable section
open Set Complex Metric
open NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- At zero potential the literal free centers form a complete critical labeling with cutoff zero. -/
theorem criticalPointLabeling_free (hp : p ≠ ⊤) (hp1 : 1 < p) :
    CriticalPointLabeling hp hp1 0 (pairParitySubspace 0).zero_mem 0 (fun n => (Real.pi : ℂ)*n) := by
  have hf : deriv (canonicalDiscriminant (p := p) hp 0) = fun z => -2*sin z :=
    funext (discriminant_derivative_zero hp)
  have hs (n : ℤ) : -2*sin ((Real.pi : ℂ)*n) = 0 := by
    rw [mul_comm (Real.pi : ℂ), Complex.sin_int_mul_pi, mul_zero]
  have hc : centralCriticalRoots hp hp1 0 (pairParitySubspace 0).zero_mem 0 = {0} := by
    have hcard : (centralCriticalRoots hp hp1 0 (pairParitySubspace 0).zero_mem 0).card = 1 := by
      rw [card_centralCriticalRoots, hf]
      exact analyticZeroCount_free_derivative_central 0
    obtain ⟨a,ha⟩ := Multiset.card_eq_one.mp hcard
    have hm : a ∈ centralCriticalRoots hp hp1 0 (pairParitySubspace 0).zero_mem 0 := by rw [ha]; simp
    obtain ⟨hab,haz⟩ := (mem_centralCriticalRoots hp hp1 0 (pairParitySubspace 0).zero_mem 0 a).mp hm
    rw [hf] at haz
    have ha0 := free_derivative_zero_eq_center
      (show centralCircleRadius 0 < Real.pi by unfold centralCircleRadius; simp; linarith [Real.pi_pos])
      0 (by simpa using hab) haz
    simpa only [Int.cast_zero, mul_zero, ha0] using ha
  refine ⟨?_,?_,?_⟩
  · simpa only [Int.natCast_zero, neg_zero, Finset.Icc_self, Finset.sum_singleton,
      Int.cast_zero, mul_zero] using hc.symm
  · intro n _
    refine ⟨mem_ball_self (by positivity),?_,?_,?_⟩
    · rw [hf]
      exact hs n
    · rw [hf]
      exact analyticOrderAt_free_derivative n
    · intro z hz
      rw [hf]
      exact ⟨fun hzero => free_derivative_zero_eq_center (by linarith [Real.pi_pos]) n hz hzero,
        fun he => he ▸ hs n⟩
  · intro z
    rw [hf]
    constructor
    · intro hz
      have hs0 : sin z = 0 := (mul_eq_zero.mp hz).resolve_left (by norm_num)
      obtain ⟨n,hn⟩ := Complex.sin_eq_zero_iff.mp hs0
      exact ⟨n,by simpa only [mul_comm] using hn.symm⟩
    · rintro ⟨n,rfl⟩
      exact hs n

/-- Every signed canonical critical coordinate is exactly its free lattice center at zero potential. -/
theorem canonicalCriticalPoints_zero (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) :
    canonicalCriticalPoints hp hp1 0 (pairParitySubspace 0).zero_mem n = (Real.pi : ℂ)*n := by
  have hm : Monotone (fun n : ℤ => complexLexKey ((Real.pi : ℂ)*n)) := by
    intro i j hij
    have he (k : ℤ) : (Real.pi : ℂ)*k = ((Real.pi*(k : ℝ) : ℝ) : ℂ) := by simp
    change complexLexLE ((Real.pi : ℂ)*i) ((Real.pi : ℂ)*j)
    rw [he i,he j,complexLexLE_ofReal_iff]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hij) Real.pi_pos.le
  exact (congrFun ((criticalPointLabeling_free hp hp1).eq_canonicalCriticalPoints hm) n).symm

/-- The canonical displacement coefficient is identically zero at zero potential. -/
@[simp] theorem canonicalCriticalDisplacement_zero (hp : p ≠ ⊤) (hp1 : 1 < p) :
    canonicalCriticalDisplacement hp hp1 0 (pairParitySubspace 0).zero_mem = 0 := by
  ext n
  simp only [canonicalCriticalDisplacement_apply, canonicalCriticalPoints_zero, sub_self, lp.coeFn_zero, Pi.zero_apply]

end NLS.ZakharovShabat
