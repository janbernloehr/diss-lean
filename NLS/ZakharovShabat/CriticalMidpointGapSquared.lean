import NLS.ZakharovShabat.CriticalOffsetCoefficientLowerBound

/-!
# Lemma 8.6: the squared-gap improvement of critical-point asymptotics

On one open convex neighborhood of each potential, the actual offset from
the gap midpoint equals the squared gap times an lp coefficient sequence
with a common norm bound at every sufficiently large signed index. No gap
is divided by, so the conclusion includes collapsed gaps.
-/

noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual derivative quotient in the squared-gap critical-point formula.
Only sufficiently distant coefficients are asserted to have nonzero denominators. -/
def canonicalCriticalGapQuotient (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p)
    (heven : φ ∈ pairParitySubspace 0) (n : ℤ) : ℂ :=
  canonicalDeletedCriticalDerivative hp hp1 φ heven n/(4*canonicalCriticalOffsetCoefficient hp hp1 φ heven n)

/-- The uniform coefficient lower bound controls the quotient without dividing by a gap. -/
theorem norm_canonicalCriticalGapQuotient_le (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p)
    (heven : φ ∈ pairParitySubspace 0) (n : ℤ)
    (h : 1 ≤ ‖canonicalCriticalOffsetCoefficient hp hp1 φ heven n‖) :
    ‖canonicalCriticalGapQuotient hp hp1 φ heven n‖ ≤ ‖canonicalDeletedCriticalDerivative hp hp1 φ heven n‖/4 := by
  rw [canonicalCriticalGapQuotient,norm_div,norm_mul,Complex.norm_ofNat]
  exact div_le_div_of_nonneg_left (norm_nonneg _) (by norm_num) (by linarith)

/-- Locally uniform bounded lp representatives for the squared-gap quotient and exact offset identity. -/
theorem exists_uniform_critical_midpoint_gap_sq_lp (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p) :
    ∃ N : ℕ, 0 < N ∧ ∃ U : Set (PairSpace p), IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∃ K : ℝ, 0 ≤ K ∧ ∀ ψ ∈ U, ∀ heven : ψ ∈ pairParitySubspace 0,
        ∃ a : Coeff p, ‖a‖ ≤ K ∧ ∀ n : ℤ, N < n.natAbs →
          a n = canonicalCriticalGapQuotient hp hp1 ψ heven n ∧
          canonicalCriticalMidpointOffset hp hp1 ψ heven n = (canonicalPeriodicGap hp hp1 ψ heven n)^2*a n := by
  obtain ⟨N,hN,V,hvo,hvc,hvφ,hv0,hlower⟩ := exists_uniform_criticalOffsetCoefficient_lower_bound hp hp1 φ
  obtain ⟨M,_,W,hwo,hwc,hwφ,hw0,S,hS,hvalues⟩ := exists_uniform_deletedProduct_critical_coefficients hp hp1 φ
  refine ⟨max N M,lt_of_lt_of_le hN (le_max_left _ _),V ∩ W,hvo.inter hwo,hvc.inter hwc,
    ⟨hvφ,hwφ⟩,⟨hv0,hw0⟩,S/4,by positivity,fun ψ hψ heven => ?_⟩
  obtain ⟨_,b,_,hb,hab⟩ := hvalues ψ hψ.2 heven
  let f : ℤ → ℂ := fun n => if max N M < n.natAbs then canonicalCriticalGapQuotient hp hp1 ψ heven n else 0
  have hdom (n : ℤ) : ‖f n‖ ≤ ‖((1/4 : ℂ) • b) n‖ := by
    simp only [lp.coeFn_smul,Pi.smul_apply,norm_smul,norm_div,norm_one,Complex.norm_ofNat]
    by_cases hn : max N M < n.natAbs
    · simp only [f,if_pos hn]
      rw [(hab n (lt_of_le_of_lt (le_max_right _ _) hn)).2]
      simpa only [div_eq_mul_inv,one_mul,mul_comm] using norm_canonicalCriticalGapQuotient_le hp hp1 ψ heven n
        (hlower ψ hψ.1 heven n (lt_of_le_of_lt (le_max_left _ _) hn))
    · simp only [f,if_neg hn,norm_zero]
      positivity
  let a : Coeff p := ⟨f,(lp.memℓp ((1/4 : ℂ) • b)).mono' hdom⟩
  refine ⟨a,(lp.norm_mono (zero_lt_one.trans hp1).ne' hdom).trans ?_,fun n hn => ?_⟩
  · rw [norm_smul]
    norm_num only [norm_div,norm_one,Complex.norm_ofNat]
    simpa only [div_eq_mul_inv,one_mul,mul_comm] using mul_le_mul_of_nonneg_left hb (by norm_num : (0 : ℝ) ≤ 1/4)
  · have ha : a n = canonicalCriticalGapQuotient hp hp1 ψ heven n := by
      change f n = _
      simp only [f,if_pos hn]
    refine ⟨ha,?_⟩
    rw [ha]
    have hB := hlower ψ hψ.1 heven n (lt_of_le_of_lt (le_max_left _ _) hn)
    exact canonicalCriticalMidpointOffset_eq_gap_sq_mul_quotient hp hp1 ψ heven n
      (norm_pos_iff.mp (lt_of_lt_of_le zero_lt_one hB))

/-- The full actual quotient sequence belongs to lp at each fixed even potential. -/
theorem memℓp_canonicalCriticalGapQuotient (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p)
    (heven : φ ∈ pairParitySubspace 0) : Memℓp (canonicalCriticalGapQuotient hp hp1 φ heven) p := by
  obtain ⟨N,_,_,_,_,hφ,_,_,_,h⟩ := exists_uniform_critical_midpoint_gap_sq_lp hp hp1 φ
  obtain ⟨a,_,ha⟩ := h φ hφ heven
  apply NLS.memℓp_of_eq_outside_finset (lp.memℓp a) (Finset.Icc (-(N : ℤ)) N)
  intro n hn
  exact ((ha n (by simp only [Finset.mem_Icc] at hn; omega)).1).symm

/-- Lemma 8.6: the canonical critical-point midpoint offset is the squared gap times a locally bounded lp tail. -/
theorem exists_uniform_canonicalCriticalPoints_midpoint_gap_sq (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p) :
    ∃ N : ℕ, 0 < N ∧ ∃ U : Set (PairSpace p), IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∃ K : ℝ, 0 ≤ K ∧ ∀ ψ ∈ U, ∀ heven : ψ ∈ pairParitySubspace 0,
        ∃ a : Coeff p, ‖a‖ ≤ K ∧ ∀ n : ℤ, N < n.natAbs →
          canonicalCriticalPoints hp hp1 ψ heven n-canonicalPeriodicMidpoint hp hp1 ψ heven n =
            (canonicalPeriodicGap hp hp1 ψ heven n)^2*a n := by
  obtain ⟨N,hN,U,ho,hc,hφ,h0,K,hK,h⟩ := exists_uniform_critical_midpoint_gap_sq_lp hp hp1 φ
  refine ⟨N,hN,U,ho,hc,hφ,h0,K,hK,fun ψ hψ heven => ?_⟩
  obtain ⟨a,ha,he⟩ := h ψ hψ heven
  exact ⟨a,ha,fun n hn => by simpa only [canonicalCriticalMidpointOffset_apply] using (he n hn).2⟩

end NLS.ZakharovShabat
