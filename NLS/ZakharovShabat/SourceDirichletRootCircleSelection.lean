import NLS.ZakharovShabat.SourceBoundaryDisplacementAnalytic
import NLS.SequenceSpaces.FiniteExponentTail

/-! # Exact Dirichlet root selection by large circles

Vanishing displacement tails and a bound for the finite central block
show that the half-integer-radius circle encloses exactly the symmetric
cutoff of the actual boundary-root sequence. This works at complex
sources as well as real sources.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Large half-integer circles select exactly the symmetric index block
of every finite-exponent displaced lattice. -/
theorem eventually_displacedRoots_mem_centralBall_iff (hp : p ≠ ⊤) (a : Coeff p) :
    ∃ K : ℕ, ∀ N : ℕ, K ≤ N → ∀ m : ℤ,
      ‖displacedRoots a m‖ < centralCircleRadius N ↔ m.natAbs ≤ N := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le Fact.out).ne'
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  obtain ⟨K₀,hK₀⟩ := Coeff.exists_natAbs_norm_lt hpr a
    (by positivity : 0 < Real.pi/4)
  obtain ⟨K₁,hK₁⟩ := exists_nat_gt ((Real.pi*K₀+‖a‖)/Real.pi)
  refine ⟨max K₀ K₁,?_⟩
  intro N hN m
  have hnorm : ‖(Real.pi : ℂ)*m‖ = Real.pi*(m.natAbs : ℝ) := by
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos,
      Complex.norm_intCast,Nat.cast_natAbs,Int.cast_abs]
  have hhead : Real.pi*K₀+‖a‖ < centralCircleRadius N := by
    have hK₁ : Real.pi*K₀+‖a‖ < (K₁ : ℝ)*Real.pi :=
      (div_lt_iff₀ Real.pi_pos).mp (by exact_mod_cast hK₁)
    have hK₁N : (K₁ : ℝ) ≤ (N : ℝ) := by exact_mod_cast ((le_max_right K₀ K₁).trans hN)
    unfold centralCircleRadius
    nlinarith [Real.pi_pos]
  have hupper : ‖displacedRoots a m‖ ≤ Real.pi*(m.natAbs : ℝ)+‖a m‖ := by
    dsimp only [displacedRoots]
    simpa only [hnorm] using norm_add_le ((Real.pi : ℂ)*m) (a m)
  have hlower : Real.pi*(m.natAbs : ℝ) ≤ ‖displacedRoots a m‖+‖a m‖ := by
    have h := norm_sub_le (displacedRoots a m) (a m)
    simp only [displacedRoots,add_sub_cancel_right,hnorm] at h
    exact h
  constructor
  · intro hm
    by_contra hnot
    have hmN : (N : ℝ)+1 ≤ (m.natAbs : ℝ) := by exact_mod_cast (show N+1 ≤ m.natAbs by omega)
    have htail := hK₀ m (by omega)
    unfold centralCircleRadius at hm
    nlinarith [Real.pi_pos]
  · intro hm
    by_cases hsmall : m.natAbs < K₀
    · have hmK : (m.natAbs : ℝ) ≤ (K₀ : ℝ) := by exact_mod_cast hsmall.le
      have hcoord := lp.norm_apply_le_norm hp0 a m
      nlinarith [Real.pi_pos]
    · have htail := hK₀ m (by omega)
      have hmN : (m.natAbs : ℝ) ≤ (N : ℝ) := by exact_mod_cast hm
      unfold centralCircleRadius
      nlinarith [Real.pi_pos]

/-- The actual Dirichlet sequence has the exact symmetric circle
selection needed for Cauchy interpolation, at every complex source. -/
theorem eventually_canonicalDirichletRoots_mem_centralBall_iff
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) :
    ∃ K : ℕ, ∀ N : ℕ, K ≤ N → ∀ m : ℤ,
      ‖canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ m‖ < centralCircleRadius N ↔ m.natAbs ≤ N := by
  have he (m : ℤ) : displacedRoots (sourceBoundaryDisplacement hp hp1 .dirichlet φ) m =
      canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ m := by
    simp only [displacedRoots,sourceBoundaryDisplacement_apply]
    ring
  simpa only [he] using eventually_displacedRoots_mem_centralBall_iff hp
    (sourceBoundaryDisplacement hp hp1 .dirichlet φ)

end NLS.ZakharovShabat
