import NLS.ZakharovShabat.SourcePsiJacobianDiagonalAsymptotic
import NLS.SequenceSpaces.FiniteExponentTail

/-!
# Uniform diagonal Jacobian tail from `ℓᵖ` coefficients

For fixed source data and one quotient majorant, the midpoint, gap,
and quotient errors all tend to zero in the two-sided index tail.
The free lattice denominator is bounded below by π independently of
the deleted index. Thus the quantitative diagonal bound gives a
uniform nonzero tail whenever its contour hypotheses hold.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Distinct lattice points have free spectral separation at least π. -/
theorem pi_le_norm_free_lattice_difference
    (n m : ℤ) (hmn : m ≠ n) :
    Real.pi ≤ ‖(Real.pi : ℂ)*((n-m : ℤ) : ℂ)‖ := by
  have hidx : (1:ℝ) ≤ |((n-m : ℤ) : ℝ)| := by
    exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr (Ne.symm hmn))
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_intCast]
  simp only [abs_of_pos Real.pi_pos]
  nlinarith [Real.pi_pos]

/-- A single two-sided cutoff makes the diagonal error estimate less
than one for every deleted index distinct from the selected index. -/
theorem exists_sourcePsi_diagonal_lp_tail_bound
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (B : Coeff p) :
    ∃ K : ℕ, ∀ m : ℤ, K ≤ m.natAbs →
      2*(‖sourcePeriodicMidpointDisplacement hp hp1 ψ m‖ +
        ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖/2) ≤ Real.pi ∧
      ∀ n : ℤ, m ≠ n →
        4*‖B m‖ +
          4*(‖sourcePeriodicMidpointDisplacement hp hp1 ψ m‖ +
            ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖/2) /
              ‖(Real.pi : ℂ)*((n-m : ℤ) : ℂ)‖ < 1 := by
  have hpr : 0 < p.toReal :=
    ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans hp1)) hp
  obtain ⟨Kb,hb⟩ := NLS.Coeff.exists_natAbs_norm_lt hpr B
    (by norm_num : (0:ℝ) < 1/8)
  obtain ⟨Km,hm⟩ := NLS.Coeff.exists_natAbs_norm_lt hpr
    (sourcePeriodicMidpointDisplacement hp hp1 ψ)
    (by positivity : (0:ℝ) < Real.pi/32)
  obtain ⟨Kg,hg⟩ := NLS.Coeff.exists_natAbs_norm_lt hpr
    (sourcePeriodicGapDisplacement hp hp1 ψ)
    (by positivity : (0:ℝ) < Real.pi/16)
  refine ⟨max Kb (max Km Kg),?_⟩
  intro m htail
  have hb' := hb m ((le_max_left _ _).trans htail)
  have hm' := hm m ((le_max_left _ _).trans
    ((le_max_right _ _).trans htail))
  have hg' := hg m ((le_max_right _ _).trans
    ((le_max_right _ _).trans htail))
  have hD :
      ‖sourcePeriodicMidpointDisplacement hp hp1 ψ m‖ +
        ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖/2 < Real.pi/16 := by
    linarith
  constructor
  · nlinarith [Real.pi_pos]
  intro n hmn
  have hsep := pi_le_norm_free_lattice_difference n m hmn
  have hsepPos : 0 < ‖(Real.pi : ℂ)*((n-m : ℤ) : ℂ)‖ := by
    linarith [Real.pi_pos]
  have hfrac :
      (‖sourcePeriodicMidpointDisplacement hp hp1 ψ m‖ +
        ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖/2) /
          ‖(Real.pi : ℂ)*((n-m : ℤ) : ℂ)‖ < 1/16 := by
    apply (div_lt_iff₀ hsepPos).2
    nlinarith [Real.pi_pos]
  calc
    4*‖B m‖ +
        4*(‖sourcePeriodicMidpointDisplacement hp hp1 ψ m‖ +
          ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖/2) /
            ‖(Real.pi : ℂ)*((n-m : ℤ) : ℂ)‖ =
      4*‖B m‖ +
        4*((‖sourcePeriodicMidpointDisplacement hp hp1 ψ m‖ +
          ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖/2) /
            ‖(Real.pi : ℂ)*((n-m : ℤ) : ℂ)‖) := by ring
    _ < 4*(1/8:ℝ) + 4*(1/16:ℝ) := by gcongr
    _ < 1 := by norm_num

/-- The diagonal majorant tends to zero in the selected index,
uniformly over every distinct deleted index. The small-gap condition
needed for the denominator estimate holds on the same tail. -/
theorem exists_sourcePsi_diagonal_lp_uniform_error_tail
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (B : Coeff p)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℕ, ∀ m : ℤ, K ≤ m.natAbs →
      2*(‖sourcePeriodicMidpointDisplacement hp hp1 ψ m‖ +
        ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖/2) ≤ Real.pi ∧
      ∀ n : ℤ, m ≠ n →
        4*‖B m‖ +
          4*(‖sourcePeriodicMidpointDisplacement hp hp1 ψ m‖ +
            ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖/2) /
              ‖(Real.pi : ℂ)*((n-m : ℤ) : ℂ)‖ < ε := by
  obtain ⟨K₀,hK₀⟩ :=
    exists_sourcePsi_diagonal_lp_tail_bound hp hp1 ψ B
  have hpr : 0 < p.toReal :=
    ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans hp1)) hp
  obtain ⟨Kb,hb⟩ := NLS.Coeff.exists_natAbs_norm_lt hpr B
    (by positivity : (0:ℝ) < ε/8)
  obtain ⟨Km,hm⟩ := NLS.Coeff.exists_natAbs_norm_lt hpr
    (sourcePeriodicMidpointDisplacement hp hp1 ψ)
    (by positivity : (0:ℝ) < ε*Real.pi/16)
  obtain ⟨Kg,hg⟩ := NLS.Coeff.exists_natAbs_norm_lt hpr
    (sourcePeriodicGapDisplacement hp hp1 ψ)
    (by positivity : (0:ℝ) < ε*Real.pi/8)
  refine ⟨max K₀ (max Kb (max Km Kg)),?_⟩
  intro m htail
  have hsmall := (hK₀ m ((le_max_left _ _).trans htail)).1
  have hb' := hb m ((le_max_left _ _).trans
    ((le_max_right _ _).trans htail))
  have hm' := hm m ((le_max_left _ _).trans
    ((le_max_right _ _).trans
      ((le_max_right _ _).trans htail)))
  have hg' := hg m ((le_max_right _ _).trans
    ((le_max_right _ _).trans
      ((le_max_right _ _).trans htail)))
  refine ⟨hsmall,?_⟩
  intro n hmn
  have hD :
      ‖sourcePeriodicMidpointDisplacement hp hp1 ψ m‖ +
        ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖/2 <
          ε*Real.pi/8 := by
    linarith
  have hsep := pi_le_norm_free_lattice_difference n m hmn
  have hsepPos : 0 < ‖(Real.pi : ℂ)*((n-m : ℤ) : ℂ)‖ := by
    linarith [Real.pi_pos]
  have hsepScaled : ε*Real.pi ≤
      ε*‖(Real.pi : ℂ)*((n-m : ℤ) : ℂ)‖ :=
    mul_le_mul_of_nonneg_left hsep hε.le
  have hfrac :
      (‖sourcePeriodicMidpointDisplacement hp hp1 ψ m‖ +
        ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖/2) /
          ‖(Real.pi : ℂ)*((n-m : ℤ) : ℂ)‖ < ε/8 := by
    apply (div_lt_iff₀ hsepPos).2
    nlinarith
  calc
    4*‖B m‖ +
        4*(‖sourcePeriodicMidpointDisplacement hp hp1 ψ m‖ +
          ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖/2) /
            ‖(Real.pi : ℂ)*((n-m : ℤ) : ℂ)‖ =
      4*‖B m‖ +
        4*((‖sourcePeriodicMidpointDisplacement hp hp1 ψ m‖ +
          ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖/2) /
            ‖(Real.pi : ℂ)*((n-m : ℤ) : ℂ)‖) := by ring
    _ < 4*(ε/8) + 4*(ε/8) := by gcongr
    _ = ε := by ring

/-- Any family of diagonal entries satisfying the spectral majorant
converges to two uniformly in the deleted index. -/
theorem sourcePsi_diagonal_uniform_tends_to_two_of_lp_bound
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (B : Coeff p) (Q : ℤ → ℤ → ℂ)
    (hQ : ∀ n m : ℤ, m ≠ n →
      ‖Q n m-2‖ ≤
        4*‖B m‖ +
          4*(‖sourcePeriodicMidpointDisplacement hp hp1 ψ m‖ +
            ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖/2) /
              ‖(Real.pi : ℂ)*((n-m : ℤ) : ℂ)‖) :
    ∀ ε : ℝ, 0 < ε → ∃ K : ℕ,
      ∀ m : ℤ, K ≤ m.natAbs → ∀ n : ℤ, m ≠ n →
        ‖Q n m-2‖ < ε := by
  intro ε hε
  obtain ⟨K,hK⟩ :=
    exists_sourcePsi_diagonal_lp_uniform_error_tail hp hp1 ψ B ε hε
  refine ⟨K,?_⟩
  intro m hm n hmn
  exact (hQ n m hmn).trans_lt ((hK m hm).2 n hmn)

/-- Uniform convergence to two gives a common nonzero tail for all
deleted indices. -/
theorem exists_sourcePsi_diagonal_uniform_nonzero_tail_of_lp_bound
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (B : Coeff p) (Q : ℤ → ℤ → ℂ)
    (hQ : ∀ n m : ℤ, m ≠ n →
      ‖Q n m-2‖ ≤
        4*‖B m‖ +
          4*(‖sourcePeriodicMidpointDisplacement hp hp1 ψ m‖ +
            ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖/2) /
              ‖(Real.pi : ℂ)*((n-m : ℤ) : ℂ)‖) :
    ∃ K : ℕ, ∀ m : ℤ, K ≤ m.natAbs →
      ∀ n : ℤ, m ≠ n → Q n m ≠ 0 := by
  obtain ⟨K,hK⟩ :=
    sourcePsi_diagonal_uniform_tends_to_two_of_lp_bound
      hp hp1 ψ B Q hQ 1 (by norm_num)
  refine ⟨K,?_⟩
  intro m hm n hmn hzero
  have h := hK m hm n hmn
  rw [hzero] at h
  norm_num at h

end NLS.ZakharovShabat
