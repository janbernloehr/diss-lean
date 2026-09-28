import NLS.ZakharovShabat.SourcePsiJacobianOffDiagonalMeanValue

/-!
# Root-ratio geometry for off-diagonal psi Jacobian entries

The extra numerator in an off-diagonal entry is small because the
selected root and the point supplied by the gap mean-value theorem
are both close to the same free lattice center. A root in a different
quarter-π disc stays a fixed fraction of the lattice distance away.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The distance from the selected root to any point of its standard
gap is controlled by three `ℓᵖ` displacement coordinates. -/
theorem norm_displacedRoot_sub_standardGapPoint_le
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (a : Coeff p) (ψ : CoeffPair p) (m : ℤ) (μ : ℂ)
    (hμ : μ ∈ standardRootGapSegment
      (sourceStandardRootMidpoint hp hp1 ψ m)
      (sourceStandardRootHalfGap hp hp1 ψ m)) :
    ‖displacedRoots a m-μ‖ ≤
      ‖a m‖ + ‖sourcePeriodicMidpointDisplacement hp hp1 ψ m‖ +
        ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖/2 := by
  have hgap := norm_sourceStandardRoot_gapPoint_sub_free_le
    hp hp1 ψ m μ hμ
  have heq : displacedRoots a m-μ =
      a m-(μ-(Real.pi : ℂ)*m) := by
    simp [displacedRoots]
    ring
  rw [heq]
  linarith [norm_sub_le (a m) (μ-(Real.pi : ℂ)*m)]

/-- When the varied root and the selected gap point lie within
quarter-π of their respective free centers, their separation is at
least half the free lattice distance. -/
theorem half_pi_lattice_separation_le_root_sub_gapPoint
    {p : ℝ≥0∞} (a : Coeff p)
    (m k : ℤ) (hmk : m ≠ k) (μ : ℂ)
    (hroot : ‖a k‖ ≤ Real.pi/4)
    (hgap : ‖μ-(Real.pi : ℂ)*m‖ ≤ Real.pi/4) :
    (Real.pi/2)*‖((m-k : ℤ) : ℂ)‖ ≤
      ‖displacedRoots a k-μ‖ := by
  have hsplit : (Real.pi : ℂ)*((k-m : ℤ) : ℂ) =
      (displacedRoots a k-μ)-a k+(μ-(Real.pi : ℂ)*m) := by
    simp [displacedRoots]
    ring
  have htri : ‖(Real.pi : ℂ)*((k-m : ℤ) : ℂ)‖ ≤
      ‖displacedRoots a k-μ‖+‖a k‖+
        ‖μ-(Real.pi : ℂ)*m‖ := by
    rw [hsplit]
    have h₁ := norm_sub_le (displacedRoots a k-μ) (a k)
    have h₂ := norm_add_le ((displacedRoots a k-μ)-a k)
      (μ-(Real.pi : ℂ)*m)
    linarith
  have hnorm : ‖(Real.pi : ℂ)*((k-m : ℤ) : ℂ)‖ =
      Real.pi*‖((m-k : ℤ) : ℂ)‖ := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
    have heq : (((k-m : ℤ) : ℂ)) = -(((m-k : ℤ) : ℂ)) := by
      push_cast
      ring
    rw [heq,norm_neg]
  have hidx : (1:ℝ) ≤ ‖((m-k : ℤ) : ℂ)‖ := by
    have h : (1:ℤ) ≤ |m-k| := Int.one_le_abs (sub_ne_zero.mpr hmk)
    exact_mod_cast h
  rw [hnorm] at htri
  nlinarith [Real.pi_pos]

/-- On a small selected gap, the off-diagonal root ratio has an
`ℓᵖ` numerator and inverse lattice-distance denominator. -/
theorem norm_offDiagonal_rootRatio_le
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (a : Coeff p) (ψ : CoeffPair p)
    (m k : ℤ) (hmk : m ≠ k) (μ : ℂ)
    (hμ : μ ∈ standardRootGapSegment
      (sourceStandardRootMidpoint hp hp1 ψ m)
      (sourceStandardRootHalfGap hp hp1 ψ m))
    (hroot : ‖a k‖ ≤ Real.pi/4)
    (hgap : ‖μ-(Real.pi : ℂ)*m‖ ≤ Real.pi/4) :
    ‖(displacedRoots a m-μ)/(displacedRoots a k-μ)‖ ≤
      (‖a m‖ + ‖sourcePeriodicMidpointDisplacement hp hp1 ψ m‖ +
        ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖/2) /
          ((Real.pi/2)*‖((m-k : ℤ) : ℂ)‖) := by
  have hnum := norm_displacedRoot_sub_standardGapPoint_le
    hp hp1 a ψ m μ hμ
  have hsep := half_pi_lattice_separation_le_root_sub_gapPoint
    a m k hmk μ hroot hgap
  have hidx : (((m-k : ℤ) : ℂ)) ≠ 0 := by
    exact_mod_cast sub_ne_zero.mpr hmk
  have hdenPos : 0 < (Real.pi/2)*‖((m-k : ℤ) : ℂ)‖ :=
    mul_pos (by positivity) (norm_pos_iff.mpr hidx)
  rw [norm_div]
  exact (div_le_div_of_nonneg_right hnum (norm_nonneg _)).trans
    (div_le_div_of_nonneg_left
      (by positivity) hdenPos hsep)

/-- The pointwise ratio estimate follows from a quarter-π bound on
the selected source gap's midpoint and width coefficients. -/
theorem norm_offDiagonal_rootRatio_le_of_smallGapDisplacements
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (a : Coeff p) (ψ : CoeffPair p)
    (m k : ℤ) (hmk : m ≠ k) (μ : ℂ)
    (hμ : μ ∈ standardRootGapSegment
      (sourceStandardRootMidpoint hp hp1 ψ m)
      (sourceStandardRootHalfGap hp hp1 ψ m))
    (hroot : ‖a k‖ ≤ Real.pi/4)
    (hsmall : ‖sourcePeriodicMidpointDisplacement hp hp1 ψ m‖ +
      ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖/2 ≤ Real.pi/4) :
    ‖(displacedRoots a m-μ)/(displacedRoots a k-μ)‖ ≤
      (‖a m‖ + ‖sourcePeriodicMidpointDisplacement hp hp1 ψ m‖ +
        ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖/2) /
          ((Real.pi/2)*‖((m-k : ℤ) : ℂ)‖) := by
  exact norm_offDiagonal_rootRatio_le hp hp1 a ψ m k hmk μ hμ
    hroot ((norm_sourceStandardRoot_gapPoint_sub_free_le
      hp hp1 ψ m μ hμ).trans hsmall)

end NLS.ZakharovShabat
