import NLS.ZakharovShabat.SourceClusterDiscsLocal
import NLS.ZakharovShabat.SourceTailIsolation

/-!
# Separation between central and distant source discs

The outer central periodic endpoints bound the real extent of every
central midpoint disc. When these endpoints are in their free quarter-π
discs, a central margin at most π/4 leaves room before every tail disc.
-/

noncomputable section
open Set Metric Complex
open NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Any point in a free quarter-π disc lies in its closed real strip. -/
private theorem refinedDisk_re_strip {n : ℤ} {z : ℂ}
    (hz : z ∈ refinedResonantDisk n) :
    |z.re - Real.pi * n| ≤ Real.pi / 2 :=
  refinedResonantDisk_subset_strip n hz

/-- The right endpoint at a later real-type gap bounds every earlier
right endpoint. -/
private theorem source_right_le_right_of_le
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    {i j : ℤ} (hij : i ≤ j) :
    (canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) i).re ≤
      (canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) j).re := by
  rcases hij.lt_or_eq with hij | rfl
  · have hgap := canonicalPeriodicRight_re_lt_left_of_lt hp hp1
      (periodOnePotential φ) (periodOnePotential_mem φ)
      (isRealType_periodOnePotential φ hφ) hij
    have hwithin := re_le_of_complexLexLE
      ((canonicalPeriodicEndpoints_spec hp hp1 (periodOnePotential φ)
        (periodOnePotential_mem φ)).2.1 j)
    exact hgap.le.trans hwithin
  · rfl

/-- The left endpoint at an earlier real-type gap bounds every later
left endpoint. -/
private theorem source_left_le_left_of_le
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    {i j : ℤ} (hij : i ≤ j) :
    (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) i).re ≤
      (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) j).re := by
  rcases hij.lt_or_eq with hij | rfl
  · have hwithin := re_le_of_complexLexLE
      ((canonicalPeriodicEndpoints_spec hp hp1 (periodOnePotential φ)
        (periodOnePotential_mem φ)).2.1 i)
    have hgap := canonicalPeriodicRight_re_lt_left_of_lt hp hp1
      (periodOnePotential φ) (periodOnePotential_mem φ)
      (isRealType_periodOnePotential φ hφ) hij
    exact hwithin.trans hgap.le
  · rfl

/-- A central midpoint disc is disjoint from every positive tail free disc
once the outer right endpoint is localized and the margin is at most π/4. -/
theorem sourceClusterDisc_disjoint_positive_tail
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (N : ℕ) (ε : ℝ) (hε : 0 ≤ ε) (hεmax : ε ≤ Real.pi/4)
    (houter : canonicalPeriodicRight hp hp1 (periodOnePotential φ)
      (periodOnePotential_mem φ) (N : ℤ) ∈ refinedResonantDisk (N : ℤ))
    {i j : ℤ} (hi : i ≤ (N : ℤ)) (hj : (N : ℤ) < j) :
    Disjoint (sourceClusterDisc hp hp1 φ (fun _ => ε) i)
      (refinedResonantDisk j) := by
  have hwithin := re_le_of_complexLexLE
    ((canonicalPeriodicEndpoints_spec hp hp1 (periodOnePotential φ)
      (periodOnePotential_mem φ)).2.1 i)
  have hRi := source_right_le_right_of_le hp hp1 φ hφ hi
  have hRN := (abs_le.mp (refinedDisk_re_strip houter)).2
  have hjreal : ((N : ℤ) : ℝ) + 1 ≤ (j : ℝ) := by
    exact_mod_cast (show (N : ℤ) + 1 ≤ j by omega)
  have hmul := mul_le_mul_of_nonneg_left hjreal Real.pi_pos.le
  have hgap : ε + Real.pi/4 ≤ Real.pi*(j : ℝ) -
      (canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) i).re := by
    nlinarith
  simpa only [sourceClusterDisc, refinedResonantDisk, Complex.ofReal_mul,
    Complex.ofReal_intCast] using
    (midpoint_disc_disjoint_right_point_disc hwithin hε (by positivity : 0 ≤ Real.pi/4) hgap)

/-- A central midpoint disc is disjoint from every negative tail free disc
once the outer left endpoint is localized and the margin is at most π/4. -/
theorem sourceClusterDisc_disjoint_negative_tail
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (N : ℕ) (ε : ℝ) (hε : 0 ≤ ε) (hεmax : ε ≤ Real.pi/4)
    (houter : canonicalPeriodicLeft hp hp1 (periodOnePotential φ)
      (periodOnePotential_mem φ) (-(N : ℤ)) ∈ refinedResonantDisk (-(N : ℤ)))
    {i j : ℤ} (hi : -(N : ℤ) ≤ i) (hj : j < -(N : ℤ)) :
    Disjoint (sourceClusterDisc hp hp1 φ (fun _ => ε) i)
      (refinedResonantDisk j) := by
  have hwithin := re_le_of_complexLexLE
    ((canonicalPeriodicEndpoints_spec hp hp1 (periodOnePotential φ)
      (periodOnePotential_mem φ)).2.1 i)
  have hLi := source_left_le_left_of_le hp hp1 φ hφ hi
  have hLN := (abs_le.mp (refinedDisk_re_strip houter)).1
  have hjreal : (j : ℝ) + 1 ≤ ((-(N : ℤ)) : ℝ) := by
    exact_mod_cast (show j + 1 ≤ -(N : ℤ) by omega)
  have hmul := mul_le_mul_of_nonneg_left hjreal Real.pi_pos.le
  have hgap : Real.pi/4 + ε ≤
      (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) i).re -
        Real.pi*(j : ℝ) := by
    simp only [Int.cast_neg, Int.cast_natCast, mul_neg, mul_add, mul_one] at hLN hmul
    nlinarith [Real.pi_pos]
  have hh := point_disc_disjoint_right_midpoint_disc hwithin hε
    (by positivity : 0 ≤ Real.pi/4) hgap
  simpa only [sourceClusterDisc, refinedResonantDisk, Complex.ofReal_mul,
    Complex.ofReal_intCast] using hh.symm

end NLS.ZakharovShabat
