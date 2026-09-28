import NLS.ZakharovShabat.FreeDerivativeZeroCounts
import NLS.ZakharovShabat.RestoredSpectralPairs
import Mathlib.Topology.Maps.Proper.CompactlyGenerated

/-!
# Properness of the displaced spectral root sequence

An `ℓᵖ` displacement is uniformly bounded, while the free lattice
escapes every compact set. Consequently, the displaced-root map from
the discrete integer indices is proper and its range is closed.
No quarter-π localization is needed for this fact.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The preimage of a compact spectral set under the displaced-root
map contains only finitely many integer indices. -/
theorem finite_displacedRoots_preimage_compact
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (a : Coeff p) (K : Set ℂ) (hK : IsCompact K) :
    (displacedRoots a ⁻¹' K).Finite := by
  obtain ⟨B,hB⟩ := hK.isBounded.exists_norm_le
  obtain ⟨N,hN⟩ := exists_nat_gt ((B+‖a‖)/Real.pi)
  apply (Set.finite_Icc (-(N:ℤ)) (N:ℤ)).subset
  intro k hk
  have hroot : ‖displacedRoots a k‖ ≤ B := hB _ hk
  have ha : ‖a k‖ ≤ ‖a‖ :=
    lp.norm_apply_le_norm (ne_of_gt (zero_lt_one.trans_le Fact.out)) a k
  have hcenter : ‖(Real.pi : ℂ)*k‖ = Real.pi*(k.natAbs:ℝ) := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos Real.pi_pos,Complex.norm_intCast]
    simp only [Nat.cast_natAbs,Int.cast_abs]
  have htri : ‖(Real.pi : ℂ)*k‖ ≤ ‖displacedRoots a k‖+‖a k‖ := by
    have heq : (Real.pi : ℂ)*k = displacedRoots a k-a k := by
      simp only [displacedRoots]
      ring
    rw [heq]
    exact norm_sub_le _ _
  have hNreal : (B+‖a‖)/Real.pi < (N:ℝ) := by
    exact_mod_cast hN
  have hlarge : B+‖a‖ < Real.pi*(N:ℝ) :=
    by simpa only [mul_comm] using (div_lt_iff₀ Real.pi_pos).mp hNreal
  have hkNat : k.natAbs < N := by
    have hkReal : (k.natAbs:ℝ) < (N:ℝ) := by
      rw [hcenter] at htri
      nlinarith [Real.pi_pos]
    exact_mod_cast hkReal
  simp only [Set.mem_Icc]
  omega

/-- Every `ℓᵖ` displaced-root map is proper. -/
theorem isProperMap_displacedRoots
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (a : Coeff p) : IsProperMap (displacedRoots a) := by
  apply isProperMap_iff_isCompact_preimage.mpr
  constructor
  · exact continuous_of_discreteTopology
  · intro K hK
    exact isCompact_iff_finite.mpr
      (finite_displacedRoots_preimage_compact a K hK)

/-- The range of every `ℓᵖ` displaced-root sequence is closed. -/
theorem isClosed_range_displacedRoots
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (a : Coeff p) : IsClosed (Set.range (displacedRoots a)) :=
  (isProperMap_displacedRoots a).isClosed_range

end NLS.ZakharovShabat
