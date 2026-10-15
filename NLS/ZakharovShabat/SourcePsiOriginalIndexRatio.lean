import NLS.ZakharovShabat.SourcePsiOriginalRatioEstimate
import NLS.ZakharovShabat.SourcePsiOriginalOmega

/-!
# Equation (2.28) on the original isolating disks

The literal index ratio differs from one by O(1/|n-m|), uniformly over
all full root inputs placed in the supplied original disks. No gap
placement or root reality is assumed. At each fixed row, one tail
cutoff works for every such root input and every point of that disk.
-/

noncomputable section
open Set Complex Metric Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The literal ratio (nπ-mπ)/(σₙ-z) in (2.28). -/
def sourcePsiOriginalIndexRatio (n m : ℤ) (a : Coeff p) (z : ℂ) : ℂ :=
  (Real.pi:ℂ)*((n-m:ℤ):ℂ)/(displacedRoots a n-z)

omit [Fact (1 ≤ p)] in
/-- The exact algebraic identity underlying the source estimate. -/
theorem sourcePsiOriginalIndexRatio_sub_one (n m : ℤ) (a : Coeff p) (z : ℂ)
    (hz : displacedRoots a n ≠ z) :
    sourcePsiOriginalIndexRatio n m a z = 1 +
      ((Real.pi:ℂ)*n-displacedRoots a n+(z-(Real.pi:ℂ)*m))/(displacedRoots a n-z) := by
  unfold sourcePsiOriginalIndexRatio
  push_cast
  field_simp [sub_ne_zero.mpr hz]
  ring

/-- One reciprocal-distance bound covers all roots in the original disks. -/
theorem SourceIsolatingNeighborhoods.original_indexRatio_uniform_bound
    {hp : p ≠ ⊤} {hp1 : 1 < p} {V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (hD : SourceIsolatingNeighborhoods hp hp1 V D c) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ a ∈ sourcePsiOriginalRootPlacement (p := p) D,
      ∀ n m : ℤ, m ≠ n → ∀ z ∈ D m,
        ‖sourcePsiOriginalIndexRatio n m a z-1‖ ≤ K/‖((n-m:ℤ):ℂ)‖ := by
  obtain ⟨A,hA,hbound⟩ := hD.exists_uniform_lattice_bound
  refine ⟨(A+A)*c,mul_nonneg (add_nonneg hA hA) (zero_le_one.trans hD.one_le),?_⟩
  intro a ha n m hmn z hz
  have hsep := hD.weighted_separation_closure n m hmn (displacedRoots a n) (ha n) z (subset_closure hz)
  have hb := sourcePsi_indexRatio_error_bound n m hmn (displacedRoots a n) z hsep.1.symm
    A A c (hbound m z hz) (hbound n _ (ha n)) hsep.2
  have he : sourcePsiOriginalIndexRatio n m a z-1 =
      (Real.pi:ℂ)*(((n-m:ℤ):ℂ)/(displacedRoots a n-z)-(Real.pi:ℂ)⁻¹) := by
    unfold sourcePsiOriginalIndexRatio
    have hpi : (Real.pi:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    field_simp [hpi]
  rw [he,norm_mul,Complex.norm_real,Real.norm_of_nonneg Real.pi_pos.le]
  calc
    _ ≤ Real.pi * (((A+A)/Real.pi*c)/‖((n-m:ℤ):ℂ)‖) :=
      mul_le_mul_of_nonneg_left hb Real.pi_pos.le
    _ = _ := by field_simp

/-- For a fixed row, the ratio tends uniformly to one in both index directions. -/
theorem SourceIsolatingNeighborhoods.original_indexRatio_uniform_tail
    {hp : p ≠ ⊤} {hp1 : 1 < p} {V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (m : ℤ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℤ, N ≤ n.natAbs →
      ∀ a ∈ sourcePsiOriginalRootPlacement (p := p) D, ∀ z ∈ D m,
        ‖sourcePsiOriginalIndexRatio n m a z-1‖ < ε := by
  obtain ⟨K,hK,hb⟩ := hD.original_indexRatio_uniform_bound
  obtain ⟨L,hL⟩ := exists_nat_gt (K/ε)
  refine ⟨m.natAbs+L+1,?_⟩
  intro n hn a ha z hz
  have hmn : m ≠ n := by intro he; subst n; omega
  have ht : n.natAbs ≤ (n-m).natAbs+m.natAbs := by
    simpa only [sub_add_cancel] using Int.natAbs_add_le (n-m) m
  have hnorm : ‖((n-m:ℤ):ℂ)‖ = ((n-m).natAbs:ℝ) := by
    rw [Complex.norm_intCast, ← Int.cast_abs, ← Int.natCast_natAbs]
    simp
  have hden : 0 < ‖((n-m:ℤ):ℂ)‖ := norm_pos_iff.mpr (by exact_mod_cast sub_ne_zero.mpr hmn.symm)
  have hlarge : (L:ℝ) < ‖((n-m:ℤ):ℂ)‖ := by
    rw [hnorm]
    exact_mod_cast (show L < (n-m).natAbs by omega)
  apply (hb a ha n m hmn z hz).trans_lt
  apply (div_lt_iff₀ hden).mpr
  have hh := (div_lt_iff₀ hε).mp (hL.trans hlarge)
  nlinarith

end NLS.ZakharovShabat
