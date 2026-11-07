import NLS.ZakharovShabat.SourcePsiOriginalIndexRatio
import NLS.ZakharovShabat.SourcePsiGapProductCompact
import NLS.SequenceSpaces.UniformReciprocalTail
import NLS.SequenceSpaces.LpCoordinateContinuity

/-! Original index ratios tend to one on high ACTUAL gaps uniformly
in EVERY other signed index and every full gap-root sequence. -/
noncomputable section
open Set Metric Complex NLS.LpSequence
open scoped ENNReal Classical
namespace NLS.ZakharovShabat

def sourceGapRootErrorMajorant (ψ : CoeffPair 2) : Coeff 2 :=
  magnitude (canonicalPeriodicLeftDisplacement (by norm_num) (by norm_num)
    (periodOnePotential ψ) (periodOnePotential_mem ψ))+
      magnitude (sourcePeriodicGapDisplacement (by norm_num) (by norm_num) ψ)

theorem norm_sourceGapRootErrorMajorant_apply (ψ : CoeffPair 2) (k : ℤ) :
    ‖sourceGapRootErrorMajorant ψ k‖ =
      ‖canonicalPeriodicLeftDisplacement (by norm_num) (by norm_num)
        (periodOnePotential ψ) (periodOnePotential_mem ψ) k‖+
      ‖sourcePeriodicGapDisplacement (by norm_num) (by norm_num) ψ k‖ := by
  change ‖(‖canonicalPeriodicLeftDisplacement (by norm_num) (by norm_num)
    (periodOnePotential ψ) (periodOnePotential_mem ψ) k‖:ℂ)+
      (‖sourcePeriodicGapDisplacement (by norm_num) (by norm_num) ψ k‖:ℂ)‖ = _
  rw [← Complex.ofReal_add,Complex.norm_real,Real.norm_of_nonneg (by positivity)]

theorem SourceIsolatingNeighborhoods.gap_indexRatio_uniform_tail
    {V : Set (CoeffPair 2)} {D : ℤ → Set ℂ} {C : ℝ}
    (hD : SourceIsolatingNeighborhoods (by norm_num) (by norm_num) V D C)
    (ψ : CoeffPair 2) (hψ : ψ ∈ V) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ m : ℤ, N ≤ m.natAbs → ∀ a ∈ sourcePeriodicGapRootSet (by norm_num) (by norm_num) ψ,
      ∀ k : ℤ, k ≠ m → ∀ z ∈ sourcePeriodicSegment (by norm_num) (by norm_num) ψ m,
        ‖sourcePsiOriginalIndexRatio k m a z-1‖ < ε := by
  let ρ := sourceGapRootErrorMajorant ψ
  have hc : 0 < C := zero_lt_one.trans_le hD.one_le
  obtain ⟨N,hN⟩ := Coeff.exists_uniform_reciprocal_pair_tail ρ (ε/C) (div_pos hε hc)
  refine ⟨N,?_⟩
  intro m hm a ha k hkm z hz
  have hroot : ‖displacedRoots a k-(Real.pi:ℂ)*k‖ ≤ ‖ρ k‖ := by
    rw [norm_sourceGapRootErrorMajorant_apply]
    exact norm_sourcePeriodicSegment_sample_sub_free_le (by norm_num) (by norm_num) ψ k _ (ha k)
  have hpoint : ‖z-(Real.pi:ℂ)*m‖ ≤ ‖ρ m‖ := by
    rw [norm_sourceGapRootErrorMajorant_apply]
    exact norm_sourcePeriodicSegment_sample_sub_free_le (by norm_num) (by norm_num) ψ m z hz
  have hs := hD.weighted_separation_closure k m hkm.symm (displacedRoots a k)
    (hD.gap ψ hψ k (ha k)) z (subset_closure (hD.gap ψ hψ m hz))
  have hb := sourcePsi_indexRatio_error_bound k m hkm.symm (displacedRoots a k) z hs.1.symm
    ‖ρ m‖ ‖ρ k‖ C hpoint hroot hs.2
  have he : sourcePsiOriginalIndexRatio k m a z-1 =
      (Real.pi:ℂ)*(((k-m:ℤ):ℂ)/(displacedRoots a k-z)-(Real.pi:ℂ)⁻¹) := by
    unfold sourcePsiOriginalIndexRatio
    field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
  rw [he,norm_mul,Complex.norm_real,Real.norm_of_nonneg Real.pi_pos.le]
  calc
    _ ≤ Real.pi*(((‖ρ m‖+‖ρ k‖)/Real.pi*C)/‖((k-m:ℤ):ℂ)‖) :=
      mul_le_mul_of_nonneg_left hb Real.pi_pos.le
    _ = C*((‖ρ k‖+‖ρ m‖)/‖((k-m:ℤ):ℂ)‖) := by field_simp; ring
    _ < C*(ε/C) := mul_lt_mul_of_pos_left (hN m hm k hkm) hc
    _ = ε := mul_div_cancel₀ _ hc.ne'

end NLS.ZakharovShabat
