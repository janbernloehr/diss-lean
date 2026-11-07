import NLS.ZakharovShabat.SourcePsiOriginalQuotientError

/-! Literal omitted-root quotients tend to one along arbitrary points
in the original positive row discs at each fixed full root input. -/
noncomputable section
open Set Complex Filter Topology
open scoped ENNReal Classical
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem SourceCorollary10_6Data.tendsto_quotient_positive_rows
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    (H : SourceCorollary10_6Data hp hp1 W)
    {D : ℤ → Set ℂ} {C : ℝ} (hD : SourceIsolatingNeighborhoods hp hp1 V D C)
    (hV : IsOpen V) (ψ : CoeffPair p) (hψW : ψ ∈ W) (hψV : ψ ∈ V)
    (a : Coeff p) (z : ℕ → ℂ) (hz : ∀ j : ℕ, z j ∈ D ((j:ℤ)+1)) :
    Tendsto (fun j : ℕ => sourceSingleRootQuotientJointProduct hp hp1 ((j:ℤ)+1) (z j,(a,ψ))) atTop (𝓝 1) := by
  obtain ⟨U,_,hbase,_,_,hbound⟩ := H.local_allDisk_quotient_errorBound hD hV ψ hψW hψV a
  obtain ⟨E,_,_,hE⟩ := hbound (a,ψ) hbase
  have ht : Tendsto (fun j : ℕ => ‖E ((j:ℤ)+1)‖) atTop (𝓝 0) := by
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨N,hN⟩ := Coeff.exists_cutoff_norm_apply_lt hp E hε
    refine ⟨N,fun j hj => ?_⟩
    have hn : ((j:ℤ)+1).natAbs = j+1 := by omega
    have hb := hN ((j:ℤ)+1) (by rw [hn]; omega)
    simpa [Real.dist_eq] using hb
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  exact squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _))
    (Eventually.of_forall (fun j => hE ((j:ℤ)+1) (z j) (hz j))) ht

end NLS.ZakharovShabat
