import NLS.ZakharovShabat.SourcePsiOriginalIndexRatio

/-! Every nontrivial original index ratio has a uniform positive
lower norm bound, before all placed inputs and both signed indices. -/
noncomputable section
open Set Metric Complex
open scoped ENNReal Classical
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem SourceIsolatingNeighborhoods.indexRatio_uniform_lower
    {hp : p ≠ ⊤} {hp1 : 1 < p} {V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {C : ℝ} (hD : SourceIsolatingNeighborhoods hp hp1 V D C) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ a ∈ sourcePsiOriginalRootPlacement (p := p) D,
      ∀ n m : ℤ, n ≠ m → ∀ z ∈ D m, γ ≤ ‖sourcePsiOriginalIndexRatio n m a z‖ := by
  obtain ⟨A,hA,hbound⟩ := hD.exists_uniform_lattice_bound
  let γ := Real.pi/(Real.pi+2*A)
  have hden : 0 < Real.pi+2*A := by positivity
  have hγ : 0 < γ := div_pos Real.pi_pos hden
  refine ⟨γ,hγ,?_⟩
  intro a ha n m hnm z hz
  have hs := hD.weighted_separation_closure n m hnm.symm (displacedRoots a n) (ha n) z (subset_closure hz)
  have hr : 0 < ‖displacedRoots a n-z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hs.1.symm)
  have hdnorm : ‖((n-m:ℤ):ℂ)‖ = ((n-m).natAbs:ℝ) := by
    rw [Complex.norm_intCast,← Int.cast_abs,← Int.natCast_natAbs]
    simp
  have hdp : 0 < (n-m).natAbs := Int.natAbs_pos.mpr (sub_ne_zero.mpr hnm)
  have hd : 1 ≤ ‖((n-m:ℤ):ℂ)‖ := by rw [hdnorm]; exact_mod_cast hdp
  have he : displacedRoots a n-z = (displacedRoots a n-(Real.pi:ℂ)*n)+
      (Real.pi:ℂ)*((n-m:ℤ):ℂ)+((Real.pi:ℂ)*m-z) := by push_cast; ring
  have hu : ‖displacedRoots a n-z‖ ≤ (Real.pi+2*A)*‖((n-m:ℤ):ℂ)‖ := by
    rw [he]
    have htri := (norm_add_le (displacedRoots a n-(Real.pi:ℂ)*n+(Real.pi:ℂ)*((n-m:ℤ):ℂ))
      ((Real.pi:ℂ)*m-z)).trans (add_le_add (norm_add_le _ _) le_rfl)
    have hn := hbound n (displacedRoots a n) (ha n)
    have hm : ‖(Real.pi:ℂ)*m-z‖ ≤ A := by rw [norm_sub_rev]; exact hbound m z hz
    have hmiddle : ‖(Real.pi:ℂ)*((n-m:ℤ):ℂ)‖ = Real.pi*‖((n-m:ℤ):ℂ)‖ := by
      rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg Real.pi_pos.le]
    rw [hmiddle] at htri
    nlinarith
  rw [sourcePsiOriginalIndexRatio,norm_div,norm_mul,Complex.norm_real,Real.norm_of_nonneg Real.pi_pos.le]
  apply (le_div_iff₀ hr).mpr
  calc
    _ ≤ γ*((Real.pi+2*A)*‖((n-m:ℤ):ℂ)‖) := mul_le_mul_of_nonneg_left hu hγ.le
    _ = _ := by dsimp only [γ]; field_simp

end NLS.ZakharovShabat
