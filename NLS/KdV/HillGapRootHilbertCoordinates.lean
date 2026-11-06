import NLS.KdV.HillAbelianHilbertProduct
import NLS.SequenceSpaces.PowerDecaySummability

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal

namespace NLS.KdV



def hillGapRootScaledOffset (σ : ℕ → ℝ) (m : ℤ) : ℂ :=
  if 0 < m then ((σ (m.toNat-1)-freeHillValue m.toNat : ℝ) : ℂ)/(m : ℂ) else 0

theorem memlp_hillGapRootScaledOffset
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (σ : ℕ → ℝ) (hσ : σ ∈ hillGapRootBox q hq hr) :
    Memℓp (hillGapRootScaledOffset σ) 2 := by
  have hg : Memℓp (fun m : ℤ => 4*‖q‖*‖Coeff.positivePuncturedLattice 2 (by norm_num) m‖) 2 :=
    (lp.memℓp (Coeff.positivePuncturedLattice 2 (by norm_num))).norm.const_mul (4*‖q‖)
  have h := memlp_of_natAbs_eventual_bound 2 (by norm_num) (hillGapRootScaledOffset σ)
    (fun m : ℤ => 4*‖q‖*‖Coeff.positivePuncturedLattice 2 (by norm_num) m‖)
    (by simpa only [ENNReal.ofReal_ofNat] using hg) (hillRealLabelCutoff q) ?_
  · simpa only [ENNReal.ofReal_ofNat] using h
  · intro m hm
    unfold hillGapRootScaledOffset
    by_cases hmp : 0 < m
    · rw [if_pos hmp,Coeff.positivePuncturedLattice_apply,if_pos hmp]
      have hmcut : hillRealLabelCutoff q ≤ m.toNat := by omega
      have hmtwo : 2 ≤ m.toNat := (hillRealLabelCutoff_ge_two q).trans hmcut
      have hmbound : 8*‖q‖ ≤ (m.toNat : ℝ) := (hillRealLabelCutoff_bound q).trans
        (by exact_mod_cast hmcut)
      have hloc := hillGapRoot_high_localization q hq hr σ hσ m.toNat hmtwo hmbound
      rw [norm_div,norm_real,Real.norm_eq_abs,norm_inv,div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right hloc (inv_nonneg.mpr (norm_nonneg _))
    · rw [if_neg hmp,norm_zero]
      positivity

def hillGapRootHilbertCoordinates
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (σ : ℕ → ℝ) (hσ : σ ∈ hillGapRootBox q hq hr) : Coeff 2 :=
  ⟨hillGapRootScaledOffset σ,memlp_hillGapRootScaledOffset q hq hr σ hσ⟩

theorem hillGapRootHilbertCoordinates_reconstruct
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (σ : ℕ → ℝ) (hσ : σ ∈ hillGapRootBox q hq hr) (k : ℕ) :
    (σ k : ℂ) = (freeHillValue (k+1 : ℕ) : ℂ) + ((k+1 : ℕ) : ℂ)*
      hillGapRootHilbertCoordinates q hq hr σ hσ ((k+1 : ℕ) : ℤ) := by
  change (σ k : ℂ) = _ + ((k+1 : ℕ) : ℂ)*hillGapRootScaledOffset σ ((k+1 : ℕ) : ℤ)
  rw [hillGapRootScaledOffset,if_pos (by omega : 0 < ((k+1 : ℕ) : ℤ)),Int.toNat_natCast,
    Nat.add_sub_cancel,ofReal_sub,Int.cast_natCast]
  have hk : ((k+1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by omega : k+1 ≠ 0)
  field_simp
  ring

theorem hillAbelianHilbertPsi_eq_genuine_candidate
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (σ : ℕ → ℝ) (hσ : σ ∈ hillGapRootBox q hq hr) (n : ℕ) (energy : ℂ) :
    hillAbelianHilbertPsi n (energy,hillGapRootHilbertCoordinates q hq hr σ hσ) =
      hillAbelianPsiCandidate σ n energy :=
  hillAbelianHilbertPsi_eq_real_candidate n energy _ σ
    (hillGapRootHilbertCoordinates_reconstruct q hq hr σ hσ)

end NLS.KdV
