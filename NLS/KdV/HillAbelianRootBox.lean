import NLS.KdV.HillEnergyCriticalProduct

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal

namespace NLS.KdV

variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

def hillGapRootBox : Set (ℕ → ℝ) :=
  {σ | ∀ k, σ k ∈ Icc (hillRealLabels q hq hr (2*(k+1)-1))
    (hillRealLabels q hq hr (2*(k+1)))}

theorem isCompact_hillGapRootBox : IsCompact (hillGapRootBox q hq hr) := by
  exact isCompact_pi_infinite (s := fun k : ℕ => Icc
    (hillRealLabels q hq hr (2*(k+1)-1)) (hillRealLabels q hq hr (2*(k+1))))
    (fun _ => isCompact_Icc)

theorem hillGapRootBox_nonempty : (hillGapRootBox q hq hr).Nonempty := by
  refine ⟨fun k => hillGapCriticalPoint q hq hr (k+1),?_⟩
  intro k
  exact (hillGapCriticalPoint_spec q hq hr (k+1) (by omega)).1

def hillGapRootEnergyFactor (σ : ℕ → ℝ) (k : ℕ) (z : ℂ) : ℂ :=
  ((σ k : ℂ)-z)/(freeHillValue (k+1 : ℕ) : ℂ)

def hillAbelianNumeratorFactor (σ : ℕ → ℝ) (n k : ℕ) (z : ℂ) : ℂ :=
  if k+1 = n then 1 else hillGapRootEnergyFactor σ k z

theorem hillGapRoot_high_localization (σ : ℕ → ℝ) (hσ : σ ∈ hillGapRootBox q hq hr)
    (n : ℕ) (hn : 2 ≤ n) (hcut : 16*‖q‖ ≤ (n : ℝ)) :
    |σ (n-1)-freeHillValue n| ≤ 4*‖q‖ := by
  obtain ⟨p,hl,hu⟩ := hillRealLabels_high_pair q hq hr n hn hcut
  have hloc := p.localization q hq n (by omega) (by linarith [norm_nonneg q])
  have hs := hσ (n-1)
  have hn1 : n-1+1 = n := by omega
  rw [hn1,hl,hu] at hs
  rcases abs_le.mp hloc.1 with ⟨hlo0,hlo1⟩
  rcases abs_le.mp hloc.2 with ⟨hup0,hup1⟩
  exact abs_le.mpr ⟨by linarith [hs.1],by linarith [hs.2]⟩

theorem exists_hillGapRootEnergyFactor_uniform_majorant (R : ℝ) (hR : 0 ≤ R) :
    ∃ N : ℕ, ∃ u : ℕ → ℝ, Summable u ∧ ∀ σ ∈ hillGapRootBox q hq hr,
      ∀ k : ℕ, N ≤ k → ∀ z : ℂ, ‖z‖ ≤ R →
        ‖hillGapRootEnergyFactor σ k z-1‖ ≤ u k := by
  let C := 4*‖q‖+R
  let u : ℕ → ℝ := fun k => C/(k+1 : ℕ)^2
  have hs0 : Summable (fun n : ℕ => 1/(n : ℝ)^2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hs : Summable u := by
    simpa only [u,div_eq_mul_inv,one_mul] using
      ((summable_nat_add_iff 1).mpr hs0).mul_left C
  refine ⟨hillRealLabelCutoff q,u,hs,?_⟩
  intro σ hσ k hk z hz
  have hn2 : 2 ≤ k+1 := by have h := hillRealLabelCutoff_ge_two q; omega
  have hcut : 16*‖q‖ ≤ (k+1 : ℕ) := (hillRealLabelCutoff_bound q).trans
    (by exact_mod_cast (show hillRealLabelCutoff q ≤ k+1 by omega))
  have hloc := hillGapRoot_high_localization q hq hr σ hσ (k+1) hn2 hcut
  simp only [Nat.add_sub_cancel] at hloc
  have hnle : ((k+1 : ℕ) : ℝ)^2 ≤ freeHillValue (k+1 : ℕ) := by
    have h := mul_le_mul_of_nonneg_right
      (show (1 : ℝ) ≤ Real.pi^2 by nlinarith [Real.pi_gt_three])
      (sq_nonneg ((k+1 : ℕ) : ℝ))
    simpa only [one_mul,freeHillValue,Int.cast_natCast] using h
  have hc : 0 < freeHillValue (k+1 : ℕ) := lt_of_lt_of_le (by positivity) hnle
  have he : hillGapRootEnergyFactor σ k z-1 =
      (((σ k-freeHillValue (k+1 : ℕ) : ℝ) : ℂ)-z)/
        (freeHillValue (k+1 : ℕ) : ℂ) := by
    unfold hillGapRootEnergyFactor
    rw [div_sub_one (ofReal_ne_zero.mpr (ne_of_gt hc))]
    push_cast
    ring
  rw [he,norm_div,norm_real,Real.norm_eq_abs,abs_of_pos hc]
  have hnum : ‖((σ k-freeHillValue (k+1 : ℕ) : ℝ) : ℂ)-z‖ ≤ C := by
    apply (norm_sub_le _ _).trans
    rw [norm_real,Real.norm_eq_abs]
    exact add_le_add hloc hz
  exact (div_le_div_of_nonneg_right hnum hc.le).trans
    (div_le_div_of_nonneg_left (by dsimp only [C]; positivity) (by positivity) hnle)

end NLS.KdV
