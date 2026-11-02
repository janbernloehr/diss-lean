import NLS.KdV.HillRealLabelingUniqueness

/-! # Canonical real labels of the actual Hill characteristic

Existence at one explicit cutoff and cutoff independence define one
intrinsic ordered labeling of the actual characteristic. Every admissible
cutoff describes the same labels and analytic multiplicities.
-/

noncomputable section
open Set
open scoped Classical
namespace NLS.KdV

def hillRealLabelCutoff (q : WeightedCoeff SpectralWeight.one.toWeight 2) : ℕ :=
  max 2 ⌈16*‖q‖⌉₊

theorem hillRealLabelCutoff_ge_two (q : WeightedCoeff SpectralWeight.one.toWeight 2) :
    2 ≤ hillRealLabelCutoff q := le_max_left _ _

theorem hillRealLabelCutoff_bound (q : WeightedCoeff SpectralWeight.one.toWeight 2) :
    16*‖q‖ ≤ (hillRealLabelCutoff q : ℝ) :=
  (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right 2 ⌈16*‖q‖⌉₊))

/-- The intrinsic one-sided real characteristic labels, with repetitions
equal to the analytic multiplicities of the physical characteristic. -/
def hillRealLabels
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hreal : IsRealHillPotential (SpectralWeight.one.toCoeff q)) : ℕ → ℝ :=
  Classical.choose (exists_hillRealCharacteristicLabeling q hq hreal (hillRealLabelCutoff q)
    (hillRealLabelCutoff_ge_two q) (hillRealLabelCutoff_bound q))

theorem hillRealLabels_spec
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hreal : IsRealHillPotential (SpectralWeight.one.toCoeff q)) :
    HillRealCharacteristicLabeling q (hillRealLabelCutoff q) (hillRealLabels q hq hreal) :=
  Classical.choose_spec (exists_hillRealCharacteristicLabeling q hq hreal (hillRealLabelCutoff q)
    (hillRealLabelCutoff_ge_two q) (hillRealLabelCutoff_bound q))

theorem hillRealLabels_congr
    (q p : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hp : SpectralWeight.one.toCoeff p ∈ Coeff.paritySubspace 0)
    (hrealq : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (hrealp : IsRealHillPotential (SpectralWeight.one.toCoeff p)) (he : q = p) :
    hillRealLabels q hq hrealq = hillRealLabels p hp hrealp := by
  subst p
  rfl

/-- Every admissible central cutoff yields the same canonical labels. -/
theorem hillRealLabels_spec_at
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hreal : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (N : ℕ) (hN : 2 ≤ N) (hcut : 16*‖q‖ ≤ (N : ℝ)) :
    HillRealCharacteristicLabeling q N (hillRealLabels q hq hreal) := by
  obtain ⟨lambda,h⟩ := exists_hillRealCharacteristicLabeling q hq hreal N hN hcut
  have he := h.unique (hillRealLabels_spec q hq hreal) hq
  rwa [he] at h

theorem monotone_hillRealLabels
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hreal : IsRealHillPotential (SpectralWeight.one.toCoeff q)) :
    Monotone (hillRealLabels q hq hreal) := (hillRealLabels_spec q hq hreal).monotone

theorem hillRealLabels_root_iff
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hreal : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (z : ℂ) :
    hillL2Radicand (SpectralWeight.one.toCoeff q) z = 0 ↔
      ∃ j : ℕ, z = (hillRealLabels q hq hreal j : ℂ) := (hillRealLabels_spec q hq hreal).roots z

theorem hillRealLabels_global_multiplicity
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hreal : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (x : ℝ) :
    {j : ℕ | hillRealLabels q hq hreal j = x}.Finite ∧
      (∑ᶠ j : ℕ, if hillRealLabels q hq hreal j = x then (1 : ℕ) else 0) =
        analyticOrderNatAt (hillL2Radicand (SpectralWeight.one.toCoeff q)) x :=
  ⟨(hillRealLabels_spec q hq hreal).finite_fiber hq x,
    ((hillRealLabels_spec q hq hreal).finite_support_and_multiplicity hq x).2⟩

theorem hillRealLabels_high_pair
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hreal : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (n : ℕ) (hn : 2 ≤ n) (hcut : 16*‖q‖ ≤ (n : ℝ)) :
    ∃ p : HillRealHighGapPair (SpectralWeight.one.toCoeff q) n,
      hillRealLabels q hq hreal (2*n-1) = p.left ∧ hillRealLabels q hq hreal (2*n) = p.right :=
  (hillRealLabels_spec_at q hq hreal n hn hcut).high_pair n le_rfl

/-- The least actual energy, fixed by the canonical ordered characteristic. -/
def hillLowestEnergy
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hreal : IsRealHillPotential (SpectralWeight.one.toCoeff q)) : ℝ := hillRealLabels q hq hreal 0

theorem hillLowestEnergy_root
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hreal : IsRealHillPotential (SpectralWeight.one.toCoeff q)) :
    hillL2Radicand (SpectralWeight.one.toCoeff q) (hillLowestEnergy q hq hreal) = 0 :=
  (hillRealLabels_spec q hq hreal).root 0

theorem hillLowestEnergy_le_root
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hreal : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (z : ℂ)
    (hz : hillL2Radicand (SpectralWeight.one.toCoeff q) z = 0) :
    hillLowestEnergy q hq hreal ≤ z.re := by
  obtain ⟨j,rfl⟩ := (hillRealLabels_root_iff q hq hreal z).mp hz
  exact monotone_hillRealLabels q hq hreal (Nat.zero_le j)

theorem hillLowestEnergy_mem_centralInterval
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hreal : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (N : ℕ) (hN : 2 ≤ N) (hcut : 8*‖q‖ ≤ (N : ℝ)) :
    hillLowestEnergy q hq hreal ∈ Ioo (-(N : ℝ)^2) (hillCentralSeparator N) := by
  have hlo := hillL2Radicand_re_lower_bound q hq N (by omega) hcut _ (hillLowestEnergy_root q hq hreal)
  have hc := card_hillRealCentralRoots q hq hreal N hN hcut
  have hp : 0 < (hillRealCentralRoots q hq N hN hcut).card := by omega
  obtain ⟨x,hx⟩ := Multiset.card_pos_iff_exists_mem.mp hp
  have hx' := (mem_hillRealCentralRoots_iff q hq hreal N hN hcut x).mp hx
  exact ⟨hlo,(hillLowestEnergy_le_root q hq hreal x hx'.2).trans_lt hx'.1.2⟩

end NLS.KdV
