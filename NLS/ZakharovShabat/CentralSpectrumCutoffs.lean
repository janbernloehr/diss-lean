import NLS.ZakharovShabat.PeriodicCounting

/-!
# Enlarging the central spectral cluster

Increasing the central cutoff absorbs exactly the intervening disjoint periodic
spectral discs. Only the counting data at the smaller cutoff are required.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The central boxes increase with their cutoff. -/
theorem centralSpectralBox_mono {N K : ℕ} (hNK : N ≤ K) :
    centralSpectralBox N ⊆ centralSpectralBox K := by
  intro z hz
  have h : (N : ℝ) ≤ K := by exact_mod_cast hNK
  exact ⟨hz.1.trans_le (by nlinarith [Real.pi_pos]), hz.2.trans h⟩

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual finite central spectra increase with their cutoff. -/
theorem centralPeriodicSpectrum_mono (hp : p ≠ ⊤) (φ : PairSpace p)
    {N K : ℕ} (hNK : N ≤ K) :
    centralPeriodicSpectrum hp φ N ⊆ centralPeriodicSpectrum hp φ K := by
  intro z hz
  obtain ⟨hs,hb⟩ := (mem_centralPeriodicSpectrum hp φ N z).mp hz
  exact (mem_centralPeriodicSpectrum hp φ K z).mpr ⟨hs,centralSpectralBox_mono hNK hb⟩

/-- Different periodic discs contain disjoint finite spectral sets. -/
theorem enclosedPeriodicSpectrum_disjoint (hp : p ≠ ⊤) (φ : PairSpace p)
    (n m : ℤ) (hnm : n ≠ m) :
    Disjoint (enclosedPeriodicSpectrum hp φ ((Real.pi : ℂ)*n) (Real.pi/4))
      (enclosedPeriodicSpectrum hp φ ((Real.pi : ℂ)*m) (Real.pi/4)) := by
  apply Finset.disjoint_left.mpr
  intro z hn hm
  exact (periodicDisks_disjoint n m hnm).le_bot
    ⟨((mem_enclosedPeriodicSpectrum hp φ _ z _).mp hn).2,
      ((mem_enclosedPeriodicSpectrum hp φ _ z _).mp hm).2⟩

/-- The added central spectrum is exactly the family of newly enclosed discs. -/
theorem PeriodicCountingData.centralSpectrum_eq_union {hp : p ≠ ⊤} {φ : PairSpace p}
    {N : ℕ} (hc : PeriodicCountingData hp φ N) (K : ℕ) (hNK : N ≤ K) :
    centralPeriodicSpectrum hp φ K = centralPeriodicSpectrum hp φ N ∪
      (Finset.Icc (-(K : ℤ)) (K : ℤ) \ Finset.Icc (-(N : ℤ)) (N : ℤ)).biUnion
        (fun n => enclosedPeriodicSpectrum hp φ ((Real.pi : ℂ)*n) (Real.pi/4)) := by
  classical
  have hrK : Real.pi/4 ≤ (K : ℝ) := by
    have h1 : (1 : ℝ) ≤ K := by exact_mod_cast hc.cutoff_pos.trans_le hNK
    linarith [Real.pi_le_four]
  ext z
  simp only [Finset.mem_union, Finset.mem_biUnion]
  constructor
  · intro hz
    obtain ⟨hs,hb⟩ := (mem_centralPeriodicSpectrum hp φ K z).mp hz
    rcases (hc.mem_spectrum_iff_central_or_disk z).mp hs with hn | ⟨n,⟨hn,hd⟩,_⟩
    · exact Or.inl hn
    · have hindex := (smallDisk_central_selection K n le_rfl hrK
        ((mem_enclosedPeriodicSpectrum hp φ _ z _).mp hd).2).2.mp hb
      exact Or.inr ⟨n, by simp only [Finset.mem_sdiff, Finset.mem_Icc]; omega, hd⟩
  · rintro (hz | ⟨n,hn,hz⟩)
    · exact centralPeriodicSpectrum_mono hp φ hNK hz
    · obtain ⟨hs,hd⟩ := (mem_enclosedPeriodicSpectrum hp φ _ z _).mp hz
      have hindex : n.natAbs ≤ K := by
        simp only [Finset.mem_sdiff, Finset.mem_Icc] at hn
        omega
      exact (mem_centralPeriodicSpectrum hp φ K z).mpr
        ⟨hs,(smallDisk_central_selection K n le_rfl hrK hd).2.mpr hindex⟩

/-- The newly absorbed discs are disjoint from the old central spectrum. -/
theorem PeriodicCountingData.central_disjoint_addedDisks {hp : p ≠ ⊤} {φ : PairSpace p}
    {N : ℕ} (hc : PeriodicCountingData hp φ N) (K : ℕ) :
    Disjoint (centralPeriodicSpectrum hp φ N)
      ((Finset.Icc (-(K : ℤ)) (K : ℤ) \ Finset.Icc (-(N : ℤ)) (N : ℤ)).biUnion
        (fun n => enclosedPeriodicSpectrum hp φ ((Real.pi : ℂ)*n) (Real.pi/4))) := by
  classical
  apply Finset.disjoint_left.mpr
  intro z hz hd
  obtain ⟨n,hn,hd⟩ := Finset.mem_biUnion.mp hd
  have hn' : N < n.natAbs := by
    simp only [Finset.mem_sdiff, Finset.mem_Icc] at hn
    omega
  exact Finset.disjoint_left.mp (hc.central_disjoint_disk n hn') hz hd

end NLS.ZakharovShabat
