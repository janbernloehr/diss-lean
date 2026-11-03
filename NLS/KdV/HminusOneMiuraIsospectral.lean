import NLS.KdV.HminusOneMiuraHighPairs
import NLS.KdV.HminusOnePhysicalCharacteristic
import NLS.ZakharovShabat.SourceIsospectralSet

/-!
# Full isospectral transport through a common rough real Miura shift

The energy at zero Dirac frequency is treated using the exact trace identity.
When that energy lies outside the original Hill spectrum, the actual
multiplicity identity extends to every frequency, including zero. The
resulting Dirac isospectrality retains both spectra and algebraic counts.
-/
noncomputable section
open Set Complex
open scoped ENNReal ComplexConjugate
namespace NLS.KdV
open NLS.ZakharovShabat

/-- A real scalar L2 lift determines the actual original real diagonal
Dirac source, with the original unit-period source convention. -/
def hillMiuraRealSource (u : PeriodOneRealL2) : realTypeSourceSubmodule 2 :=
  ⟨hillMiuraDiagonal u.val,by
    intro n
    change (hillMiuraDiagonal u.val).snd n = conj ((hillMiuraDiagonal u.val).fst (-n))
    rw [hillMiuraDiagonal_snd,hillMiuraDiagonal_fst]
    simpa only [neg_neg] using u.property (-n)⟩

/-- The exact shifted trace excludes zero Dirac frequency whenever its
physical Hill energy is outside the full original spectrum. -/
theorem zero_not_mem_periodicSpectrum_of_shifted_miura
    (q : PeriodOneHminusOne) (u : Coeff 2) (c : ℂ)
    (himage : periodOneMiura u = q+periodOneL2Inclusion (lp.single 2 0 c))
    (hc : -c ∉ singularHillSpectrum (periodOneOriginal q)) :
    (0:ℂ) ∉ periodicSpectrum (by norm_num) (periodOnePotential (hillMiuraDiagonal u)) := by
  intro hz
  have hd := (canonicalDiscriminant_sq_eq_four_iff
    (periodOnePotential (hillMiuraDiagonal u)) (periodOnePotential_mem _) 0).mpr hz
  have ht := hillHminusDiscriminant_eq_miura_of_shifted_image q u c (-c) himage
  have ht' : hillHminusDiscriminant q (-c) =
      canonicalDiscriminant (by norm_num) (periodOnePotential (hillMiuraDiagonal u)) 0 := by
    simpa only [neg_add_cancel,hillMiuraL2Discriminant,Complex.sqrt_zero,
      hillMiuraFrequencyTrace] using ht
  apply hc
  apply (singularHillSpectrum_periodOne_iff_discriminant q (-c)).mpr
  rw [ht']
  exact hd

/-- Outside-spectrum shift energy removes the zero-frequency exception
from the actual rough Miura algebraic multiplicity identity. -/
theorem singularHillAlgebraicMultiplicity_shifted_miura_all
    (q : PeriodOneHminusOne) (u : PeriodOneRealL2) (c z : ℂ)
    (himage : periodOneMiura u.val = q+periodOneL2Inclusion (lp.single 2 0 c))
    (hc : -c ∉ singularHillSpectrum (periodOneOriginal q)) :
    singularHillAlgebraicMultiplicity (periodOneOriginal q) (z^2-c) =
      periodicAlgebraicMultiplicity (by norm_num)
        (periodOnePotential (hillMiuraDiagonal u.val)) z := by
  by_cases hz : z = 0
  · subst z
    have hzero := zero_not_mem_periodicSpectrum_of_shifted_miura q u.val c himage hc
    have hH : singularHillAlgebraicMultiplicity (periodOneOriginal q) (-c) = 0 := by
      apply Nat.eq_zero_of_not_pos
      intro h
      exact hc ((singularHillAlgebraicMultiplicity_pos_iff _ _).mp h)
    have hD : periodicAlgebraicMultiplicity (by norm_num)
        (periodOnePotential (hillMiuraDiagonal u.val)) 0 = 0 := by
      apply Nat.eq_zero_of_not_pos
      intro h
      exact hzero ((periodicAlgebraicMultiplicity_pos_iff _ _ _).mp h)
    simp only [zero_pow (by norm_num : (2:ℕ) ≠ 0),zero_sub,hH,hD]
  · exact singularHillAlgebraicMultiplicity_shifted_miura q u c z hz himage

/-- Real lifts of fully isospectral original Hill potentials at one common
outside-spectrum shift belong to one actual original Dirac isospectral set. -/
theorem hillMiuraRealSource_mem_isospectral_of_shifted_images
    (q r : PeriodOneHminusOne) (u v : PeriodOneRealL2) (c : ℂ)
    (hu : periodOneMiura u.val = q+periodOneL2Inclusion (lp.single 2 0 c))
    (hv : periodOneMiura v.val = r+periodOneL2Inclusion (lp.single 2 0 c))
    (hiso : ∀ z, singularHillAlgebraicMultiplicity (periodOneOriginal r) z =
      singularHillAlgebraicMultiplicity (periodOneOriginal q) z)
    (hc : -c ∉ singularHillSpectrum (periodOneOriginal q)) :
    hillMiuraRealSource v ∈ sourceIsospectralSet (by norm_num) (hillMiuraRealSource u) := by
  have hr : -c ∉ singularHillSpectrum (periodOneOriginal r) := by
    intro h
    have hp := (singularHillAlgebraicMultiplicity_pos_iff _ _).mpr h
    rw [hiso] at hp
    exact hc ((singularHillAlgebraicMultiplicity_pos_iff _ _).mp hp)
  have hm (z : ℂ) : periodicAlgebraicMultiplicity (by norm_num)
      (periodOnePotential (hillMiuraDiagonal v.val)) z =
        periodicAlgebraicMultiplicity (by norm_num)
          (periodOnePotential (hillMiuraDiagonal u.val)) z := by
    rw [← singularHillAlgebraicMultiplicity_shifted_miura_all r v c z hv hr,
      ← singularHillAlgebraicMultiplicity_shifted_miura_all q u c z hu hc,hiso]
  refine ⟨?_,hm⟩
  ext z
  rw [← periodicAlgebraicMultiplicity_pos_iff,← periodicAlgebraicMultiplicity_pos_iff]
  exact congrArg (fun n : ℕ => 0 < n) (hm z) |>.to_iff

end NLS.KdV
