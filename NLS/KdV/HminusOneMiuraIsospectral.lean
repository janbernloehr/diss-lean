import NLS.KdV.MiuraRealSource
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

/-- Physical spectral exclusion implies the exact scalar radicand exclusion. -/
theorem hillHminusRadicand_ne_zero_of_not_mem_singularHillSpectrum
    (q : PeriodOneHminusOne) (E : ℂ)
    (hE : E ∉ singularHillSpectrum (periodOneOriginal q)) :
    hillHminusRadicand q E ≠ 0 := by
  intro hz
  apply hE
  apply (singularHillSpectrum_periodOne_iff_discriminant q E).mpr
  exact sub_eq_zero.mp hz

open NLS.ZakharovShabat

/-- Compatibility with the original physical outside-spectrum hypothesis. -/
theorem zero_not_mem_periodicSpectrum_of_shifted_miura
    (q : PeriodOneHminusOne) (u : Coeff 2) (c : ℂ)
    (himage : periodOneMiura u = q+periodOneL2Inclusion (lp.single 2 0 c))
    (hc : -c ∉ singularHillSpectrum (periodOneOriginal q)) :
    (0:ℂ) ∉ periodicSpectrum (by norm_num) (periodOnePotential (hillMiuraDiagonal u)) := by
  exact zero_not_mem_periodicSpectrum_of_shifted_miura_of_radicand_ne_zero q u c himage (hillHminusRadicand_ne_zero_of_not_mem_singularHillSpectrum q (-c) hc)

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
