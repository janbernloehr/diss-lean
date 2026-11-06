import NLS.ZakharovShabat.SpectralModulation
import NLS.ZakharovShabat.PeriodOneEmbedding
import NLS.ZakharovShabat.SourceRealTypeBanachSpace

/-! # Norm-preserving spectral translation of actual period-one sources -/
noncomputable section
set_option autoImplicit false
open Set Complex
open scoped ENNReal ComplexConjugate
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Opposite source Fourier shifts preserve the ORIGINAL source pair norm. -/
def sourceSpectralModulation (n : ℤ) : CoeffPair p ≃ₗᵢ[ℂ] CoeffPair p :=
  (Coeff.shift (-n)).withLpProdCongr p (Coeff.shift n)

@[simp] theorem sourceSpectralModulation_fst (n j : ℤ) (φ : CoeffPair p) :
    (sourceSpectralModulation n φ).fst j=φ.fst (j+n) := by
  change Coeff.shift (-n) φ.fst j=_
  rw [Coeff.shift_apply,sub_neg_eq_add]

@[simp] theorem sourceSpectralModulation_snd (n j : ℤ) (φ : CoeffPair p) :
    (sourceSpectralModulation n φ).snd j=φ.snd (j-n) := rfl

/-- The modulation preserves the actual source real form. -/
theorem isRealType_sourceSpectralModulation (n : ℤ) (φ : CoeffPair p)
    (hr : IsRealType (CoeffPair.toMax p φ)) :
    IsRealType (CoeffPair.toMax p (sourceSpectralModulation n φ)) := by
  intro j
  change (sourceSpectralModulation n φ).snd j=conj ((sourceSpectralModulation n φ).fst (-j))
  rw [sourceSpectralModulation_snd,sourceSpectralModulation_fst,show -j+n=-(j-n) by omega]
  exact hr (j-n)

private theorem periodDouble_shift (n : ℤ) (a : Coeff p) :
    Coeff.periodDouble (Coeff.shift n a)=Coeff.shift (2*n) (Coeff.periodDouble a) := by
  ext j
  by_cases hj : j%2=0
  · have he : j=2*(j/2) := by omega
    rw [he,Coeff.periodDouble_even,Coeff.shift_apply,Coeff.shift_apply,
      show 2*(j/2)-2*n=2*(j/2-n) by ring,Coeff.periodDouble_even]
  · have he : j=2*(j/2)+1 := by omega
    rw [he,Coeff.periodDouble_odd,Coeff.shift_apply,
      show 2*(j/2)+1-2*n=2*(j/2-n)+1 by ring,Coeff.periodDouble_odd]

/-- Source and period-two operator modulations retain their exact factors
of two under the ORIGINAL period-one Fourier insertion. -/
theorem periodOnePotential_spectralModulation (n : ℤ) (φ : CoeffPair p) :
    periodOnePotential (sourceSpectralModulation n φ)=
      pairSpectralModulation (2*n) (periodOnePotential φ) := by
  apply Prod.ext
  · change Coeff.periodDouble (Coeff.shift (-n) φ.fst)=Coeff.shift (-(2*n)) (Coeff.periodDouble φ.fst)
    rw [periodDouble_shift,show 2*(-n)=-(2*n) by ring]
  · exact periodDouble_shift n φ.snd

/-- Every actual source spectral point translates by exactly pi*n under
this norm-preserving real-source modulation. -/
theorem mem_source_periodicSpectrum_spectralModulation (hp : p≠⊤) (n : ℤ)
    (φ : CoeffPair p) (z : ℂ) (hz : z∈periodicSpectrum hp (periodOnePotential φ)) :
    z+(Real.pi : ℂ)*n∈periodicSpectrum hp (periodOnePotential (sourceSpectralModulation n φ)) := by
  rw [periodOnePotential_spectralModulation]
  exact mem_periodicSpectrum_spectralModulation hp n _ z hz

end NLS.ZakharovShabat
