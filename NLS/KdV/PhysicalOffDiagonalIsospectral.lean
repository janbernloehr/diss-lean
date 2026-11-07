import NLS.KdV.PhysicalOffDiagonalFrequency
import NLS.KdV.HillHminusOneMiuraSpectralInvariance
import NLS.ZakharovShabat.SourceCalibratedMomentIsospectral

/-! The actual paired off-diagonal correction is a spectral invariant
on the entire real slice of one fixed physical Miura chart. -/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.ZakharovShabat
namespace NLS.KdV.PhysicalMiuraFrequencyChart

theorem offDiagonalCorrection_eq_of_discriminant_eq (B : PhysicalMiuraFrequencyChart)
    (q p : PeriodOneHminusOne) (hq : q∈B.domain) (hp : p∈B.domain)
    (hqr : IsRealPeriodOneHminusOne q) (hpr : IsRealPeriodOneHminusOne p)
    (hD : hillHminusDiscriminant p=hillHminusDiscriminant q) (n : ℕ+) :
    B.offDiagonalCorrection n p=B.offDiagonalCorrection n q := by
  have hqC := (B.domain_subset hq).1
  have hpC := (B.domain_subset hp).1
  have hqreal := isRealType_hillMiuraDiagonal ⟨B.psi.miura.lift q,B.real_lift q hqC hqr⟩
  have hpreal := isRealType_hillMiuraDiagonal ⟨B.psi.miura.lift p,B.real_lift p hpC hpr⟩
  let φ : realTypeSourceSubmodule 2 := ⟨B.psi.miura.criticalSource q,hqreal⟩
  let ψ : realTypeSourceSubmodule 2 := ⟨B.psi.miura.criticalSource p,hpreal⟩
  have hi := hillHminusMiuraSource_isospectral_of_discriminant_eq B.psi.miura q p hqC hpC hqreal hpreal hD
  have hm (j k : ℤ) (m : ℕ) : B.atlas.moment j k m ψ.val=B.atlas.moment j k m φ.val :=
    B.atlas.moment_real_eq_of_calibrated_roots B.atlas B.psi.family.verified.real_agreement
      B.psi.family.verified.real_agreement φ ψ hi j k m
  have hs : B.atlas.weightedSecondMomentSum (n : ℤ) ψ.val=
      B.atlas.weightedSecondMomentSum (n : ℤ) φ.val := by
    unfold SourceAbelianMomentAtlas.weightedSecondMomentSum
    exact tsum_congr (fun k => congrArg (fun z : ℂ => (k : ℂ)*z) (hm (n : ℤ) k 2))
  change -12*(B.atlas.weightedSecondMomentSum (n : ℤ) ψ.val-
    (n : ℂ)*(B.atlas.moment (n : ℤ) (n : ℤ) 2 ψ.val-B.atlas.moment (n : ℤ) (-(n : ℤ)) 2 ψ.val))=_
  rw [hs,hm (n : ℤ) (n : ℤ) 2,hm (n : ℤ) (-(n : ℤ)) 2]
  rfl

end NLS.KdV.PhysicalMiuraFrequencyChart
