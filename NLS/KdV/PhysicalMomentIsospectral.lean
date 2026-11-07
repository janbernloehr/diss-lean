import NLS.KdV.PhysicalOffDiagonalIsospectral

/-! All actual signed moments and the full physical correction are
spectral invariants on the real slice of a fixed Miura chart. -/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.ZakharovShabat
namespace NLS.KdV.PhysicalMiuraFrequencyChart

theorem moment_eq_of_discriminant_eq (B : PhysicalMiuraFrequencyChart)
    (q p : PeriodOneHminusOne) (hq : q∈B.domain) (hp : p∈B.domain)
    (hqr : IsRealPeriodOneHminusOne q) (hpr : IsRealPeriodOneHminusOne p)
    (hD : hillHminusDiscriminant p=hillHminusDiscriminant q) (n k : ℤ) (m : ℕ) :
    B.atlas.moment n k m (B.psi.miura.criticalSource p)=
      B.atlas.moment n k m (B.psi.miura.criticalSource q) := by
  have hqC := (B.domain_subset hq).1
  have hpC := (B.domain_subset hp).1
  have hqreal := isRealType_hillMiuraDiagonal ⟨B.psi.miura.lift q,B.real_lift q hqC hqr⟩
  have hpreal := isRealType_hillMiuraDiagonal ⟨B.psi.miura.lift p,B.real_lift p hpC hpr⟩
  let φ : realTypeSourceSubmodule 2 := ⟨B.psi.miura.criticalSource q,hqreal⟩
  let ψ : realTypeSourceSubmodule 2 := ⟨B.psi.miura.criticalSource p,hpreal⟩
  have hi := hillHminusMiuraSource_isospectral_of_discriminant_eq B.psi.miura q p hqC hpC hqreal hpreal hD
  exact B.atlas.moment_real_eq_of_calibrated_roots B.atlas B.psi.family.verified.real_agreement
    B.psi.family.verified.real_agreement φ ψ hi n k m

theorem correction_eq_of_discriminant_eq (B : PhysicalMiuraFrequencyChart)
    (q p : PeriodOneHminusOne) (hq : q∈B.domain) (hp : p∈B.domain)
    (hqr : IsRealPeriodOneHminusOne q) (hpr : IsRealPeriodOneHminusOne p)
    (hD : hillHminusDiscriminant p=hillHminusDiscriminant q) (n : ℕ+) :
    B.correction n p=B.correction n q := by
  unfold correction SourceAbelianMomentAtlas.weightedSecondMomentSum
  apply congrArg (fun z : ℂ => -12*z)
  exact tsum_congr (fun k => congrArg (fun z : ℂ => (k : ℂ)*z)
    (B.moment_eq_of_discriminant_eq q p hq hp hqr hpr hD (n : ℤ) k 2))

end NLS.KdV.PhysicalMiuraFrequencyChart
