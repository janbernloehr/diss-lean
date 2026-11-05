import NLS.MKdV.QuasiHillMonodromyEnergy
import NLS.MKdV.MiuraHillDirichletComparison
import NLS.MKdV.MiuraHillDirichletPositivity
import NLS.KdV.HillOpenEndpointTraceDerivative

/-! # Nontrivial parabolic monodromy at actual open Miura endpoints

The actual Hill endpoint multiplicity and literal operator comparison
discharge the parabolic and nonzero lower-entry hypotheses. All positive
gap indices and every original real H¹ profile are included.
-/
noncomputable section
open Set Complex Matrix NLS.LinearVolterra NLS.ZakharovShabat NLS.KdV
open scoped ComplexConjugate
namespace NLS.MKdV

theorem miuraQuasiHillDiscriminant_open_endpoint
    (a : ScalarDomain 2) (ha : ∀ m,a.val m = conj (a.val (-m)))
    (k : ℕ) (hk : 1 ≤ k)
    (hgap : miuraHillLabels a ha (2*k-1) ≠ miuraHillLabels a ha (2*k))
    (E : ℂ) (hE : E = (miuraHillLabels a ha (2*k-1) : ℂ) ∨
      E = (miuraHillLabels a ha (2*k) : ℂ)) :
    quasiHillDiscriminant (periodOneMiuraCurve a) E = 2*(-1:ℂ)^k ∧
      deriv (quasiHillDiscriminant (periodOneMiuraCurve a)) E ≠ 0 := by
  let q := realSobolevMiuraHillPotential a ha
  have he : E = (hillRealLabels q.val q.property.1 q.property.2 (2*k-1) : ℂ) ∨
      E = (hillRealLabels q.val q.property.1 q.property.2 (2*k) : ℂ) := hE
  have hhalf : hillRealGapHalfLength q.val q.property.1 q.property.2 k ≠ 0 := by
    intro hz
    have hsub : hillRealLabels q.val q.property.1 q.property.2 (2*k)-
        hillRealLabels q.val q.property.1 q.property.2 (2*k-1) = 0 :=
      (div_eq_zero_iff).mp hz |>.resolve_right (by norm_num)
    exact hgap (sub_eq_zero.mp hsub).symm
  have hfun : hillL2Discriminant (SpectralWeight.one.toCoeff q.val) =
      quasiHillDiscriminant (periodOneMiuraCurve a) := by
    funext w
    rw [realSobolevMiuraHillPotential_toCoeff]
    exact hillL2Discriminant_miura a w
  constructor
  · rw [← hfun]
    have ht := hillRealLabels_pair_trace q.val q.property.1 q.property.2 k hk
    rcases he with rfl | rfl
    · exact ht.1
    · exact ht.2
  · rw [← hfun]
    exact deriv_hillL2Discriminant_ne_zero_open_gap_endpoint q.val q.property.1 q.property.2 k hk hhalf E he

theorem miuraQuasiHillMonodromy_open_Dirichlet_endpoint
    (a : ScalarDomain 2) (ha : ∀ m,a.val m = conj (a.val (-m)))
    (k : ℕ) (hk : 1 ≤ k)
    (hgap : miuraHillLabels a ha (2*k-1) ≠ miuraHillLabels a ha (2*k))
    (E : ℂ) (hE : E = (miuraHillLabels a ha (2*k-1) : ℂ) ∨
      E = (miuraHillLabels a ha (2*k) : ℂ))
    (hD : hillL2DirichletCharacteristic (sobolevMiuraHillPotential a) E = 0) :
    ∃ c : ℂ,c ≠ 0 ∧ quasiHillFundamentalMatrix (periodOneMiuraCurve a) E 1 =
      !![(-1:ℂ)^k,0;c,(-1:ℂ)^k] := by
  have ht := miuraQuasiHillDiscriminant_open_endpoint a ha k hk hgap E hE
  rw [hillL2DirichletCharacteristic_miura] at hD
  have hε : ((-1:ℂ)^k)^2 = 1 := by
    rw [← pow_mul,Nat.mul_comm k 2,pow_mul]
    norm_num
  exact ⟨_,quasiHillMonodromy_lower_ne_zero_of_Dirichlet_trace_deriv
    (periodOneMiuraCurve a) E ((-1)^k) hε hD ht.1 ht.2,
    quasiHillMonodromy_parabolic_of_Dirichlet_trace (periodOneMiuraCurve a) E ((-1)^k) hε hD ht.1⟩

end NLS.MKdV
