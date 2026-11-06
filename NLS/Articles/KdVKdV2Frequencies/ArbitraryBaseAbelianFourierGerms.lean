import NLS.Articles.KdVKdV2Frequencies.ArbitraryBaseAbelianFourierData
import NLS.KdV.HillHminusSobolevAbelianFourierPrincipal

/-! # Actual all-order Abelian packet germs with their Fourier principal -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies.RoughAbelianFourierDataAt
open NLS.KdV
variable {q0 : PeriodOneHminusOne}

/-- For the SAME full actual packet, EVERY eligible real native source
has a complex analytic Sobolev germ. At EVERY real source in that germ,
its derivative has the literal full Fourier principal plus compact.
The ONE actual chart and uniformly invertible positive symbol precede
all orders, bases and output indices. -/
theorem exists_native_packet_fourier_germ
    (D : RoughAbelianFourierDataAt q0) (t : ℝ) (ht : 0≤t)
    (q : WeightedCoeff (Weight.sobolev (t-1)) 2)
    (hqr : IsRealPeriodOneHminusOne (periodOneSobolevImageInclusion t ht q))
    (hq : periodOneSobolevImageInclusion t ht q∈ball q0 D.radius) :
    ∃ V : Set (WeightedCoeff (Weight.sobolev (t-1)) 2), IsOpen V ∧ q∈V ∧
      ∃ M : ℝ, ∃ E : WeightedCoeff (Weight.sobolev (t-1)) 2 → Coeff 2,
        0≤M ∧ AnalyticOnNhd ℂ E V ∧ ∀ p∈V,
          periodOneSobolevImageInclusion t ht p∈ball q0 D.radius ∧ ‖E p‖≤M ∧
          (∀ n : ℤ, E p n=(Weight.sobolev t n : ℂ)*D.packet (periodOneSobolevImageInclusion t ht p) n) ∧
          (IsRealPeriodOneHminusOne (periodOneSobolevImageInclusion t ht p) →
            IsCompactOperator (fderiv ℂ E p-D.chart.nativeAbelianFourierPrincipal D.symbol t ht p)) := by
  have hqB := D.source_domain hq
  have hreal := D.real_lift _ hqB.1.1 hqr
  have heta := D.chart.exists_native_sobolev_eta_germ D.roots t ht q hqB hreal
    (D.native_lifts t ht q hqB.1.1)
  obtain ⟨V,hV,hqV,M,F,E,hM,hFa,hEa,hdata⟩ :=
    D.chart.exists_sobolev_abelian_symbol_packet_compact_germ D.symbol
      (ball q0 D.radius) isOpen_ball D.symbol_analytic
      D.symbol_upper D.upper_pos.le (fun p hp => (D.symbol_data p hp).1) t ht q hq heta
  refine ⟨V,hV,hqV,M,E,hM,hEa,?_⟩
  intro p hp
  obtain ⟨hpD,hEb,hFcoeff,hEcoeff,hEc⟩ := hdata p hp
  refine ⟨hpD.2,hEb,?_,?_⟩
  · intro n
    rw [hEcoeff n,(D.packet_data _ hpD.2).1]
  · intro hpr
    exact D.chart.isCompactOperator_native_abelian_derivative_sub_fourier D.roots D.native_lifts
      D.symbol t ht V hV F E (fun a ha => ⟨(hdata a ha).1.1,(hdata a ha).2.2.1⟩)
      p hp (D.real_lift _ hpD.1.1.1 hpr) hEc

end NLS.Articles.KdVKdV2Frequencies.RoughAbelianFourierDataAt
