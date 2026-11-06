import NLS.KdV.HillHminusSobolevEtaGerms
import NLS.KdV.HillHminusStrongMiuraCharts

/-! # One actual rough Hill chart with all native weighted eta germs

At every real rough base, the actual Miura chart, original psi family and
energy translation precede ALL Sobolev orders and all eligible real
sources. Each such source has an open COMPLEX native neighborhood carrying
the actual weighted eta sequence analytically, with one bound before all
signed output indices. Original positive Hill labels are retained.
-/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.KdV

/-- At EVERY real rough Hill base, ONE chart retains the actual original
positive labels and has complex Sobolev-valued eta germs at ALL eligible
real sources, for ALL s>=-1, using the SAME root family and lift. -/
theorem exists_hillHminus_all_sobolev_eta_charts
    (q0 : PeriodOneHminusOne) (hr0 : IsRealPeriodOneHminusOne q0) :
    ∃ P : HillHminusPsiChart, ∃ c : ℝ,
      0<c ∧ P.miura.energyShift=(c : ℂ)^2 ∧ q0∈P.sourceBetaDomain ∧
      (∀ q∈P.miura.domain, IsRealPeriodOneHminusOne q →
        periodOneL2Conjugation (P.miura.lift q)=P.miura.lift q) ∧
      (∀ q∈P.miura.domain, hillHminusRadicand q (-P.miura.energyShift)≠0) ∧
      (∀ q∈P.miura.domain, ∀ hr : IsRealPeriodOneHminusOne q, ∀ n : ℕ, 0<n →
        hillHminusRealLabels q hr (2*n-1)=(hillMiuraDiracLeft (P.miura.lift q) n).re^2-c^2 ∧
        hillHminusRealLabels q hr (2*n)=(hillMiuraDiracRight (P.miura.lift q) n).re^2-c^2) ∧
      ∃ _H : SourceLemma12_12Data (by norm_num) (by norm_num)
        P.family.originalDomain P.family.domain P.family.roots,
      ∀ t : ℝ, ∀ ht : 0≤t, ∀ q : WeightedCoeff (Weight.sobolev (t-1)) 2,
        IsRealPeriodOneHminusOne (periodOneSobolevImageInclusion t ht q) →
        periodOneSobolevImageInclusion t ht q∈P.miura.domain →
        ∃ V : Set (WeightedCoeff (Weight.sobolev (t-1)) 2), IsOpen V ∧ q∈V ∧
          ∃ M : ℝ, ∃ E : WeightedCoeff (Weight.sobolev (t-1)) 2 → Coeff 2,
            0≤M ∧ AnalyticOnNhd ℂ E V ∧ ∀ p∈V,
              periodOneSobolevImageInclusion t ht p∈P.sourceBetaDomain ∧ ‖E p‖≤M ∧
              ∀ n : ℤ, E p n=(Weight.sobolev t n : ℂ)*
                P.sourceEtaSequence (periodOneSobolevImageInclusion t ht p) n := by
  obtain ⟨C,c,hc,hshift,hqC,hreal,houtside,hlabels,hstrong⟩ :=
    exists_hillHminus_real_Miura_all_strong_sobolev_chart q0 hr0
  obtain ⟨A,H⟩ := exists_miuraHillPsiFamily_with_original_estimates
  let P : HillHminusPsiChart := ⟨C,A⟩
  have real_mem (q : PeriodOneHminusOne) (hq : q∈C.domain)
      (hr : IsRealPeriodOneHminusOne q) : q∈P.sourceBetaDomain := by
    have hu := (periodOneL2Conjugation_fixed_iff _).mp (hreal q hq hr)
    have hp : q∈P.source := ⟨hq,A.real_mem_source ⟨C.lift q,hu⟩⟩
    exact P.mem_sourceBetaDomain_of_real q hp hu
  refine ⟨P,c,hc,hshift,real_mem q0 hqC hr0,hreal,houtside,hlabels,H,?_⟩
  intro t ht q hr hq
  exact P.exists_native_sobolev_eta_germ H t ht q
    (real_mem _ hq hr) (hreal _ hq hr) (hstrong t ht q hq)

end NLS.KdV
