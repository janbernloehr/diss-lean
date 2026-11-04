import NLS.KdV.HillCommonAnalyticCorrectionTail
import NLS.KdV.HillGlobalRegularAnalytic
import NLS.KdV.HillSummedRegularCorrection
import NLS.ComplexAnalysis.NormalAnalyticSeries

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))
include h0q h0r

theorem exists_hillSummedRegularAbelianCorrection_analytic_extension
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 1 ≤ n) :
    ∃ F : Coeff 2 → ℂ, AnalyticAt ℂ F (SpectralWeight.one.toCoeff q) ∧
      ∀ᶠ r : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
        F (SpectralWeight.one.toCoeff r.val)=hillSummedRegularAbelianCorrection r.val r.property.1 r.property.2 n hn := by
  obtain ⟨U,hU,hqU,N,hN,C,hC,β,hβa,hβbound,hβmatch⟩ :=
    exists_hillRegularAbelianCorrection_common_analytic_tail h0q h0r q hq hr n hn
  have hmajor : Summable (fun j : ℕ => C/((j : ℝ)+N)^2) := by
    simpa only [mul_one_div] using (NLS.ReciprocalSeries.summable_nat_reciprocal_sq_tail N hN).mul_left C
  have htailA : AnalyticOnNhd ℂ (fun p => ∑' j : ℕ, β (j+N) p) U :=
    analyticOnNhd_tsum_of_summable_uniform_bound (fun j p => β (j+N) p) U hU
      (fun j => hβa (j+N) (by omega)) _ hmajor
      (fun j p hp => by simpa only [Nat.cast_add] using hβbound p hp (j+N) (by omega))
  have hhead (j : ℕ) := exists_hillRegularAbelianCorrection_analytic_extension q hq hr h0q h0r n (j+1) hn (by omega)
  choose γ hγa hγmatch using hhead
  let F : Coeff 2 → ℂ := fun p => (∑ j ∈ Finset.range (N-1), γ j p)+(∑' j : ℕ, β (j+N) p)
  have hFa : AnalyticAt ℂ F (SpectralWeight.one.toCoeff q) :=
    (Finset.analyticAt_fun_sum _ (fun j _ => hγa j)).add (htailA _ hqU)
  have hheadmatch : ∀ᶠ r : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
      ∀ j ∈ Finset.range (N-1), γ j (SpectralWeight.one.toCoeff r.val)=
        hillRegularAbelianCorrection r.val r.property.1 r.property.2 n hn (j+1) (by omega) := by
    exact (Filter.eventually_all_finset _).mpr (fun j _ => hγmatch j)
  refine ⟨F,hFa,?_⟩
  filter_upwards [hβmatch,hheadmatch] with r hrβ hrγ
  have hsum := Summable.sum_add_tsum_nat_add (N-1)
    (summable_hillRegularAbelianCorrection h0q h0r r.val r.property.1 r.property.2 n hn)
  have htail (j : ℕ) : β (j+N) (SpectralWeight.one.toCoeff r.val)=
      hillRegularAbelianCorrection r.val r.property.1 r.property.2 n hn (j+N) (by omega) := hrβ.2 (j+N) (by omega)
  dsimp only [F]
  rw [Finset.sum_congr rfl hrγ,tsum_congr htail]
  simpa only [hillSummedRegularAbelianCorrection,Nat.add_assoc,Nat.sub_add_cancel hN] using hsum

end NLS.KdV
