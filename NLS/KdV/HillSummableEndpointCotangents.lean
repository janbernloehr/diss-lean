import NLS.KdV.HillCommonEndpointCotangentTail
import NLS.KdV.HillAllEndpointRegularCotangents
import NLS.SequenceSpaces.ReciprocalSquareTail
import NLS.KdV.HillNormingTransversePairing

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.ZakharovShabat NLS.FunctionalAnalysis
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))
include h0q h0r

/-- At an all-periodic source all genuine physical correction germs can be
chosen with absolutely summable norming coefficients. The analytic tail is
uniform on one complex source neighborhood. -/
theorem exists_hillRegularCorrections_summable_endpoint_cotangents
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1≤n)
    (hterminal : ∀ k : ℕ, ∀ hk : 1≤k,
      hillDirichletLogMultiplier q.val q.property.1 q.property.2 k hk=0) :
    ∃ γ : ℕ → Coeff 2 → ℂ, ∃ c : ℕ → ℂ,
      (∀ j : ℕ, AnalyticAt ℂ (γ j) (SpectralWeight.one.toCoeff q.val) ∧
        (∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
          γ j (SpectralWeight.one.toCoeff p.val)=hillRegularAbelianCorrection
            p.val p.property.1 p.property.2 n hn (j+1) (by omega)) ∧
        ∀ h : WeightedCoeff SpectralWeight.one.toWeight 2,
          SpectralWeight.one.toCoeff h∈Coeff.paritySubspace 0 →
          (fderiv ℂ (γ j) (SpectralWeight.one.toCoeff q.val)) (SpectralWeight.one.toCoeff h)=
            c j*hillPhysicalDirectionPairing (SpectralWeight.one.toCoeff h)
              (hillLogNormingGradientCurve q (j+1) (by omega))) ∧
      Summable (fun j : ℕ => ‖c j‖) ∧
      ∃ U : Set (Coeff 2), IsOpen U ∧ SpectralWeight.one.toCoeff q.val∈U ∧
        ∃ J : ℕ, ∃ C : ℝ, 0<C ∧
          (∀ j : ℕ, J≤j → AnalyticOnNhd ℂ (γ j) U) ∧
          (∀ p∈U, ∀ j : ℕ, J≤j → ‖γ j p‖≤C/((j : ℝ)+1)^2) ∧
          ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
            SpectralWeight.one.toCoeff p.val∈U ∧ ∀ j : ℕ, J≤j →
              γ j (SpectralWeight.one.toCoeff p.val)=hillRegularAbelianCorrection
                p.val p.property.1 p.property.2 n hn (j+1) (by omega) := by
  obtain ⟨U,hU,hqU,N,hN,C,hC,A,hA,β,hβa,hβbound,hβmatch,hβD⟩ :=
    exists_hillRegularAbelianCorrection_common_endpoint_cotangent_tail h0q h0r
      q.val q.property.1 q.property.2 n hn
  have hex (k : ℕ) (hk : N≤k) := hβD k hk (hterminal k (hN.trans hk))
  choose ct hct hDt using hex
  have hhead (j : ℕ) := exists_hillRegularAbelianCorrection_endpoint_norming_cotangent h0q h0r
    q n (j+1) hn (by omega) (hterminal (j+1) (by omega))
  choose α ch hαa hαmatch hαD using hhead
  let γ : ℕ → Coeff 2 → ℂ := fun j => if _hj : N≤j+1 then β (j+1) else α j
  let c : ℕ → ℂ := fun j => if hj : N≤j+1 then ct (j+1) hj else ch j
  refine ⟨γ,c,?_,?_,U,hU,hqU,N,C,hC,?_,?_,?_⟩
  · intro j
    by_cases hj : N≤j+1
    · refine ⟨?_,?_,?_⟩
      · simpa only [γ,dif_pos hj] using hβa (j+1) hj _ hqU
      · filter_upwards [hβmatch] with p hp
        simpa only [γ,dif_pos hj] using hp.2 (j+1) hj
      · intro h _
        simpa only [γ,c,dif_pos hj] using hDt (j+1) hj (SpectralWeight.one.toCoeff h)
    · simpa only [γ,c,dif_neg hj] using ⟨hαa j,hαmatch j,hαD j⟩
  · have hs : Summable (fun j : ℕ => A/((j : ℝ)+1)^2) := by
      simpa only [mul_one_div,Nat.cast_one] using
        (NLS.ReciprocalSeries.summable_nat_reciprocal_sq_tail 1 (by omega)).mul_left A
    apply hs.of_norm_bounded_eventually_nat
    filter_upwards [eventually_ge_atTop N] with j hj
    have hj' : N≤j+1 := by omega
    simpa only [c,dif_pos hj',norm_norm,Nat.cast_add,Nat.cast_one] using hct (j+1) hj'
  · intro j hj
    have hj' : N≤j+1 := by omega
    simpa only [γ,dif_pos hj'] using hβa (j+1) hj'
  · intro p hp j hj
    have hj' : N≤j+1 := by omega
    simpa only [γ,dif_pos hj',Nat.cast_add,Nat.cast_one] using hβbound p hp (j+1) hj'
  · filter_upwards [hβmatch] with p hp
    refine ⟨hp.1,?_⟩
    intro j hj
    have hj' : N≤j+1 := by omega
    simpa only [γ,dif_pos hj'] using hp.2 (j+1) hj'

/-- Absolute summability is intrinsic to every physically matched analytic
correction family and its genuine norming-span coefficients. -/
theorem hillRegularCorrectionGerms_endpoint_coefficients_summable
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1≤n)
    (hterminal : ∀ k : ℕ, ∀ hk : 1≤k,
      hillDirichletLogMultiplier q.val q.property.1 q.property.2 k hk=0)
    (G : ℕ → Coeff 2 → ℂ) (c : ℕ → ℂ)
    (hG : ∀ j : ℕ, AnalyticAt ℂ (G j) (SpectralWeight.one.toCoeff q.val))
    (hphysical : ∀ j : ℕ, ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      G j (SpectralWeight.one.toCoeff p.val)=hillRegularAbelianCorrection
        p.val p.property.1 p.property.2 n hn (j+1) (by omega))
    (hD : ∀ j : ℕ, ∀ h : WeightedCoeff SpectralWeight.one.toWeight 2,
      SpectralWeight.one.toCoeff h∈Coeff.paritySubspace 0 →
      (fderiv ℂ (G j) (SpectralWeight.one.toCoeff q.val)) (SpectralWeight.one.toCoeff h)=
        c j*hillPhysicalDirectionPairing (SpectralWeight.one.toCoeff h)
          (hillLogNormingGradientCurve q (j+1) (by omega))) :
    Summable (fun j : ℕ => ‖c j‖) := by
  obtain ⟨γ,d,hγ,hs,_⟩ := exists_hillRegularCorrections_summable_endpoint_cotangents h0q h0r q n hn hterminal
  have heq (j : ℕ) : c j=d j := by
    have hmatch : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
        G j (SpectralWeight.one.toCoeff p.val)=γ j (SpectralWeight.one.toCoeff p.val) := by
      filter_upwards [hphysical j,(hγ j).2.1] with p hpG hpγ
      exact hpG.trans hpγ.symm
    rw [hillNormingCotangent_coefficient_eq_transverse_derivative q (j+1) (by omega) (G j) (c j) (hD j),
      hillNormingCotangent_coefficient_eq_transverse_derivative q (j+1) (by omega) (γ j) (d j) (hγ j).2.2]
    congr 1
    exact hillPhysicalCoefficientGerm_fderiv_eq_of_eventuallyEq q.val q.property.1 q.property.2
      (G j) (γ j) (hG j) (hγ j).1 hmatch
      (hillDirichletHamiltonianSource q (j+1) (by omega))
      (hillDirichletHamiltonianSource_mem_even q (j+1) (by omega))
  simpa only [heq] using hs

end NLS.KdV
