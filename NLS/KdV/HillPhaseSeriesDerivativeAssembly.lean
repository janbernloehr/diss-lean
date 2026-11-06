import NLS.KdV.HillPhaseFiniteHead
import NLS.KdV.HillSeparatedPeriodKernel
import NLS.KdV.HillPrimitiveCorrectionMatching
import NLS.KdV.HillPhysicalGermDerivativeUniqueness
import NLS.KdV.HillPrimitivePartialSumVariations
import NLS.SequenceSpaces.FiniteHeadSeries
import NLS.ComplexAnalysis.NormalSeriesDerivatives

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

/-- The actual normally convergent phase assembly inherits the checked
finite physical primitive derivative limit. -/
theorem hillPrimitiveSeries_fderiv_of_normal_tail
    (n N : ℕ) (hn : 1≤n) (hN : 1≤N)
    (U : Set (WeightedCoeff SpectralWeight.one.toWeight 2)) (hU : IsOpen U) (hqU : q∈U)
    (V : Set RealPeriodOneHillPotential) (hV : IsOpen V) (hqV : (⟨q,hq,hr⟩ : RealPeriodOneHillPotential)∈V)
    (β : ℕ → WeightedCoeff SpectralWeight.one.toWeight 2 → ℂ)
    (hβ : ∀ j : ℕ, AnalyticOnNhd ℂ (β j) U)
    (hz : ∀ j : ℕ, ¬(N≤j+1 ∧ j+1≠n) → β j=0)
    (M : ℝ) (hb : ∀ j : ℕ, ∀ p∈U, ‖β j p‖≤M*hillOffDiagonalPeriodKernel n ((j+1 : ℕ) : ℤ))
    (hβreal : ∀ p∈V, ∀ j : ℕ, ∀ _hj : N≤j+1, j+1≠n → β j p.val=
      hillRegularAbelianCorrection p.val p.property.1 p.property.2 n hn (j+1) (by omega))
    (B ε : ℕ → Coeff 2 → ℂ)
    (hB : ∀ j : ℕ, AnalyticAt ℂ (B j) (SpectralWeight.one.toCoeff q))
    (hmatch : ∀ j : ℕ, ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
      B j (SpectralWeight.one.toCoeff p.val)=hillRegularAbelianCorrection p.val p.property.1 p.property.2 n hn (j+1) (by omega)+
        (if j+1=n then 1 else 0)*(ε j (SpectralWeight.one.toCoeff p.val)-(Real.pi : ℂ)))
    (hpartial : ∀ k : ℕ, ∀ hk : 1≤k,
      Tendsto (fun K => (fderiv ℂ (fun p : Coeff 2 => ∑ j∈Finset.range K,B j p) (SpectralWeight.one.toCoeff q))
        (SpectralWeight.one.toCoeff (hillPhysicalMomentHamiltonianSource q hq hr k hk 0)))
        atTop (𝓝 (-(if k=n then 1 else 0 : ℂ)))) :
    let A : WeightedCoeff SpectralWeight.one.toWeight 2 → ℂ :=
      fun p => ∑ j∈hillPhaseFiniteHead N n,B j (SpectralWeight.one.toCoeff p)
    AnalyticAt ℂ (fun p => A p+∑' j : ℕ,β j p) q ∧
      ∀ k : ℕ, ∀ hk : 1≤k,
        (fderiv ℂ (fun p => A p+∑' j : ℕ,β j p) q) (hillPhysicalMomentHamiltonianSource q hq hr k hk 0)=
          -(if k=n then 1 else 0 : ℂ) := by
  intro A
  let J := hillPhaseFiniteHead N n
  let C : ℕ → WeightedCoeff SpectralWeight.one.toWeight 2 → ℂ := fun j p => B j (SpectralWeight.one.toCoeff p)
  have hC (j : ℕ) : AnalyticAt ℂ (C j) q := (hB j).comp (SpectralWeight.one.toCoeff.analyticAt q)
  have hA : AnalyticAt ℂ A q := Finset.analyticAt_fun_sum _ (fun j _ => hC j)
  have hs : Summable (fun j : ℕ => M*hillOffDiagonalPeriodKernel n ((j+1 : ℕ) : ℤ)) :=
    ((summable_hillOffDiagonalPeriodKernel n).comp_injective (show Function.Injective (fun j : ℕ => ((j+1 : ℕ) : ℤ)) by
      intro i j hij
      exact Nat.add_right_cancel (Int.ofNat_injective hij))).mul_left M
  have hS := analyticOnNhd_tsum_of_summable_uniform_bound β U hU hβ _ hs hb
  refine ⟨hA.add (hS q hqU),?_⟩
  intro k hk
  let h := hillPhysicalMomentHamiltonianSource q hq hr k hk 0
  have heven : SpectralWeight.one.toCoeff h∈Coeff.paritySubspace 0 :=
    hillEnergyContourHamiltonianSource_mem_even _ _ _ _ _ _
  have hderC (j : ℕ) : (fderiv ℂ (C j) q) h=
      (fderiv ℂ (B j) (SpectralWeight.one.toCoeff q)) (SpectralWeight.one.toCoeff h) := by
    have hd := (hB j).differentiableAt.hasFDerivAt.comp q SpectralWeight.one.toCoeff.hasFDerivAt
    change HasFDerivAt (𝕜 := ℂ) (C j) _ q at hd
    rw [hd.fderiv]
    rfl
  have hderβ (j : ℕ) (hj : j∉J) : (fderiv ℂ (β j) q) h=(fderiv ℂ (C j) q) h := by
    have hactive : N≤j+1 ∧ j+1≠n := by
      have hh := (mem_hillPhaseFiniteHead N n hN hn j).not.mp hj
      omega
    apply hillPhysicalGerm_fderiv_eq_of_eventuallyEq q hq hr (β j) (C j) (hβ j q hqU) (hC j) ?_ h heven
    filter_upwards [hV.mem_nhds hqV,hmatch j] with p hpV hpj
    rw [hβreal p hpV j hactive.1 hactive.2]
    change _=B j (SpectralWeight.one.toCoeff p.val)
    rw [hpj,if_neg hactive.2,zero_mul,add_zero]
  have hzero (j : ℕ) (hj : j∈J) : (fderiv ℂ (β j) q) h=0 := by
    have hh := (mem_hillPhaseFiniteHead N n hN hn j).mp hj
    have hnact : ¬(N≤j+1 ∧ j+1≠n) := by omega
    rw [hz j hnact]
    simp
  have hfinite (K : ℕ) (hK : max N n≤K) :
      (fderiv ℂ (fun p => A p+∑ j∈Finset.range K,β j p) q) h=
        (fderiv ℂ (fun p : Coeff 2 => ∑ j∈Finset.range K,B j p) (SpectralWeight.one.toCoeff q)) (SpectralWeight.one.toCoeff h) := by
    have htail : AnalyticAt ℂ (fun p => ∑ j∈Finset.range K,β j p) q :=
      Finset.analyticAt_fun_sum _ (fun j _ => hβ j q hqU)
    rw [fderiv_fun_add hA.differentiableAt htail.differentiableAt]
    simp only [add_apply]
    change (fderiv ℂ (fun p => ∑ j∈J,C j p) q) h+_=_
    rw [fderiv_fun_sum (fun j _ => (hC j).differentiableAt),
      fderiv_fun_sum (fun j _ => (hβ j q hqU).differentiableAt),
      fderiv_fun_sum (fun j _ => (hB j).differentiableAt)]
    simp only [sum_apply]
    rw [sum_head_add_sum_range_of_zero_on_head (fun j => (fderiv ℂ (β j) q) h)
      (fun j => (fderiv ℂ (C j) q) h) J K (hillPhaseFiniteHead_subset_range N n K hN hK) hzero hderβ]
    exact Finset.sum_congr rfl (fun j _ => hderC j)
  have hd := tendsto_fderiv_add_sum_range_of_summable_uniform_bound A β U hU hβ _ hs hb q hqU hA
  have heval := (ContinuousLinearMap.apply ℂ ℂ h).continuous.tendsto
    (fderiv ℂ (fun p => A p+∑' j : ℕ,β j p) q)
  have hactual := (hpartial k hk).congr' (by
    filter_upwards [eventually_ge_atTop (max N n)] with K hK
    exact (hfinite K hK).symm)
  exact tendsto_nhds_unique (heval.comp hd) hactual

end NLS.KdV
