import NLS.KdV.HillGardnerOpenCorrection
import NLS.KdV.HillSummedRegularCorrectionAnalytic
import NLS.KdV.HillDirichletInterpolation
import NLS.ComplexAnalysis.NormalAnalyticSeriesDerivative

/-! # Source derivative of the actual infinite regular correction -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical
namespace NLS.KdV
private theorem tendsto_sub_single_sum (u : ℕ → ℂ) (n : ℕ) (hn : 1≤n) (Z l : ℂ)
    (hu : Tendsto (fun M => ∑ j ∈ Finset.range M, u j) atTop (𝓝 l)) :
    Tendsto (fun M => ∑ j ∈ Finset.range M, (u j-(if j+1=n then 1 else 0)*Z)) atTop (𝓝 (l-Z)) := by
  apply (hu.sub tendsto_const_nhds).congr'
  filter_upwards [eventually_ge_atTop n] with M hM
  rw [Finset.sum_sub_distrib]
  congr 1
  have he (j : ℕ) : j+1=n ↔ j=n-1 := by omega
  simp_rw [ite_mul,one_mul,zero_mul,he]
  simp only [Finset.sum_ite_eq',Finset.mem_range,show n-1<M by omega,if_true]

variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))
include h0q h0r

/-- A genuine analytic extension of the absolutely convergent physical
regular correction sum has its source derivative evaluated by the filled
Dirichlet interpolation formula. -/
theorem exists_hillSummedRegularAbelianCorrection_gardner_variation
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 1 ≤ n)
    (hnopen : hillRealGapHalfLength q hq hr n≠0) :
    ∃ F : Coeff 2 → ℂ, AnalyticAt ℂ F (SpectralWeight.one.toCoeff q) ∧
      (∀ b : ℂ, (fderiv ℂ F (SpectralWeight.one.toCoeff q))
        (hillL2DiscriminantGardnerDirection (SpectralWeight.one.toCoeff q) b) =
        -hillAbelianSelectedGlobalPsi q hq hr n hn b/2 -
          I*hillDeflatedEnergyCanonicalRoot q hq hr n (hillDirichletEnergy q hq hr n hn)*
            hillDirichletGardnerKernel (⟨q,hq,hr⟩ : RealPeriodOneHillPotential) n hn b) ∧
      ∀ᶠ r : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
        F (SpectralWeight.one.toCoeff r.val)=hillSummedRegularAbelianCorrection r.val r.property.1 r.property.2 n hn := by
  obtain ⟨U,hU,hqU,N,hN,C,hC,β,hβa,hβbound,hβmatch⟩ :=
    exists_hillRegularAbelianCorrection_common_analytic_tail h0q h0r q hq hr n hn
  have hmajor : Summable (fun j : ℕ => C/((j : ℝ)+N)^2) := by
    simpa only [mul_one_div] using (NLS.ReciprocalSeries.summable_nat_reciprocal_sq_tail N hN).mul_left C
  have hbound (j : ℕ) (p : Coeff 2) (hp : p∈U) : ‖β (j+N) p‖≤C/((j:ℝ)+N)^2 := by
    simpa only [Nat.cast_add] using hβbound p hp (j+N) (by omega)
  have htailA : AnalyticOnNhd ℂ (fun p => ∑' j : ℕ, β (j+N) p) U :=
    analyticOnNhd_tsum_of_summable_uniform_bound (fun j p => β (j+N) p) U hU
      (fun j => hβa (j+N) (by omega)) _ hmajor hbound
  have hhead (j : ℕ) := exists_hillRegularAbelianCorrection_analytic_extension q hq hr h0q h0r n (j+1) hn (by omega)
  choose γ hγa hγmatch using hhead
  let F : Coeff 2 → ℂ := fun p => (∑ j ∈ Finset.range (N-1), γ j p)+(∑' j : ℕ, β (j+N) p)
  have hFa : AnalyticAt ℂ F (SpectralWeight.one.toCoeff q) :=
    (Finset.analyticAt_fun_sum _ (fun j _ => hγa j)).add (htailA _ hqU)
  have hheadmatch : ∀ᶠ r : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
      ∀ j ∈ Finset.range (N-1), γ j (SpectralWeight.one.toCoeff r.val)=
        hillRegularAbelianCorrection r.val r.property.1 r.property.2 n hn (j+1) (by omega) := by
    exact (Filter.eventually_all_finset _).mpr (fun j _ => hγmatch j)
  refine ⟨F,hFa,?_,?_⟩
  · intro b
    let a := SpectralWeight.one.toCoeff q
    let v := hillL2DiscriminantGardnerDirection a b
    let Z := I*hillDeflatedEnergyCanonicalRoot q hq hr n (hillDirichletEnergy q hq hr n hn)*
      hillDirichletGardnerKernel (⟨q,hq,hr⟩ : RealPeriodOneHillPotential) n hn b
    let R : ℕ → ℂ := fun j =>
      hillAbelianSelectedGlobalPsi q hq hr n hn (hillDirichletEnergy q hq hr (j+1) (by omega))*
        hillDirichletGardnerKernel (⟨q,hq,hr⟩ : RealPeriodOneHillPotential) (j+1) (by omega) b -
          (if j+1=n then 1 else 0)*Z
    have hγD (j : ℕ) : (fderiv ℂ (γ j) a) v=R j :=
      fderiv_hillRegularAbelianCorrection_extension q hq hr h0q h0r n (j+1) hn (by omega) hnopen
        (γ j) (hγa j).differentiableAt (hγmatch j) b
    have hβD (j : ℕ) : (fderiv ℂ (β (j+N)) a) v=R (j+(N-1)) := by
      have hm : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
          β (j+N) (SpectralWeight.one.toCoeff p.val)=
            hillRegularAbelianCorrection p.val p.property.1 p.property.2 n hn (j+N) (by omega) :=
        hβmatch.mono (fun _ hp => hp.2 (j+N) (by omega))
      have hh := fderiv_hillRegularAbelianCorrection_extension q hq hr h0q h0r n (j+N) hn (by omega) hnopen
        (β (j+N)) (hβa (j+N) (by omega) _ hqU).differentiableAt hm b
      have he : j+(N-1)+1=j+N := by omega
      simpa only [R,he] using hh
    have htailD := tendsto_fderiv_sum_apply_of_summable_uniform_bound
      (fun j p => β (j+N) p) U hU (fun j => hβa (j+N) (by omega)) _ hmajor hbound a hqU v
    have hDF : fderiv ℂ F a = (∑ j ∈ Finset.range (N-1), fderiv ℂ (γ j) a)+
        fderiv ℂ (fun p => ∑' j : ℕ, β (j+N) p) a :=
      ((HasFDerivAt.fun_sum (fun j _ => (hγa j).differentiableAt.hasFDerivAt)).add
        (htailA a hqU).differentiableAt.hasFDerivAt).fderiv
    have hpartial : Tendsto (fun L => (∑ j ∈ Finset.range (N-1), (fderiv ℂ (γ j) a) v)+
        (∑ j ∈ Finset.range L, (fderiv ℂ (β (j+N)) a) v)) atTop (𝓝 ((fderiv ℂ F a) v)) := by
      rw [hDF]
      simpa only [add_apply,sum_apply] using (tendsto_const_nhds.add htailD)
    have hpartialR : Tendsto (fun L => ∑ j ∈ Finset.range (N-1+L), R j) atTop (𝓝 ((fderiv ℂ F a) v)) := by
      convert hpartial using 1
      funext L
      rw [Finset.sum_range_add]
      congr 1
      · exact Finset.sum_congr rfl (fun j _ => (hγD j).symm)
      · exact Finset.sum_congr rfl (fun j _ => by simpa only [Nat.add_comm] using (hβD j).symm)
    have hlimit : Tendsto (fun M => ∑ j ∈ Finset.range M, R j) atTop
        (𝓝 (-hillAbelianSelectedGlobalPsi q hq hr n hn b/2-Z)) := by
      exact tendsto_sub_single_sum _ n hn Z _ (tendsto_hillDirichletInterpolationSum q hq hr n hn b)
    have hshift : Tendsto (fun L : ℕ => N-1+L) atTop atTop := by
      simpa only [Nat.add_comm] using (tendsto_add_atTop_nat (N-1))
    exact tendsto_nhds_unique hpartialR (hlimit.comp hshift)
  · filter_upwards [hβmatch,hheadmatch] with r hrβ hrγ
    have hsum := Summable.sum_add_tsum_nat_add (N-1)
      (summable_hillRegularAbelianCorrection h0q h0r r.val r.property.1 r.property.2 n hn)
    have htail (j : ℕ) : β (j+N) (SpectralWeight.one.toCoeff r.val)=
        hillRegularAbelianCorrection r.val r.property.1 r.property.2 n hn (j+N) (by omega) := hrβ.2 (j+N) (by omega)
    dsimp only [F]
    rw [Finset.sum_congr rfl hrγ,tsum_congr htail]
    simpa only [hillSummedRegularAbelianCorrection,Nat.add_assoc,Nat.sub_add_cancel hN] using hsum

end NLS.KdV
