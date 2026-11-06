import NLS.KdV.HillSummableEndpointCotangents
import NLS.KdV.HillInfiniteNormingGardner
import NLS.KdV.HillSummedRegularCorrectionAnalytic
import NLS.ComplexAnalysis.NormalSeriesDerivatives

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.LinearVolterra NLS.FunctionalAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))
include h0q h0r

/-- The full actual infinite correction at an all-periodic source has a
physically matched analytic germ represented by an absolutely convergent
norming-gradient combination in the genuine Gardner domain. -/
theorem exists_hillSummedRegularCorrection_endpoint_cotangent
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1≤n)
    (hterminal : ∀ k : ℕ, ∀ hk : 1≤k,
      hillDirichletLogMultiplier q.val q.property.1 q.property.2 k hk=0) :
    ∃ F : Coeff 2 → ℂ, ∃ c : ℕ → ℂ,
      AnalyticAt ℂ F (SpectralWeight.one.toCoeff q.val) ∧
      (∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
        F (SpectralWeight.one.toCoeff p.val)=hillSummedRegularAbelianCorrection
          p.val p.property.1 p.property.2 n hn) ∧
      Summable (fun j : ℕ => ‖c j‖) ∧
      ∀ h : WeightedCoeff SpectralWeight.one.toWeight 2,
        SpectralWeight.one.toCoeff h∈Coeff.paritySubspace 0 →
        (fderiv ℂ F (SpectralWeight.one.toCoeff q.val)) (SpectralWeight.one.toCoeff h)=
          hillPhysicalDirectionPairing (SpectralWeight.one.toCoeff h) (hillInfiniteNormingGradient q c) := by
  obtain ⟨γ,c,hγ,hc,U,hU,hqU,J,C,hC,hγtail,hbound,hmatch⟩ :=
    exists_hillRegularCorrections_summable_endpoint_cotangents h0q h0r q n hn hterminal
  let p0 := SpectralWeight.one.toCoeff q.val
  let A : Coeff 2 → ℂ := fun p => ∑ j∈Finset.range J,γ j p
  let f : ℕ → Coeff 2 → ℂ := fun j p => γ (j+J) p
  let M : ℕ → ℝ := fun j => C/((j : ℝ)+(J+1 : ℕ))^2
  have hM : Summable M := by
    simpa only [M,mul_one_div] using
      (NLS.ReciprocalSeries.summable_nat_reciprocal_sq_tail (J+1) (by omega)).mul_left C
  have hf (j : ℕ) : AnalyticOnNhd ℂ (f j) U := hγtail (j+J) (by omega)
  have hb (j : ℕ) (p : Coeff 2) (hp : p∈U) : ‖f j p‖≤M j := by
    simpa only [f,M,Nat.cast_add,Nat.cast_one,add_assoc] using hbound p hp (j+J) (by omega)
  have hAt : AnalyticAt ℂ A p0 := Finset.analyticAt_fun_sum _ (fun j _ => (hγ j).1)
  have hFt := analyticOnNhd_tsum_of_summable_uniform_bound f U hU hf M hM hb
  let F : Coeff 2 → ℂ := fun p => A p+∑' j : ℕ,f j p
  have hF : AnalyticAt ℂ F p0 := hAt.add (hFt p0 hqU)
  have hheadmatch : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      ∀ j∈Finset.range J,γ j (SpectralWeight.one.toCoeff p.val)=hillRegularAbelianCorrection
        p.val p.property.1 p.property.2 n hn (j+1) (by omega) :=
    (Filter.eventually_all_finset _).mpr (fun j _ => (hγ j).2.1)
  have hphysical : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      F (SpectralWeight.one.toCoeff p.val)=hillSummedRegularAbelianCorrection
        p.val p.property.1 p.property.2 n hn := by
    filter_upwards [hmatch,hheadmatch] with p hp hh
    have hsum := (summable_hillRegularAbelianCorrection h0q h0r p.val p.property.1 p.property.2 n hn).sum_add_tsum_nat_add J
    have htail (j : ℕ) : f j (SpectralWeight.one.toCoeff p.val)=hillRegularAbelianCorrection
        p.val p.property.1 p.property.2 n hn ((j+J)+1) (by omega) := hp.2 (j+J) (by omega)
    dsimp only [F,A]
    rw [Finset.sum_congr rfl hh,tsum_congr htail]
    exact hsum
  have hsG := (hillNormingGradientSeries_norm_summable h0q h0r q c hc).1.of_norm
  have hsTail : Summable (fun j : ℕ => c (j+J) • hillLogNormingGradientCurve q (j+J+1) (by omega)) :=
    (summable_nat_add_iff J).mpr hsG
  refine ⟨F,c,hF,hphysical,hc,?_⟩
  intro h heven
  let T := hillPhysicalDirectionPairing (SpectralWeight.one.toCoeff h)
  have hfinite (K : ℕ) :
      (fderiv ℂ (fun p => ∑ j∈Finset.range K,f j p) p0) (SpectralWeight.one.toCoeff h)=
        T (∑ j∈Finset.range K,c (j+J) • hillLogNormingGradientCurve q (j+J+1) (by omega)) := by
    rw [fderiv_fun_sum (fun j _ => (hf j p0 hqU).differentiableAt)]
    simp only [sum_apply,map_sum,map_smul,smul_eq_mul]
    exact Finset.sum_congr rfl (fun j _ => (hγ (j+J)).2.2 h heven)
  have hlim := (T.continuous.tendsto (∑' j : ℕ,c (j+J) • hillLogNormingGradientCurve q (j+J+1) (by omega))).comp
    hsTail.hasSum.tendsto_sum_nat
  have htailD : (fderiv ℂ (fun p => ∑' j : ℕ,f j p) p0) (SpectralWeight.one.toCoeff h)=
      T (∑' j : ℕ,c (j+J) • hillLogNormingGradientCurve q (j+J+1) (by omega)) := by
    apply fderiv_tsum_apply_eq_of_partial_sum_limit f U hU hf M hM hb p0 (SpectralWeight.one.toCoeff h) hqU
    apply hlim.congr'
    exact Eventually.of_forall (fun K => (hfinite K).symm)
  have hheadD : (fderiv ℂ A p0) (SpectralWeight.one.toCoeff h)=
      T (∑ j∈Finset.range J,c j • hillLogNormingGradientCurve q (j+1) (by omega)) := by
    rw [show A=(fun p => ∑ j∈Finset.range J,γ j p) from rfl,
      fderiv_fun_sum (fun j _ => (hγ j).1.differentiableAt)]
    simp only [sum_apply,map_sum,map_smul,smul_eq_mul]
    exact Finset.sum_congr rfl (fun j _ => (hγ j).2.2 h heven)
  change (fderiv ℂ (fun p => A p+∑' j : ℕ,f j p) p0) (SpectralWeight.one.toCoeff h)=_
  rw [fderiv_fun_add hAt.differentiableAt (hFt p0 hqU).differentiableAt,add_apply,hheadD,htailD,←map_add]
  exact congrArg T (hsG.sum_add_tsum_nat_add J)

/-- The full infinite physical correction cotangent is intrinsic on the
original source tangent space, independently of the analytic extension. -/
theorem hillSummedRegularCorrectionGerm_endpoint_cotangent
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1≤n)
    (hterminal : ∀ k : ℕ, ∀ hk : 1≤k,
      hillDirichletLogMultiplier q.val q.property.1 q.property.2 k hk=0)
    (G : Coeff 2 → ℂ) (hG : AnalyticAt ℂ G (SpectralWeight.one.toCoeff q.val))
    (hGphysical : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      G (SpectralWeight.one.toCoeff p.val)=hillSummedRegularAbelianCorrection
        p.val p.property.1 p.property.2 n hn) :
    ∃ c : ℕ → ℂ, Summable (fun j : ℕ => ‖c j‖) ∧
      ∀ h : WeightedCoeff SpectralWeight.one.toWeight 2,
        SpectralWeight.one.toCoeff h∈Coeff.paritySubspace 0 →
        (fderiv ℂ G (SpectralWeight.one.toCoeff q.val)) (SpectralWeight.one.toCoeff h)=
          hillPhysicalDirectionPairing (SpectralWeight.one.toCoeff h) (hillInfiniteNormingGradient q c) := by
  obtain ⟨F,c,hF,hphysical,hc,hD⟩ := exists_hillSummedRegularCorrection_endpoint_cotangent h0q h0r q n hn hterminal
  have heq : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      G (SpectralWeight.one.toCoeff p.val)=F (SpectralWeight.one.toCoeff p.val) := by
    filter_upwards [hGphysical,hphysical] with p hpG hpF
    exact hpG.trans hpF.symm
  refine ⟨c,hc,?_⟩
  intro h heven
  exact (hillPhysicalCoefficientGerm_fderiv_eq_of_eventuallyEq q.val q.property.1 q.property.2
    G F hG hF heq h heven).trans (hD h heven)

/-- All actual fully summed corrections at an all-periodic source have
simultaneous physical H1 cotangents and zero genuine pairwise Gardner
brackets. No finite truncation replaces the physical correction. -/
theorem exists_hillSummedRegularCorrections_endpoint_Gardner_family
    (q : RealPeriodOneHillPotential)
    (hterminal : ∀ k : ℕ, ∀ hk : 1≤k,
      hillDirichletLogMultiplier q.val q.property.1 q.property.2 k hk=0) :
    ∃ F : ℕ → Coeff 2 → ℂ, ∃ c : ℕ → ℕ → ℂ,
      (∀ n : ℕ, AnalyticAt ℂ (F n) (SpectralWeight.one.toCoeff q.val) ∧
        (∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
          F n (SpectralWeight.one.toCoeff p.val)=hillSummedRegularAbelianCorrection
            p.val p.property.1 p.property.2 (n+1) (by omega)) ∧
        Summable (fun j : ℕ => ‖c n j‖) ∧
        ∀ h : WeightedCoeff SpectralWeight.one.toWeight 2,
          SpectralWeight.one.toCoeff h∈Coeff.paritySubspace 0 →
          (fderiv ℂ (F n) (SpectralWeight.one.toCoeff q.val)) (SpectralWeight.one.toCoeff h)=
            hillPhysicalDirectionPairing (SpectralWeight.one.toCoeff h) (hillInfiniteNormingGradient q (c n))) ∧
      (∀ n : ℕ,
        AbsolutelyContinuousOnInterval (extend (hillInfiniteNormingGradient q (c n))) 0 1 ∧
        MemLp (extend (hillInfiniteNormingGradient q (c n))) 2 (volume.restrict (Ioc (0 : ℝ) 1)) ∧
        MemLp (deriv (extend (hillInfiniteNormingGradient q (c n)))) 2 (volume.restrict (Ioc (0 : ℝ) 1))) ∧
      ∀ n m : ℕ,
        (∫ x in (0 : ℝ)..1,extend (hillInfiniteNormingGradient q (c n)) x*
          deriv (extend (hillInfiniteNormingGradient q (c m))) x)=0 := by
  have hex (n : ℕ) := exists_hillSummedRegularCorrection_endpoint_cotangent h0q h0r q (n+1) (by omega) hterminal
  choose F c hF hphysical hc hD using hex
  exact ⟨F,c,fun n => ⟨hF n,hphysical n,hc n,hD n⟩,
    fun n => hillInfiniteNormingGradient_H1 h0q h0r q (c n) (hc n),
    fun n m => hillInfiniteNormingGradient_GardnerBracket_eq_zero h0q h0r q (c n) (c m) (hc n) (hc m)⟩

end NLS.KdV
