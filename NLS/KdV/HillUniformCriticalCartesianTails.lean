import NLS.SequenceSpaces.NatL2BoundedMultipliers
import NLS.KdV.HillUniformFullRegularPhase
import NLS.KdV.HillCriticalOwnAmplitudeHilbert
import NLS.KdV.HillOwnCartesianAmplitude

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal Classical

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

include h0q h0r in
/-- The full original critical weighted Cartesian high tails and their
real conjugates have actual complex Hilbert analytic extensions on one
common native source ball, before the weight and the tail cutoff. -/
theorem exists_hillNativeCriticalCartesianTails_uniform_analytic :
    ∃ δ C : ℝ, ∃ N0 : ℕ, 0<δ ∧ 0<C ∧ ∃ hN0 : 1≤N0,
      ∀ w : SpectralWeight, ∀ N : ℕ, ∀ hN : N0≤N,
      ∃ F G : WeightedCoeff w.doubleIndex.toWeight 2 → Coeff 2,
        AnalyticOnNhd ℂ F (ball 0 δ) ∧ AnalyticOnNhd ℂ G (ball 0 δ) ∧
        (∀ q∈ball 0 δ, ‖F q‖^2≤C*(δ^2+512*δ^4) ∧ ‖G q‖^2≤C*(δ^2+512*δ^4)) ∧
        ∀ q : RealHillWeightedPotential w, ‖q.val‖<δ → ∀ k : ℕ,
          F q.val (Equiv.intEquivNat.symm k)=
            (w (2*((k+N : ℕ) : ℤ)) : ℂ)*(Real.sqrt (2*Real.pi*((k+N : ℕ) : ℝ)) : ℂ)*
              hillSpectralCartesian (hillPeriodOneUnitPotential w q.val)
                (hillPeriodOneUnitPotential_even w q.val) (hillPeriodOneUnitPotential_real w q.val q.property)
                (k+N) (by omega) ∧
          G q.val (Equiv.intEquivNat.symm k)=
            (w (2*((k+N : ℕ) : ℤ)) : ℂ)*(Real.sqrt (2*Real.pi*((k+N : ℕ) : ℝ)) : ℂ)*
              (starRingEnd ℂ) (hillSpectralCartesian (hillPeriodOneUnitPotential w q.val)
                (hillPeriodOneUnitPotential_even w q.val) (hillPeriodOneUnitPotential_real w q.val q.property)
                (k+N) (by omega)) := by
  obtain ⟨δ,M,Np,hδ,hM,hNp,hphases⟩ := exists_hillSummedRegularAbelianCorrection_uniform_native_analytic h0q h0r
  obtain ⟨C,hC,Nb,hNb,hbound⟩ := exists_hillNativeCriticalOwnAmplitudeTerms_uniform_square_bound h0q h0r δ hδ.le
  obtain ⟨Na,hNa,ha⟩ := exists_hillNativeCriticalOwnAmplitudeTerms_common_analytic h0q h0r δ
  obtain ⟨Nm,hNm,hmatch⟩ := exists_hillNativeCriticalOwnAmplitudeTerms_real_physical_matching h0q h0r δ
  let N0 := Np+Nb+Na+Nm
  have hN0 : 1≤N0 := by dsimp only [N0];omega
  refine ⟨δ,C*(Real.exp M)^2,N0,hδ,by positivity,hN0,?_⟩
  intro w N hN
  have hNP : Np≤N := by dsimp only [N0] at hN;omega
  have hNB : Nb≤N := by dsimp only [N0] at hN;omega
  have hNA : Na≤N := by dsimp only [N0] at hN;omega
  have hNM : Nm≤N := by dsimp only [N0] at hN;omega
  have hcharts (k : ℕ) := hphases (k+N) (by omega) w
  choose Φ hΦa _ hΦr hΦpa hΦpb hΦma hΦmb using hcharts
  let A : WeightedCoeff w.doubleIndex.toWeight 2 → ℕ → ℂ := fun q k =>
    hillNativeCriticalOwnAmplitudeTerm h0q h0r w (k+N) q
  let D : WeightedCoeff w.doubleIndex.toWeight 2 → ℕ → ℂ := fun q k =>
    hillNativeCriticalOwnDualAmplitudeTerm h0q h0r w (k+N) q
  let P : WeightedCoeff w.doubleIndex.toWeight 2 → ℕ → ℂ := fun q k => Complex.exp (I*Φ k q)
  let Q : WeightedCoeff w.doubleIndex.toWeight 2 → ℕ → ℂ := fun q k => Complex.exp (-I*Φ k q)
  have hqδ (q : WeightedCoeff w.doubleIndex.toWeight 2) (hq : q∈ball 0 δ) : ‖q‖≤δ :=
    (show ‖q‖<δ by simpa only [mem_ball,dist_zero_right] using hq).le
  obtain ⟨hFa,hFdata⟩ := Coeff.analyticOnNhd_natL2OfFunction_mul_of_uniform_bound A P (ball 0 δ) isOpen_ball
    (fun k => (ha w (k+N) (by omega)).1) hΦpa (C*(δ^2+512*δ^4)) (Real.exp M) (Real.exp_pos M).le
    (fun q hq => (hbound w N hNB q (hqδ q hq)).1) (fun q hq k => hΦpb k q hq)
  obtain ⟨hGa,hGdata⟩ := Coeff.analyticOnNhd_natL2OfFunction_mul_of_uniform_bound D Q (ball 0 δ) isOpen_ball
    (fun k => (ha w (k+N) (by omega)).2) hΦma (C*(δ^2+512*δ^4)) (Real.exp M) (Real.exp_pos M).le
    (fun q hq => (hbound w N hNB q (hqδ q hq)).2) (fun q hq k => hΦmb k q hq)
  refine ⟨fun q => Coeff.natL2OfFunction (fun k => A q k*P q k),
    fun q => Coeff.natL2OfFunction (fun k => D q k*Q q k),hFa,hGa,?_,?_⟩
  · intro q hq
    constructor
    · exact (hFdata q hq).1.trans_eq (by ring)
    · exact (hGdata q hq).1.trans_eq (by ring)
  · intro q hq k
    have hqb : q.val∈ball 0 δ := by simpa only [mem_ball,dist_zero_right] using hq
    have hm := hmatch w q hq.le (k+N) (by omega)
    have hp := hΦr k q hq
    let r : RealPeriodOneHillPotential := ⟨hillPeriodOneUnitPotential w q.val,
      hillPeriodOneUnitPotential_even w q.val,hillPeriodOneUnitPotential_real w q.val q.property⟩
    have hreal : (starRingEnd ℂ) (hillSummedRegularAbelianCorrection r.val r.property.1 r.property.2 (k+N) (by omega))=
        hillSummedRegularAbelianCorrection r.val r.property.1 r.property.2 (k+N) (by omega) :=
      Complex.conj_eq_iff_im.mpr (hillSummedRegularAbelianCorrection_im_eq_zero h0q h0r r.val r.property.1 r.property.2 (k+N) (by omega))
    constructor
    · rw [(hFdata q.val hqb).2 k]
      change hillNativeCriticalOwnAmplitudeTerm h0q h0r w (k+N) q.val*Complex.exp (I*Φ k q.val)=_
      rw [hm.1,hp,hillSpectralCartesian_eq_ownAmplitude_mul_correction]
      ring
    · rw [(hGdata q.val hqb).2 k]
      change hillNativeCriticalOwnDualAmplitudeTerm h0q h0r w (k+N) q.val*Complex.exp (-I*Φ k q.val)=_
      rw [hm.2,hp,hillSpectralCartesian_eq_ownAmplitude_mul_correction,map_mul,←Complex.exp_conj,map_mul,Complex.conj_I,hreal]
      ring

end NLS.KdV
