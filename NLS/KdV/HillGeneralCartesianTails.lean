import NLS.SequenceSpaces.NatL2BoundedMultipliers
import NLS.KdV.HillGeneralFullRegularPhase
import NLS.KdV.HillCriticalOwnAmplitudeHilbert
import NLS.KdV.HillOwnCartesianAmplitude

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

include h0q h0r in
/-- The original critical weighted Cartesian tails and their conjugates
have common analytic extensions around every real source, uniformly on
bounded native domains before the weight and the tail cutoff. -/
theorem exists_hillNativeCriticalCartesianTails_general_analytic (L : ℝ) (hL : 0≤L) :
    ∃ δ C : ℝ, ∃ N0 : ℕ, ∃ V : Set RealPeriodOneHillPotential,
      0<δ ∧ 0<C ∧ ∃ hN0 : 1≤N0, IsOpen V ∧ (⟨q,hq,hr⟩ : RealPeriodOneHillPotential)∈V ∧
      (∀ p∈V, SpectralWeight.one.toCoeff p.val∈ball (SpectralWeight.one.toCoeff q) δ) ∧
      ∀ w : SpectralWeight, ∀ N : ℕ, ∀ hN : N0≤N,
      ∃ F G : WeightedCoeff w.doubleIndex.toWeight 2 → Coeff 2,
        AnalyticOnNhd ℂ F (hillNativeSourceDomain w (SpectralWeight.one.toCoeff q) δ L) ∧
        AnalyticOnNhd ℂ G (hillNativeSourceDomain w (SpectralWeight.one.toCoeff q) δ L) ∧
        (∀ r : WeightedCoeff w.doubleIndex.toWeight 2,
          hillPeriodOneCoefficientMap w r∈ball (SpectralWeight.one.toCoeff q) δ → ‖r‖<L →
          ‖F r‖^2≤C*(L^2+512*L^4) ∧ ‖G r‖^2≤C*(L^2+512*L^4)) ∧
        ∀ r : RealHillWeightedPotential w, hillRealWeightedEmbedding w r∈V → ‖r.val‖<L → ∀ k : ℕ,
          F r.val (Equiv.intEquivNat.symm k)=
            (w (2*((k+N : ℕ) : ℤ)) : ℂ)*(Real.sqrt (2*Real.pi*((k+N : ℕ) : ℝ)) : ℂ)*
              hillSpectralCartesian (hillPeriodOneUnitPotential w r.val)
                (hillPeriodOneUnitPotential_even w r.val) (hillPeriodOneUnitPotential_real w r.val r.property)
                (k+N) (by omega) ∧
          G r.val (Equiv.intEquivNat.symm k)=
            (w (2*((k+N : ℕ) : ℤ)) : ℂ)*(Real.sqrt (2*Real.pi*((k+N : ℕ) : ℝ)) : ℂ)*
              (starRingEnd ℂ) (hillSpectralCartesian (hillPeriodOneUnitPotential w r.val)
                (hillPeriodOneUnitPotential_even w r.val) (hillPeriodOneUnitPotential_real w r.val r.property)
                (k+N) (by omega)) := by
  obtain ⟨δ,M,Np,V,hδ,hM,hNp,hV,hqV,hsource,hphases⟩ :=
    exists_hillSummedRegularAbelianCorrection_uniform_general_native_charts q hq hr h0q h0r L hL
  obtain ⟨C,hC,Nb,hNb,hbound⟩ := exists_hillNativeCriticalOwnAmplitudeTerms_uniform_square_bound h0q h0r L hL
  obtain ⟨Na,hNa,ha⟩ := exists_hillNativeCriticalOwnAmplitudeTerms_common_analytic h0q h0r L
  obtain ⟨Nm,hNm,hmatch⟩ := exists_hillNativeCriticalOwnAmplitudeTerms_real_physical_matching h0q h0r L
  let N0 := Np+Nb+Na+Nm
  have hN0 : 1≤N0 := by dsimp only [N0];omega
  refine ⟨δ,C*(Real.exp M)^2,N0,V,hδ,by positivity,hN0,hV,hqV,hsource,?_⟩
  intro w N hN
  have hNP : Np≤N := by dsimp only [N0] at hN;omega
  have hNB : Nb≤N := by dsimp only [N0] at hN;omega
  have hNA : Na≤N := by dsimp only [N0] at hN;omega
  have hNM : Nm≤N := by dsimp only [N0] at hN;omega
  have hcharts (k : ℕ) := hphases (k+N) (by omega) w
  choose Φ hΦa _ hΦr hΦpa hΦma hΦexp using hcharts
  let A : WeightedCoeff w.doubleIndex.toWeight 2 → ℕ → ℂ := fun q k =>
    hillNativeCriticalOwnAmplitudeTerm h0q h0r w (k+N) q
  let D : WeightedCoeff w.doubleIndex.toWeight 2 → ℕ → ℂ := fun q k =>
    hillNativeCriticalOwnDualAmplitudeTerm h0q h0r w (k+N) q
  let P : WeightedCoeff w.doubleIndex.toWeight 2 → ℕ → ℂ := fun q k => Complex.exp (I*Φ k q)
  let Q : WeightedCoeff w.doubleIndex.toWeight 2 → ℕ → ℂ := fun q k => Complex.exp (-I*Φ k q)
  let U := hillNativeSourceDomain w (SpectralWeight.one.toCoeff q) δ L
  have hU : IsOpen U := isOpen_hillNativeSourceDomain w (SpectralWeight.one.toCoeff q) δ L
  have hUB : U⊆ball (0 : WeightedCoeff w.doubleIndex.toWeight 2) L := by
    intro r hr
    rw [mem_ball,dist_zero_right]
    exact hr.2
  have hnorm (r : WeightedCoeff w.doubleIndex.toWeight 2) (hr : r∈U) : ‖r‖<L := by
    exact hr.2
  obtain ⟨hFa,hFdata⟩ := Coeff.analyticOnNhd_natL2OfFunction_mul_of_uniform_bound A P U hU
    (fun k => (ha w (k+N) (by omega)).1.mono hUB) hΦpa (C*(L^2+512*L^4)) (Real.exp M) (Real.exp_pos M).le
    (fun q hq => (hbound w N hNB q (hnorm q hq).le).1) (fun q hq k => (hΦexp k q hq.1 (hnorm q hq)).1)
  obtain ⟨hGa,hGdata⟩ := Coeff.analyticOnNhd_natL2OfFunction_mul_of_uniform_bound D Q U hU
    (fun k => (ha w (k+N) (by omega)).2.mono hUB) hΦma (C*(L^2+512*L^4)) (Real.exp M) (Real.exp_pos M).le
    (fun q hq => (hbound w N hNB q (hnorm q hq).le).2) (fun q hq k => (hΦexp k q hq.1 (hnorm q hq)).2)
  refine ⟨fun q => Coeff.natL2OfFunction (fun k => A q k*P q k),
    fun q => Coeff.natL2OfFunction (fun k => D q k*Q q k),hFa,hGa,?_,?_⟩
  · intro r hrU hrNorm
    have hq : r∈U := ⟨hrU,hrNorm⟩
    constructor
    · exact (hFdata r hq).1.trans_eq (by ring)
    · exact (hGdata r hq).1.trans_eq (by ring)
  · intro r hrV hrNorm k
    have hqb : r.val∈U := by
      refine ⟨?_,?_⟩
      · rw [hillPeriodOneCoefficientMap_eq_unit]
        exact hsource (hillRealWeightedEmbedding w r) hrV
      · exact hrNorm
    have hm := hmatch w r hrNorm.le (k+N) (by omega)
    have hp := hΦr k r hrV hrNorm
    let pR : RealPeriodOneHillPotential := ⟨hillPeriodOneUnitPotential w r.val,
      hillPeriodOneUnitPotential_even w r.val,hillPeriodOneUnitPotential_real w r.val r.property⟩
    have hreal : (starRingEnd ℂ) (hillSummedRegularAbelianCorrection pR.val pR.property.1 pR.property.2 (k+N) (by omega))=
        hillSummedRegularAbelianCorrection pR.val pR.property.1 pR.property.2 (k+N) (by omega) :=
      Complex.conj_eq_iff_im.mpr (hillSummedRegularAbelianCorrection_im_eq_zero h0q h0r pR.val pR.property.1 pR.property.2 (k+N) (by omega))
    constructor
    · rw [(hFdata r.val hqb).2 k]
      change hillNativeCriticalOwnAmplitudeTerm h0q h0r w (k+N) r.val*Complex.exp (I*Φ k r.val)=_
      rw [hm.1,hp,hillSpectralCartesian_eq_ownAmplitude_mul_correction]
      ring
    · rw [(hGdata r.val hqb).2 k]
      change hillNativeCriticalOwnDualAmplitudeTerm h0q h0r w (k+N) r.val*Complex.exp (-I*Φ k r.val)=_
      rw [hm.2,hp,hillSpectralCartesian_eq_ownAmplitude_mul_correction,map_mul,←Complex.exp_conj,map_mul,Complex.conj_I,hreal]
      ring

end NLS.KdV
