import NLS.ZakharovShabat.FiniteGapPacking
import NLS.ZakharovShabat.QuadraticCentralStrip

/-! # The finite central gap estimate for real M₁ potentials

The quantitative exterior strip counts bound every remaining real part.
For real-type potentials, ordered spectral gaps then fit inside that strip.
-/
noncomputable section
open scoped Classical
namespace NLS.ZakharovShabat

/-- The exact strip exclusion extends to arbitrary M₁ weights by lowering the norm. -/
theorem M1_canonicalSlot_not_mem_strip (w : SpectralWeight) (hw : w.HasLinearFactor)
    (φ : WeightedCoeffPair w.toWeight 2) (heven : weightedBaseToPair w φ ∈ pairParitySubspace 0)
    (n : ℤ) (hn : 8*‖φ‖^2 ≤ 1+|(n:ℝ)|) (m : ℤ) (hmn : m ≠ n) (i : Fin 2) :
    periodicEndpointSlot
      (canonicalPeriodicLeft (by simp) (by norm_num) (weightedBaseToPair w φ) heven)
      (canonicalPeriodicRight (by simp) (by norm_num) (weightedBaseToPair w φ) heven)
      (toLex (m,i)) ∉ resonantStrip n := by
  have hpar : weightedBaseToPair (SpectralWeight.sobolev 1 (by norm_num)) (m1LinearInclusion w hw φ) ∈
      pairParitySubspace 0 := by simpa only [weightedBaseToPair_m1LinearInclusion] using heven
  have h := linearWeight_canonicalSlot_not_mem_strip (SpectralWeight.sobolev 1 (by norm_num))
    (SpectralWeight.hasLinearFactor_sobolev 1 le_rfl) 1
    (by intro k; simp [Weight.sobolev_apply]) (m1LinearInclusion w hw φ) hpar n
    (m1LinearInclusion_threshold w hw φ n hn) m hmn i
  simpa only [periodicEndpointSlot,weightedBaseToPair_m1LinearInclusion] using h

/-- At a valid tail cutoff, every central endpoint lies between the exterior strips. -/
theorem M1_canonicalEndpoints_central_re (w : SpectralWeight) (hw : w.HasLinearFactor)
    (φ : WeightedCoeffPair w.toWeight 2) (heven : weightedBaseToPair w φ ∈ pairParitySubspace 0)
    (N : ℕ) (hN : 8*‖φ‖^2 ≤ 1+(N:ℝ)) (m : ℤ) (hm : m.natAbs < N) :
    |(canonicalPeriodicLeft (by simp) (by norm_num) (weightedBaseToPair w φ) heven m).re| ≤ ((N:ℝ)-1/2)*Real.pi ∧
    |(canonicalPeriodicRight (by simp) (by norm_num) (weightedBaseToPair w φ) heven m).re| ≤ ((N:ℝ)-1/2)*Real.pi := by
  have h (i : Fin 2) :
      |(periodicEndpointSlot
        (canonicalPeriodicLeft (by simp) (by norm_num) (weightedBaseToPair w φ) heven)
        (canonicalPeriodicRight (by simp) (by norm_num) (weightedBaseToPair w φ) heven)
        (toLex (m,i))).re| ≤ ((N:ℝ)-1/2)*Real.pi := by
    obtain ⟨n,hn⟩ := exists_centered_real_part
      (periodicEndpointSlot
        (canonicalPeriodicLeft (by simp) (by norm_num) (weightedBaseToPair w φ) heven)
        (canonicalPeriodicRight (by simp) (by norm_num) (weightedBaseToPair w φ) heven) (toLex (m,i)))
    have hnN : n.natAbs < N := by
      by_contra hh
      have hh' : (N:ℝ) ≤ |(n:ℝ)| := by
        simpa only [Nat.cast_natAbs,Int.cast_abs] using
          (show (N:ℝ) ≤ (n.natAbs:ℝ) by exact_mod_cast (Nat.le_of_not_gt hh))
      exact M1_canonicalSlot_not_mem_strip w hw φ heven n (by linarith) m
        (by intro he; subst n; omega) i hn
    have hn' : |(n:ℝ)|+1 ≤ (N:ℝ) := by
      simpa only [Nat.cast_add,Nat.cast_one,Nat.cast_natAbs,Int.cast_abs] using
        (show ((n.natAbs+1 : ℕ):ℝ) ≤ (N:ℝ) by exact_mod_cast hnN)
    have hb := abs_add_le
      ((periodicEndpointSlot
        (canonicalPeriodicLeft (by simp) (by norm_num) (weightedBaseToPair w φ) heven)
        (canonicalPeriodicRight (by simp) (by norm_num) (weightedBaseToPair w φ) heven)
        (toLex (m,i))).re-Real.pi*n) (Real.pi*n)
    simp only [sub_add_cancel,abs_mul,abs_of_pos Real.pi_pos] at hb
    nlinarith [Real.pi_pos]
  exact ⟨by simpa only [periodicEndpointSlot_left] using h 0,
    by simpa only [periodicEndpointSlot_right] using h 1⟩

/-- The finite central gaps of a real-type potential satisfy the source width estimate. -/
theorem M1_real_canonicalGap_central_sq_le (w : SpectralWeight) (hw : w.HasLinearFactor)
    (φ : WeightedCoeffPair w.toWeight 2) (heven : weightedBaseToPair w φ ∈ pairParitySubspace 0)
    (hreal : IsRealType (weightedBaseToPair w φ))
    (N : ℕ) (hpos : 0 < N) (hN : 8*‖φ‖^2 ≤ 1+(N:ℝ)) :
    (∑ n ∈ Finset.Ioo (-(N:ℤ)) N,
      ‖canonicalPeriodicGap (by simp) (by norm_num) (weightedBaseToPair w φ) heven n‖^2) ≤
      ((2*(N:ℝ)-1)*Real.pi)^2 := by
  let ξ := canonicalPeriodicLeft (by simp) (by norm_num) (weightedBaseToPair w φ) heven
  let η := canonicalPeriodicRight (by simp) (by norm_num) (weightedBaseToPair w φ) heven
  let b := ((N:ℝ)-1/2)*Real.pi
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hpos
  have hb : 0 ≤ b := mul_nonneg (by linarith) Real.pi_pos.le
  have hs := canonicalPeriodicEndpoints_spec (by simp) (by norm_num : (1:ENNReal) < 2)
    (weightedBaseToPair w φ) heven
  have hbound (n : ℤ) (hn : n ∈ Finset.Ioo (-(N:ℤ)) N) :
      -b ≤ (ξ n).re ∧ (ξ n).re ≤ (η n).re ∧ (η n).re ≤ b := by
    have hn' := Finset.mem_Ioo.mp hn
    have h := M1_canonicalEndpoints_central_re w hw φ heven N hN n (by omega)
    exact ⟨(abs_le.mp h.1).1,NLS.ComplexAnalysis.re_le_of_complexLexLE (hs.2.1 n),
      (abs_le.mp h.2).2⟩
  have hpack := sum_ordered_interval_sq_le (Finset.Ioo (-(N:ℤ)) N)
    (fun n => (ξ n).re) (fun n => (η n).re) (-b) b (by linarith) hbound
    (fun i _ j _ hij => NLS.ComplexAnalysis.re_le_of_complexLexLE (hs.2.2 i j hij))
  have heq (n : ℤ) :
      ‖canonicalPeriodicGap (by simp) (by norm_num) (weightedBaseToPair w φ) heven n‖^2 =
        ((η n).re-(ξ n).re)^2 := by
    have hr := canonicalPeriodicEndpoints_im_eq_zero_of_realType (by simp)
      (by norm_num : (1:ENNReal) < 2) (weightedBaseToPair w φ) heven hreal n
    simp only [canonicalPeriodicGap,Complex.sq_norm,Complex.normSq_apply,Complex.sub_re,
      Complex.sub_im,hr.1,hr.2,sub_self,mul_zero,add_zero]
    change _ = _^2
    ring
  simp_rw [heq]
  convert hpack using 1
  dsimp [b]
  ring

/-- The source central estimate with its exact doubled-frequency endpoint weight. -/
theorem M1_real_canonicalGap_weighted_central_sq_le (w : SpectralWeight) (hw : w.HasLinearFactor)
    (φ : WeightedCoeffPair w.toWeight 2) (heven : weightedBaseToPair w φ ∈ pairParitySubspace 0)
    (hreal : IsRealType (weightedBaseToPair w φ))
    (N : ℕ) (hpos : 0 < N) (hN : 8*‖φ‖^2 ≤ 1+(N:ℝ)) :
    (∑ n ∈ Finset.Ioo (-(N:ℤ)) N,
      (w (2*n)*‖canonicalPeriodicGap (by simp) (by norm_num) (weightedBaseToPair w φ) heven n‖)^2) ≤
      w (2*(N:ℤ)-2)^2*((2*(N:ℝ)-1)*Real.pi)^2 := by
  have h := weighted_finite_gap_sq_le w (Finset.Ioo (-(N:ℤ)) N)
    (canonicalPeriodicGap (by simp) (by norm_num) (weightedBaseToPair w φ) heven)
    ((2*(N:ℤ)-2 : ℤ):ℝ) (((2*(N:ℝ)-1)*Real.pi)^2)
    (fun n hn => by
      have hn' := Finset.mem_Ioo.mp hn
      exact_mod_cast (show |2*n| ≤ 2*(N:ℤ)-2 by apply abs_le.mpr; constructor <;> omega))
    (M1_real_canonicalGap_central_sq_le w hw φ heven hreal N hpos hN)
  simpa only [SpectralWeight.realExtension_intCast] using h

end NLS.ZakharovShabat
