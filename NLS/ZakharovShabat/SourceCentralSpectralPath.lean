import NLS.ZakharovShabat.SourceCanonicalCoefficientContinuity
import NLS.ZakharovShabat.CanonicalPeriodicFree

/-! # A continuous actual spectral path retains its central pair

Strict real band separation prevents a spectral selection starting at the
free central root from crossing either neighboring moving real band.
This retains the actual central pair even through collapsed gaps.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- No actual periodic root lies strictly in a band between consecutive
canonical pairs, including the bands adjacent to collapsed gaps. -/
theorem not_mem_source_periodicSpectrum_of_re_in_band (hp : p≠⊤) (hp1 : 1<p)
    (φ : CoeffPair p) (hr : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) (z : ℂ)
    (hlo : (canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem _) n).re<z.re)
    (hhi : z.re<(canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem _) (n+1)).re) :
    z∉periodicSpectrum hp (periodOnePotential φ) := by
  let L := canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem _)
  let R := canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem _)
  have hord (k : ℤ) : (L k).re≤(R k).re :=
    re_le_of_complexLexLE ((canonicalPeriodicEndpoints_spec hp hp1 _ (periodOnePotential_mem φ)).2.1 k)
  have hsep {i j : ℤ} (hij : i<j) : (R i).re<(L j).re :=
    canonicalPeriodicRight_re_lt_left_of_lt hp hp1 _ (periodOnePotential_mem φ)
      (isRealType_periodOnePotential φ hr) hij
  intro hz
  obtain ⟨m,he⟩ := (canonicalPeriodicEndpoints_exhaustive hp hp1 _ (periodOnePotential_mem φ) z).mp hz
  have hm : (L m).re≤z.re ∧ z.re≤(R m).re := by
    rcases he with he|he
    · rw [←he]; exact ⟨le_rfl,hord m⟩
    · rw [←he]; exact ⟨hord m,le_rfl⟩
  rcases le_or_gt m n with hmn|hnm
  · by_cases he : m=n
    · subst m; exact (not_lt_of_ge hm.2) hlo
    · have h := hsep (by omega : m<n)
      have hn := hord n
      change (R n).re<z.re at hlo
      linarith
  · by_cases he : m=n+1
    · subst m; exact (not_lt_of_ge hm.1) hhi
    · have h := hsep (by omega : n+1<m)
      have hn := hord (n+1)
      change z.re<(L (n+1)).re at hhi
      linarith

/-- Any continuous actual spectral selection from the free central root
stays in the ACTUAL central pair along every real-source path. -/
theorem continuous_source_spectral_path_mem_central_pair (hp : p≠⊤) (hp1 : 1<p)
    (φ : ℝ → CoeffPair p) (hc : Continuous φ)
    (hr : ∀ t, IsRealType (CoeffPair.toMax p (φ t))) (h0 : φ 0=0)
    (z : ℝ → ℂ) (hz : Continuous z) (hz0 : z 0=0)
    (hspec : ∀ t, z t∈periodicSpectrum hp (periodOnePotential (φ t))) (t : ℝ) :
    z t=canonicalPeriodicLeft hp hp1 (periodOnePotential (φ t)) (periodOnePotential_mem _) 0 ∨
      z t=canonicalPeriodicRight hp hp1 (periodOnePotential (φ t)) (periodOnePotential_mem _) 0 := by
  let L := fun t => canonicalPeriodicLeft hp hp1 (periodOnePotential (φ t)) (periodOnePotential_mem _)
  let R := fun t => canonicalPeriodicRight hp hp1 (periodOnePotential (φ t)) (periodOnePotential_mem _)
  have hLc (n : ℤ) : Continuous (fun t => (L t n).re) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact continuous_re.continuousAt.comp
      ((continuousAt_canonicalPeriodicLeft_periodOne_of_realType hp hp1 (φ t) (hr t) n).comp hc.continuousAt)
  have hRc (n : ℤ) : Continuous (fun t => (R t n).re) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact continuous_re.continuousAt.comp
      ((continuousAt_canonicalPeriodicRight_periodOne_of_realType hp hp1 (φ t) (hr t) n).comp hc.continuousAt)
  have hsep (t : ℝ) {i j : ℤ} (hij : i<j) : (R t i).re<(L t j).re :=
    canonicalPeriodicRight_re_lt_left_of_lt hp hp1 _ (periodOnePotential_mem (φ t))
      (isRealType_periodOnePotential (φ t) (hr t)) hij
  let lo := fun t => ((R t (-1)).re+(L t 0).re)/2
  let hi := fun t => ((R t 0).re+(L t 1).re)/2
  have hloC : Continuous (fun t => (z t).re-lo t) :=
    (continuous_re.comp hz).sub (((hRc (-1)).add (hLc 0)).div_const 2)
  have hhiC : Continuous (fun t => hi t-(z t).re) :=
    (((hRc 0).add (hLc 1)).div_const 2).sub (continuous_re.comp hz)
  have hloN (t : ℝ) : (z t).re-lo t≠0 := by
    intro he
    have h := hsep t (by norm_num : (-1 : ℤ)<0)
    apply not_mem_source_periodicSpectrum_of_re_in_band hp hp1 (φ t) (hr t) (-1) (z t) ?_ ?_ (hspec t)
    all_goals dsimp only [lo] at he; norm_num only [neg_add_cancel]; linarith
  have hhiN (t : ℝ) : hi t-(z t).re≠0 := by
    intro he
    have h := hsep t (by norm_num : (0 : ℤ)<1)
    apply not_mem_source_periodicSpectrum_of_re_in_band hp hp1 (φ t) (hr t) 0 (z t) ?_ ?_ (hspec t)
    all_goals dsimp only [hi] at he; norm_num only [zero_add]; linarith
  have hL0 (n : ℤ) : L 0 n=(Real.pi : ℂ)*n := by
    dsimp only [L]; simp only [h0,map_zero,canonicalPeriodicLeft_zero]
  have hR0 (n : ℤ) : R 0 n=(Real.pi : ℂ)*n := by
    dsimp only [R]; simp only [h0,map_zero,canonicalPeriodicRight_zero]
  have hlo0 : 0<(z 0).re-lo 0 := by
    dsimp only [lo]; rw [hz0,hL0,hR0]; simp only [zero_re,Int.cast_neg,Int.cast_one,Int.cast_zero,mul_zero,mul_neg,mul_one,neg_re,ofReal_re]; linarith [Real.pi_pos]
  have hhi0 : 0<hi 0-(z 0).re := by
    dsimp only [hi]; rw [hz0,hL0,hR0]; simp only [zero_re,Int.cast_one,Int.cast_zero,mul_zero,mul_one,ofReal_re]; linarith [Real.pi_pos]
  have hlo := isPreconnected_univ.lt_of_ne hloC.continuousOn (fun t _ => hloN t)
    ⟨0,mem_univ _,hlo0⟩ (mem_univ t)
  have hhi := isPreconnected_univ.lt_of_ne hhiC.continuousOn (fun t _ => hhiN t)
    ⟨0,mem_univ _,hhi0⟩ (mem_univ t)
  have hinside : (L t 0).re≤(z t).re ∧ (z t).re≤(R t 0).re := by
    constructor
    · by_contra hn
      have hs := hsep t (by norm_num : (-1 : ℤ)<0)
      apply not_mem_source_periodicSpectrum_of_re_in_band hp hp1 (φ t) (hr t) (-1) (z t) ?_ ?_ (hspec t)
      · dsimp only [lo] at hlo; linarith
      · simpa only [neg_add_cancel] using lt_of_not_ge hn
    · by_contra hn
      have hs := hsep t (by norm_num : (0 : ℤ)<1)
      apply not_mem_source_periodicSpectrum_of_re_in_band hp hp1 (φ t) (hr t) 0 (z t) ?_ ?_ (hspec t)
      · exact lt_of_not_ge hn
      · dsimp only [hi] at hhi; simpa only [zero_add] using (by linarith : (z t).re<(L t 1).re)
  obtain ⟨m,he⟩ := (canonicalPeriodicEndpoints_exhaustive hp hp1 _ (periodOnePotential_mem (φ t)) (z t)).mp (hspec t)
  have hm : (L t m).re≤(z t).re ∧ (z t).re≤(R t m).re := by
    have hord := re_le_of_complexLexLE ((canonicalPeriodicEndpoints_spec hp hp1 _ (periodOnePotential_mem (φ t))).2.1 m)
    rcases he with he|he
    · rw [←he]; exact ⟨le_rfl,hord⟩
    · rw [←he]; exact ⟨hord,le_rfl⟩
  have hm0 : m=0 := by
    rcases lt_trichotomy m 0 with h|h|h
    · have hs := hsep t h; linarith [hm.2,hinside.1]
    · exact h
    · have hs := hsep t h; linarith [hm.1,hinside.2]
  subst m
  exact he.elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm)

end NLS.ZakharovShabat
