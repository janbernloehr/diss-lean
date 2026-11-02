import NLS.ZakharovShabat.SourcePsiCriticalReciprocalInequality
import NLS.SequenceSpaces.ReciprocalBootstrap

/-! # Proposition 4.1: actual psi roots versus critical roots

The original normalized psi family has gap-normalized differences in every
finite exponent above one. The neighborhood precedes the exponent, and the
norm constants are uniform in the deleted index and locally uniform at all
complex sources in a constructed open neighborhood of the entire real locus.
-/
noncomputable section
set_option autoImplicit false
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The finite reciprocal iteration upgrades the actual normalized root difference
on one common complex neighborhood of each real source. -/
theorem SourceLemma12_11Data.exists_local_critical_gapNormalized_onePlus
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W : Set (CoeffPair p)}
    {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
    (H : SourceLemma12_11Data hp hp1 W₀ W s) (hp2 : 2 < p)
    (φ : realTypeSourceLocus p) (hφ : φ.val ∈ W) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ.val ∈ V ∧ V ⊆ W ∧
      ∀ q : ℝ≥0∞, q ≠ ⊤ → 1 < q → ∃ M : ℝ, 0 ≤ M ∧
        ∀ ψ ∈ V, ∀ n : ℤ, ∃ a : Coeff q, ‖a‖ ≤ M ∧ a n = 0 ∧
          (∀ k, a k = sourcePsiCriticalGapNormalized hp hp1 s n ψ k) ∧
          ∀ k : ℤ, k ≠ n → displacedRoots (s n ψ : Coeff p) k =
            sourceCriticalRoot hp hp1 ψ k+sourcePeriodicGapDisplacement hp hp1 ψ k*a k := by
  obtain ⟨Vi,hVi,hφi,hViW,A,hA,hi⟩ := H.exists_local_critical_gapNormalized_half_exponent φ hφ
  obtain ⟨Vr,hVr,hφr,_,K,C,hC,hr⟩ := H.exists_local_critical_reciprocal_inequality φ hφ
  obtain ⟨_,_,Vg,hVg,hφg,G,hG,hg⟩ :=
    exists_uniform_small_sourcePeriodicGapDisplacement hp hp1 φ.val (by norm_num : (0:ℝ)<1)
  let V := Vi ∩ Vr ∩ Vg
  have hpr2 : 2 < p.toReal := by
    simpa only [ENNReal.toReal_ofNat] using (ENNReal.toReal_lt_toReal (by norm_num) hp).mpr hp2
  have hhalf1 : 1 < p/2 := by
    rw [← Coeff.halfExponent_eq_div hp,← ENNReal.ofReal_one]
    exact ENNReal.ofReal_lt_ofReal_iff (by positivity) |>.mpr (by linarith : (1:ℝ)<p.toReal/2)
  have hhalf : p/2 ≠ ⊤ := by rw [← Coeff.halfExponent_eq_div hp]; exact ENNReal.ofReal_ne_top
  let : Fact (1 ≤ p/2) := ⟨hhalf1.le⟩
  have hfactor (ψ : CoeffPair p) (hψ : ψ ∈ V) (n k : ℤ) :
      sourcePsiCriticalDifference hp hp1 s n ψ k = sourcePeriodicGapDisplacement hp hp1 ψ k*
        sourcePsiCriticalGapNormalized hp hp1 s n ψ k := by
    obtain ⟨a,_,ha,hf⟩ := hi ψ hψ.1.1 n
    rw [← ha k]
    exact hf k
  have hboot := Coeff.exists_uniform_reciprocal_bootstrap (q₀ := p/2) hp hp1 hhalf hhalf1 V
    (sourcePeriodicGapDisplacement hp hp1) (fun ψ n => sourcePsiCriticalGapNormalized hp hp1 s n ψ)
    G A C hG hA hC K (fun ψ hψ => (hg ψ hψ.2).1) (by
      intro ψ hψ n
      obtain ⟨a,ha,hak,_⟩ := hi ψ hψ.1.1 n
      exact ⟨a,ha,hak⟩) (by
      intro ψ hψ n k hk
      simpa only [hfactor ψ hψ n] using hr ψ hψ.1.2 n k hk)
  refine ⟨V,(hVi.inter hVr).inter hVg,⟨⟨hφi,hφr⟩,hφg⟩,fun _ h => hViW h.1.1,?_⟩
  intro q hq hq1
  obtain ⟨M,hM,hrows⟩ := hboot q hq hq1
  refine ⟨M,hM,?_⟩
  intro ψ hψ n
  obtain ⟨a,ha,hak⟩ := hrows ψ hψ n
  refine ⟨a,ha,?_,hak,?_⟩
  · rw [hak n]
    simp only [sourcePsiCriticalGapNormalized,sourcePsiCriticalDifference_same,zero_div]
  · intro k hkn
    have hf := hfactor ψ hψ n k
    rw [sourcePsiCriticalDifference_other hp hp1 s n k hkn,← hak k] at hf
    exact sub_eq_iff_eq_add'.mp hf

/-- Proposition 4.1 of arXiv:1606.07052v1, with actual canonical psi roots,
critical roots, gaps, and all locally uniform quantifiers on one constructed domain. -/
theorem sourceProposition4_1 (hp : p ≠ ⊤) (hp2 : 2 < p) :
    ∃ W₀ W : Set (CoeffPair p), ∃ s : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
      SourceLemma12_11Data hp (lt_trans (by norm_num : (1:ℝ≥0∞)<2) hp2) W₀ W s ∧
      ∃ U : Set (CoeffPair p), IsOpen U ∧ realTypeSourceLocus p ⊆ U ∧ U ⊆ W ∧
        ∀ ψ ∈ U, ∃ V : Set (CoeffPair p), IsOpen V ∧ ψ ∈ V ∧ V ⊆ U ∧
          ∀ q : ℝ≥0∞, q ≠ ⊤ → 1 < q → ∃ M : ℝ, 0 ≤ M ∧
            ∀ χ ∈ V, ∀ n : ℤ, ∃ a : Coeff q, ‖a‖ ≤ M ∧ a n = 0 ∧
              (∀ k, a k = sourcePsiCriticalGapNormalized hp (lt_trans (by norm_num : (1:ℝ≥0∞)<2) hp2) s n χ k) ∧
              ∀ k : ℤ, k ≠ n → displacedRoots (s n χ : Coeff p) k =
                sourceCriticalRoot hp (lt_trans (by norm_num : (1:ℝ≥0∞)<2) hp2) χ k+
                  sourcePeriodicGapDisplacement hp (lt_trans (by norm_num : (1:ℝ≥0∞)<2) hp2) χ k*a k := by
  let hp1 : 1 < p := lt_trans (by norm_num : (1:ℝ≥0∞)<2) hp2
  obtain ⟨W₀,_,_,_,W,_,_,hreal,s,H⟩ := sourceLemma12_11 hp hp1
  have hlocal (φ : realTypeSourceLocus p) := H.exists_local_critical_gapNormalized_onePlus hp2 φ (hreal φ.property)
  choose V hV hφV hVW hrows using hlocal
  let U := ⋃ φ : realTypeSourceLocus p, V φ
  refine ⟨W₀,W,s,H,U,isOpen_iUnion hV,?_,?_,?_⟩
  · intro ψ hψ
    exact mem_iUnion.mpr ⟨⟨ψ,hψ⟩,hφV ⟨ψ,hψ⟩⟩
  · intro ψ hψ
    obtain ⟨φ,hφ⟩ := mem_iUnion.mp hψ
    exact hVW φ hφ
  · intro ψ hψ
    obtain ⟨φ,hφ⟩ := mem_iUnion.mp hψ
    refine ⟨V φ,hV φ,hφ,subset_iUnion V φ,?_⟩
    intro q hq hq1
    obtain ⟨M,hM,hbound⟩ := hrows φ q hq hq1
    refine ⟨M,hM,?_⟩
    intro χ hχ n
    exact hbound χ hχ n

end NLS.ZakharovShabat
