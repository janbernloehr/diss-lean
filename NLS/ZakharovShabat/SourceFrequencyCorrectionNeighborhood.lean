import NLS.ZakharovShabat.SourceFrequencyCorrectionCoefficients

/-! # Locally uniform refined frequency asymptotics

One connected almost-real neighborhood supports the actual frequency
correction in every finite lr with r > 1 and r >= p/3. The local source
neighborhood is chosen before the target exponent.
-/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
variable {W V : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- The refined remainder in Theorem 20.5 is locally bounded at every
complex source, on a neighborhood independent of its target exponent. -/
theorem SourceAbelianMomentAtlas.exists_frequencyCorrection_neighborhood
    (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 V s)
    (hV : IsOpen V) (hrealV : realTypeSourceLocus p ⊆ V) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ IsConnected U ∧ realTypeSourceLocus p ⊆ U ∧
      U ⊆ A.domain ∩ V ∧ ∀ φ ∈ U, ∃ T : Set (CoeffPair p),
        IsOpen T ∧ φ ∈ T ∧ T ⊆ U ∧
        ∀ r : ℝ≥0∞, r ≠ ⊤ → 1 < r → ENNReal.ofReal (p.toReal/3) ≤ r →
          ∃ C : ℝ, 0 ≤ C ∧ ∀ ψ ∈ T, ∃ b : Coeff r,
            (∀ n, b n = A.frequencyCorrection ψ n) ∧ ‖b‖ ≤ C := by
  obtain ⟨U,hU,hUc,hreal,hUV,hlocal⟩ := A.exists_lemma20_3_refined hs hV hrealV
  refine ⟨U,hU,hUc,hreal,hUV,?_⟩
  intro φ hφ
  obtain ⟨ρ,hρ,hball,hrows⟩ := hlocal φ hφ
  have hhalf : ENNReal.ofReal (p.toReal/2) ≤ p := by
    conv_rhs => rw [← ENNReal.ofReal_toReal hp]
    exact ENNReal.ofReal_le_ofReal (by linarith [ENNReal.toReal_nonneg (a := p)])
  obtain ⟨M,hM,hdata⟩ := hrows p hp hp1 hhalf
  obtain ⟨_,_,G,hG,hφG,R,hR,hgap⟩ :=
    exists_uniform_small_sourcePeriodicGapDisplacement hp hp1 φ (by norm_num : (0:ℝ)<1)
  let T := ball φ ρ ∩ G
  refine ⟨T,isOpen_ball.inter hG,⟨mem_ball_self hρ,hφG⟩,fun ψ hψ => hball hψ.1,?_⟩
  intro r hr hr1 hpr
  let : Fact (1 ≤ r) := ⟨hr1.le⟩
  let C := ‖(4/(2*Real.pi):ℂ)‖ *
    (M*(R^3*‖Coeff.puncturedLattice (min r p.conjExponent)
      (lt_min hr1 ((ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top))‖)+R^2*M/4)
  have hK := lp.norm_nonneg' (Coeff.puncturedLattice (min r p.conjExponent)
    (lt_min hr1 ((ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top)))
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro ψ hψ
  obtain ⟨d,_,hd,hdiag,hoff⟩ := hdata ψ hψ.1
  choose a haval han ha hfactor using hoff
  exact A.exists_refined_frequencyCorrection_coefficients hr hr1 hpr ψ d a R M hR hM.le
    (hgap ψ hψ.2).1 hd ha hdiag hfactor

end NLS.ZakharovShabat
