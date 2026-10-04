import NLS.ZakharovShabat.SourceAbelianMomentLemma20_3
import NLS.SequenceSpaces.ReciprocalSeriesConvergence

/-! # Absolute and locally uniform second-moment sums

Lemma 20.3 at exponent p supplies bounded coefficient rows. The bounded
gap sequence and the reciprocal Holder kernel give convergence of the
full sum, including its diagonal. The source neighborhood is common to
all selected indices; uniform convergence is asserted for each fixed n.
-/
noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
variable {W V : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- The actual second moments form an absolutely and locally uniformly
convergent series on a connected neighborhood of the real source locus. -/
theorem SourceAbelianMomentAtlas.exists_secondMoment_series
    (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 V s)
    (hV : IsOpen V) (hrealV : realTypeSourceLocus p ⊆ V) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ IsConnected U ∧ realTypeSourceLocus p ⊆ U ∧
      U ⊆ A.domain ∩ V ∧
      (∀ ψ ∈ U, ∀ n : ℤ, Summable (fun k => ‖A.moment n k 2 ψ‖)) ∧
      ∀ φ ∈ U, ∃ T : Set (CoeffPair p), IsOpen T ∧ φ ∈ T ∧ T ⊆ U ∧ ∀ n : ℤ,
        TendstoUniformlyOn
          (fun (N : ℕ) ψ => ∑ k ∈ Finset.Icc (-(N : ℤ)) N, A.moment n k 2 ψ)
          (fun ψ => ∑' k, A.moment n k 2 ψ) atTop T := by
  classical
  obtain ⟨U,hU,hUc,hreal,hUV,hlocal⟩ := A.exists_lemma20_3_refined hs hV hrealV
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans hp1)) hp
  have hhalf : ENNReal.ofReal (p.toReal/2) ≤ p := by
    conv_rhs => rw [← ENNReal.ofReal_toReal hp]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hconv (φ : CoeffPair p) (hφ : φ ∈ U) :
      ∃ T : Set (CoeffPair p), IsOpen T ∧ φ ∈ T ∧ T ⊆ U ∧ ∀ n : ℤ,
        (∀ ψ ∈ T, Summable (fun k => ‖A.moment n k 2 ψ‖)) ∧
        TendstoUniformlyOn
          (fun (N : ℕ) ψ => ∑ k ∈ Finset.Icc (-(N : ℤ)) N, A.moment n k 2 ψ)
          (fun ψ => ∑' k, A.moment n k 2 ψ) atTop T := by
    obtain ⟨ρ,hρ,hball,hrows⟩ := hlocal φ hφ
    obtain ⟨M,hM,hdata⟩ := hrows p hp hp1 hhalf
    obtain ⟨_,_,G,hG,hφG,R,hR,hgap⟩ :=
      exists_uniform_small_sourcePeriodicGapDisplacement hp hp1 φ (by norm_num : (0 : ℝ) < 1)
    let T := ball φ ρ ∩ G
    have hTball : T ⊆ ball φ ρ := fun _ h => h.1
    refine ⟨T,isOpen_ball.inter hG,⟨mem_ball_self hρ,hφG⟩,hTball.trans hball,?_⟩
    intro n
    have hcoeff (ψ : CoeffPair p) : ∃ a : Coeff p, ψ ∈ T →
        ‖a‖ ≤ M ∧ ∀ k : ℤ, k ≠ n →
          A.moment n k 2 ψ = (sourcePeriodicGapDisplacement hp hp1 ψ k)^3/((n-k:ℤ):ℂ)*a k := by
      by_cases hψ : ψ ∈ T
      · obtain ⟨d,_,_,_,hoff⟩ := hdata ψ hψ.1
        obtain ⟨a,_,_,ha,hfactor⟩ := hoff n
        exact ⟨a,fun _ => ⟨ha,hfactor⟩⟩
      · exact ⟨0,fun h => False.elim (hψ h)⟩
    choose a ha using hcoeff
    have hg (ψ : CoeffPair p) (hψ : ψ ∈ T) (k : ℤ) :
        ‖sourcePeriodicGapDisplacement hp hp1 ψ k‖ ≤ R :=
      (lp.norm_apply_le_norm (ne_of_gt (zero_lt_one.trans hp1)) _ k).trans (hgap ψ hψ.2).1
    apply Coeff.summable_uniform_of_reciprocal_bound hp hp1 n T
      (fun ψ k => A.moment n k 2 ψ) a (R^3) M (R^2/4*(Real.pi+M)) (by positivity)
      (fun ψ hψ => (ha ψ hψ).1)
    · intro ψ hψ
      obtain ⟨d,_,hd,hdiag,_⟩ := hdata ψ hψ.1
      rw [hdiag n, norm_mul, norm_div, norm_pow]
      have hd' := (lp.norm_apply_le_norm (ne_of_gt (zero_lt_one.trans hp1)) d n).trans hd
      have hsum : ‖(Real.pi:ℂ)+d n‖ ≤ Real.pi+M := by
        calc
          _ ≤ ‖(Real.pi:ℂ)‖+‖d n‖ := norm_add_le _ _
          _ = Real.pi+‖d n‖ := by rw [Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
          _ ≤ _ := add_le_add le_rfl hd'
      norm_num only [Complex.norm_ofNat]
      gcongr
      · exact hg ψ hψ n
    · intro ψ hψ k hkn
      rw [(ha ψ hψ).2 k hkn, norm_mul, norm_div, norm_pow, Complex.norm_intCast]
      calc
        _ = ‖sourcePeriodicGapDisplacement hp hp1 ψ k‖^3*‖a ψ k‖/|((n-k:ℤ):ℝ)| := by ring
        _ ≤ _ := by gcongr; exact hg ψ hψ k
  refine ⟨U,hU,hUc,hreal,hUV,?_,?_⟩
  · intro ψ hψ n
    obtain ⟨T,_,hψT,_,h⟩ := hconv ψ hψ
    exact (h n).1 ψ hψT
  · intro φ hφ
    obtain ⟨T,hT,hφT,hTU,h⟩ := hconv φ hφ
    exact ⟨T,hT,hφT,hTU,fun n => (h n).2⟩

end NLS.ZakharovShabat
