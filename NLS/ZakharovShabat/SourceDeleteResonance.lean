import NLS.ZakharovShabat.SourceRealTypeIdentity
import NLS.SequenceSpaces.DeletedCoordinateAtInfinity
import NLS.SequenceSpaces.SourceCotangent

/-! # Deleting the two signed coefficients of one resonance

The physical pair projection is complex linear, preserves real type, and
contracts the actual finite-exponent source norm. Distant projections send
one common smaller ball into a prescribed ball around a fixed source.
-/
noncomputable section
open Set Metric Filter Topology Complex
open scoped ENNReal ComplexConjugate
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def sourceDeleteResonance (n : ℤ) : CoeffPair p →L[ℂ] CoeffPair p :=
  (CoeffPair.toMax p).symm.toContinuousLinearMap.comp
    (((Coeff.deleteCoordinate (-n)).prodMap (Coeff.deleteCoordinate n)).comp
      (CoeffPair.toMax p).toContinuousLinearMap)

@[simp] theorem sourceDeleteResonance_fst (n : ℤ) (a : CoeffPair p) :
    (sourceDeleteResonance n a).fst = Coeff.deleteCoordinate (-n) a.fst := rfl

@[simp] theorem sourceDeleteResonance_snd (n : ℤ) (a : CoeffPair p) :
    (sourceDeleteResonance n a).snd = Coeff.deleteCoordinate n a.snd := rfl

theorem sourceDeleteResonance_realType (n : ℤ) (a : CoeffPair p)
    (ha : IsRealType (CoeffPair.toMax p a)) :
    IsRealType (CoeffPair.toMax p (sourceDeleteResonance n a)) := by
  intro j
  change Coeff.deleteCoordinate n a.snd j = conj (Coeff.deleteCoordinate (-n) a.fst (-j))
  by_cases hj : j = n
  · subst j
    simp
  · have hneg : -j ≠ -n := by omega
    rw [Coeff.deleteCoordinate_apply_other n j hj,
      Coeff.deleteCoordinate_apply_other (-n) (-j) hneg]
    exact ha j

private theorem norm_delete_le (n : ℤ) (a : Coeff p) :
    ‖Coeff.deleteCoordinate n a‖ ≤ ‖a‖ := by
  apply lp.norm_mono (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  intro j
  by_cases hj : j = n
  · subst j
    simp
  · rw [Coeff.deleteCoordinate_apply_other n j hj]

theorem norm_sourceDeleteResonance_le (hp : p ≠ ⊤) (n : ℤ) (a : CoeffPair p) :
    ‖sourceDeleteResonance n a‖ ≤ ‖a‖ := by
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos
    (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' hp
  rw [WithLp.prod_norm_eq_add hp0,WithLp.prod_norm_eq_add hp0]
  change (‖Coeff.deleteCoordinate (-n) a.fst‖ ^ p.toReal +
    ‖Coeff.deleteCoordinate n a.snd‖ ^ p.toReal) ^ (1/p.toReal) ≤ _
  gcongr
  · exact norm_delete_le _ _
  · exact norm_delete_le _ _

theorem norm_sub_sourceDeleteResonance_le (n : ℤ) (a : CoeffPair p) :
    ‖a-sourceDeleteResonance n a‖ ≤ ‖a.fst (-n)‖+‖a.snd n‖ := by
  have he : a-sourceDeleteResonance n a =
      CoeffPair.inlCLM (lp.single p (-n) (a.fst (-n))) +
        CoeffPair.inrCLM (lp.single p n (a.snd n)) := by
    apply (CoeffPair.toMax p).injective
    apply Prod.ext <;> ext j <;>
      simp [sourceDeleteResonance,Coeff.deleteCoordinate] <;> rfl
  rw [he]
  simpa only [CoeffPair.norm_inlCLM,CoeffPair.norm_inrCLM,
    lp.norm_single (zero_lt_one.trans_le (Fact.out : 1 ≤ p))] using norm_add_le
      (CoeffPair.inlCLM (lp.single p (-n) (a.fst (-n))))
      (CoeffPair.inrCLM (lp.single p n (a.snd n)))

theorem sourceDeleteResonance_mem_ball (hp : p ≠ ⊤) (n : ℤ) (a b : CoeffPair p)
    (δ ρ : ℝ) (ha : a ∈ ball b ρ)
    (hb : ρ+‖b.fst (-n)‖+‖b.snd n‖ ≤ δ) :
    sourceDeleteResonance n a ∈ ball b δ := by
  rw [mem_ball,dist_eq_norm] at ha ⊢
  calc
    ‖sourceDeleteResonance n a-b‖ ≤
        ‖sourceDeleteResonance n (a-b)‖+‖sourceDeleteResonance n b-b‖ := by
      rw [map_sub]
      have he : sourceDeleteResonance n a-b =
          (sourceDeleteResonance n a-sourceDeleteResonance n b)+
            (sourceDeleteResonance n b-b) := by abel
      rw [he]
      exact norm_add_le _ _
    _ ≤ ‖a-b‖+(‖b.fst (-n)‖+‖b.snd n‖) := by
      exact add_le_add (norm_sourceDeleteResonance_le hp n (a-b))
        (by rw [norm_sub_rev]; exact norm_sub_sourceDeleteResonance_le n b)
    _ < δ := by linarith

theorem exists_uniform_sourceDeleteResonance_mapsTo (hp : p ≠ ⊤)
    (b : CoeffPair p) (δ : ℝ) (hδ : 0 < δ) :
    ∃ K : ℕ, ∀ n : ℤ, K ≤ n.natAbs →
      MapsTo (sourceDeleteResonance n) (ball b (δ/2)) (ball b δ) := by
  obtain ⟨K₁,h₁⟩ := Coeff.exists_cutoff_norm_apply_lt hp b.fst (show 0 < δ/4 by positivity)
  obtain ⟨K₂,h₂⟩ := Coeff.exists_cutoff_norm_apply_lt hp b.snd (show 0 < δ/4 by positivity)
  refine ⟨max K₁ K₂,fun n hn a ha => sourceDeleteResonance_mem_ball hp n a b δ (δ/2) ha ?_⟩
  have hfst := h₁ (-n) (by simpa only [Int.natAbs_neg] using (le_max_left K₁ K₂).trans hn)
  have hsnd := h₂ n ((le_max_right K₁ K₂).trans hn)
  linarith

end NLS.ZakharovShabat
