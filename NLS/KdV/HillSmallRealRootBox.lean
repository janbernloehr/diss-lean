import NLS.KdV.HillGapRootHilbertCompactness
import NLS.KdV.HillLabelContinuity
import NLS.KdV.HillFreeGapContourGeometry

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal Classical

namespace NLS.KdV



/-- For small real potentials, all but the first root-box coordinate have
a uniform linear Hilbert bound. The first coordinate is kept explicit. -/
theorem norm_hillGapRootHilbertCoordinates_le_first_add_small
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (hsmall : ‖q‖≤1/4) (roots : ℕ → ℝ) (hroots : roots∈hillGapRootBox q hq hr) :
    ‖hillGapRootHilbertCoordinates q hq hr roots hroots‖ ≤
      ‖hillGapRootHilbertCoordinates q hq hr roots hroots 1‖+8*‖q‖ := by
  let a := hillGapRootHilbertCoordinates q hq hr roots hroots
  let e : Coeff 2 := lp.single 2 1 (a 1)
  let b := a-e
  have hnorm : ‖b‖≤‖((4*‖q‖ : ℝ) : ℂ) • Coeff.positivePuncturedLattice 2 (by norm_num)‖ := by
    apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞)≠0)
    intro m
    rw [lp.coeFn_smul,Pi.smul_apply,norm_smul,norm_real,Real.norm_of_nonneg (by positivity : 0≤4*‖q‖)]
    by_cases hm1 : m=1
    · subst m
      have he1 : e 1=a 1 := by simp [e,lp.single_apply]
      change ‖a 1-e 1‖≤_
      rw [he1,sub_self,norm_zero]
      positivity
    · have he : e m=0 := by simp [e,lp.single_apply,hm1]
      change ‖a m-e m‖≤_
      rw [he,sub_zero]
      change ‖hillGapRootScaledOffset roots m‖≤_
      rw [hillGapRootScaledOffset]
      by_cases hm : 0<m
      · rw [if_pos hm,Coeff.positivePuncturedLattice_apply,if_pos hm,norm_div,norm_real,Real.norm_eq_abs,norm_inv]
        have hn2 : 2≤m.toNat := by omega
        have hcut : 8*‖q‖≤(m.toNat : ℝ) := by
          have hh : (2 : ℝ)≤m.toNat := by exact_mod_cast hn2
          linarith
        have hh := hillGapRoot_high_localization q hq hr roots hroots m.toNat hn2 hcut
        exact (div_le_div_of_nonneg_right hh (norm_nonneg (m : ℂ))).trans_eq (by ring)
      · rw [if_neg hm,norm_zero]
        positivity
  have hb : ‖b‖≤8*‖q‖ := by
    apply hnorm.trans
    rw [norm_smul,norm_real,Real.norm_of_nonneg (by positivity : 0≤4*‖q‖)]
    exact (mul_le_mul_of_nonneg_left Coeff.norm_positivePuncturedLattice_two_le (by positivity)).trans_eq (by ring)
  have he : ‖e‖=‖a 1‖ := by
    change ‖(lp.single 2 (1 : ℤ) (a 1) : Coeff 2)‖=‖a 1‖
    exact lp.norm_single (E := fun _ : ℤ => ℂ) (by norm_num : (0 : ℝ≥0∞)<2) (1 : ℤ) (a 1)
  have hh := norm_add_le b e
  have ha : b+e=a := by dsimp only [b];abel
  rw [ha,he] at hh
  change ‖a‖≤‖a 1‖+8*‖q‖
  linarith

/-- Every original real gap-root-box Hilbert vector is uniformly small
when the real source potential tends to zero. This is uniform across all
root selections, so it can be used simultaneously for every deleted index. -/
theorem exists_hillGapRootHilbertCoordinates_uniform_small_at_zero
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))
    (ε : ℝ) (hε : 0<ε) :
    ∃ δ : ℝ, 0<δ ∧ ∀ q : RealPeriodOneHillPotential, ‖q.val‖<δ →
      ∀ roots : ℕ → ℝ, ∀ hroots : roots∈hillGapRootBox q.val q.property.1 q.property.2,
        ‖hillGapRootHilbertCoordinates q.val q.property.1 q.property.2 roots hroots‖<ε := by
  let q0 : RealPeriodOneHillPotential := ⟨0,h0q,h0r⟩
  have hL0 : hillRealLabels q0.val q0.property.1 q0.property.2 1=freeHillValue (1 : ℕ) := by
    simpa only [q0,show 2*(1 : ℕ)-1=1 by norm_num] using (hillFreeGapEndpoints h0q h0r 1 (by norm_num)).1
  have hU0 : hillRealLabels q0.val q0.property.1 q0.property.2 2=freeHillValue (1 : ℕ) := by
    simpa only [q0,show 2*(1 : ℕ)=2 by norm_num] using (hillFreeGapEndpoints h0q h0r 1 (by norm_num)).2
  have hCL : ContinuousAt (fun q : RealPeriodOneHillPotential => hillRealLabels q.val q.property.1 q.property.2 1) q0 :=
    (continuous_hillRealLabels 1).continuousAt
  have hCU : ContinuousAt (fun q : RealPeriodOneHillPotential => hillRealLabels q.val q.property.1 q.property.2 2) q0 :=
    (continuous_hillRealLabels 2).continuousAt
  obtain ⟨δL,hδL,hL⟩ := Metric.continuousAt_iff.mp hCL
    (ε/2) (by positivity)
  obtain ⟨δU,hδU,hU⟩ := Metric.continuousAt_iff.mp hCU
    (ε/2) (by positivity)
  let δ := min δL (min δU (min (1/4) (ε/16)))
  have hδ : 0<δ := by dsimp only [δ];positivity
  refine ⟨δ,hδ,?_⟩
  intro q hq roots hroots
  have hδL' : δ≤δL := min_le_left _ _
  have hδU' : δ≤δU := (min_le_left _ _).trans' (min_le_right _ _)
  have hδsmall : δ≤1/4 := (min_le_left _ _).trans'
    ((min_le_right _ _).trans (min_le_right _ _))
  have hδε : δ≤ε/16 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hdist : dist q q0=‖q.val‖ := by
    change dist q.val (0 : WeightedCoeff SpectralWeight.one.toWeight 2)=‖q.val‖
    exact dist_zero_right _
  have hl : |hillRealLabels q.val q.property.1 q.property.2 1-freeHillValue (1 : ℕ)|<ε/2 := by
    have hh := hL (show dist q q0<δL from by rw [hdist];exact hq.trans_le hδL')
    simpa only [hL0,Real.dist_eq] using hh
  have hu : |hillRealLabels q.val q.property.1 q.property.2 2-freeHillValue (1 : ℕ)|<ε/2 := by
    have hh := hU (show dist q q0<δU from by rw [hdist];exact hq.trans_le hδU')
    simpa only [hU0,Real.dist_eq] using hh
  have hgap : roots 0∈Icc (hillRealLabels q.val q.property.1 q.property.2 1)
      (hillRealLabels q.val q.property.1 q.property.2 2) := hroots 0
  have hfirst : ‖hillGapRootHilbertCoordinates q.val q.property.1 q.property.2 roots hroots 1‖<ε/2 := by
    have he : hillGapRootHilbertCoordinates q.val q.property.1 q.property.2 roots hroots 1=
        ((roots 0-freeHillValue (1 : ℕ) : ℝ) : ℂ) := by
      norm_num [hillGapRootHilbertCoordinates,hillGapRootScaledOffset]
    rw [he,norm_real,Real.norm_eq_abs]
    apply abs_lt.mpr
    constructor
    · linarith [(abs_lt.mp hl).1,hgap.1]
    · linarith [(abs_lt.mp hu).2,hgap.2]
  have hbound := norm_hillGapRootHilbertCoordinates_le_first_add_small q.val q.property.1 q.property.2
    (hq.le.trans hδsmall) roots hroots
  have hqε : ‖q.val‖<ε/16 := hq.trans_le hδε
  linarith

end NLS.KdV
