import NLS.ZakharovShabat.SourcePsiOriginalCoordinateBound
import NLS.ZakharovShabat.SourceRealTypeBanachSpace
import NLS.SequenceSpaces.CoefficientDecay
import NLS.SequenceSpaces.RealCoeff

/-!
# The original full root-placement domain

All roots, including the subsequently omitted one, lie in the supplied
original disks. The infinite coordinate condition is open in the full
lp topology: only finitely many disks need individual margins, and the
tail disks all have radius pi/4. Restricting to real source and root
spaces gives the domain Omega of Lemma 12.5, with no choice of index.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def sourcePsiOriginalRootPlacement (D : ℤ → Set ℂ) : Set (Coeff p) :=
  {a | ∀ k : ℤ, displacedRoots a k ∈ D k}

theorem SourceIsolatingNeighborhoods.isOpen_originalRootPlacement
    {hp : p ≠ ⊤} {hp1 : 1 < p} {V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (hD : SourceIsolatingNeighborhoods hp hp1 V D c) :
    IsOpen (sourcePsiOriginalRootPlacement (p := p) D) := by
  obtain ⟨N,hN⟩ := hD.tail
  apply Metric.isOpen_iff.mpr
  intro a ha
  obtain ⟨M,hM⟩ := Coeff.exists_cutoff_norm_apply_lt hp a
    (by positivity : 0 < Real.pi/8)
  let K := max N M
  let S : Set (Coeff p) :=
    {b | ∀ j ∈ Finset.Icc (-(K:ℤ)) (K:ℤ), displacedRoots b j ∈ D j}
  have hS : IsOpen S := by
    have he : S = ⋂ j ∈ Finset.Icc (-(K:ℤ)) (K:ℤ),
        {b : Coeff p | displacedRoots b j ∈ D j} := by ext b; simp [S]
    rw [he]
    apply isOpen_biInter_finset
    intro j _
    obtain ⟨d,r,_,he⟩ := hD.discs j
    have hc : Continuous (fun b : Coeff p => displacedRoots b j) :=
      continuous_const.add (lp.evalCLM ℂ (fun _ : ℤ => ℂ) p j).continuous
    rw [he]
    exact isOpen_ball.preimage hc
  obtain ⟨δ,hδ,hball⟩ := Metric.isOpen_iff.mp hS a (fun j _ => ha j)
  refine ⟨min δ (Real.pi/8),by positivity,?_⟩
  intro b hb j
  by_cases hj : j.natAbs ≤ K
  · exact hball (ball_subset_ball (min_le_left _ _) hb) j
      (by simp only [Finset.mem_Icc]; omega)
  · have hjN : N < j.natAbs := by dsimp [K] at hj; omega
    have hjM : M ≤ j.natAbs := by dsimp [K] at hj; omega
    have hab : ‖b-a‖ < Real.pi/8 :=
      (show ‖b-a‖ < min δ (Real.pi/8) by
        simpa only [mem_ball, dist_eq_norm] using hb).trans_le (min_le_right _ _)
    have hcoord : ‖b j-a j‖ ≤ ‖b-a‖ :=
      lp.norm_apply_le_norm (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' (b-a) j
    have hbSmall : ‖b j‖ < Real.pi/4 := by
      have ht := norm_add_le (b j-a j) (a j)
      rw [sub_add_cancel] at ht
      linarith [hM j hjM]
    rw [hN j hjN]
    simpa [refinedResonantDisk, displacedRoots, mem_ball, dist_eq_norm] using hbSmall

/-- Source-first order, with all real roots specified before choosing n. -/
def sourcePsiOriginalOmega (V : Set (CoeffPair p)) (D : ℤ → Set ℂ) :
    Set (realTypeSourceSubmodule p × RealCoeff p) :=
  {t | (t.1:CoeffPair p) ∈ V ∧
    RealCoeff.complexCLM p t.2 ∈ sourcePsiOriginalRootPlacement D}

theorem SourceIsolatingNeighborhoods.isOpen_originalOmega
    {hp : p ≠ ⊤} {hp1 : 1 < p} {V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (hV : IsOpen V) : IsOpen (sourcePsiOriginalOmega V D) :=
  (hV.preimage (continuous_subtype_val.comp continuous_fst)).inter
    (hD.isOpen_originalRootPlacement.preimage
      ((RealCoeff.complexCLM p).continuous.comp continuous_snd))

/-- Every other placed root avoids the entire closed selected disk. -/
theorem SourceIsolatingNeighborhoods.originalRootPlacement_avoids_closedBall
    {hp : p ≠ ⊤} {hp1 : 1 < p} {V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (a : Coeff p) (ha : a ∈ sourcePsiOriginalRootPlacement D)
    (m k : ℤ) (hkm : k ≠ m) (d r : ℝ) (hr : 0 < r)
    (he : D m = ball (d:ℂ) r) (z : ℂ) (hz : z ∈ closedBall (d:ℂ) r) :
    z ≠ displacedRoots a k := by
  apply (hD.weighted_separation_closure k m hkm.symm _ (ha k) z ?_).1
  rwa [he, closure_ball _ hr.ne']

/-- All placed roots avoid the original circle, including its own root. -/
theorem SourceIsolatingNeighborhoods.originalRootPlacement_avoids_sphere
    {hp : p ≠ ⊤} {hp1 : 1 < p} {V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (a : Coeff p) (ha : a ∈ sourcePsiOriginalRootPlacement D)
    (m k : ℤ) (d r : ℝ) (hr : 0 < r) (he : D m = ball (d:ℂ) r)
    (z : ℂ) (hz : z ∈ sphere (d:ℂ) r) : z ≠ displacedRoots a k := by
  by_cases hkm : k = m
  · subst k
    intro heq
    have hm := ha m
    rw [he, ← heq, mem_ball] at hm
    exact (ne_of_lt hm) (mem_sphere.mp hz)
  · exact hD.originalRootPlacement_avoids_closedBall a ha m k hkm d r hr he z
      (sphere_subset_closedBall hz)

end NLS.ZakharovShabat
