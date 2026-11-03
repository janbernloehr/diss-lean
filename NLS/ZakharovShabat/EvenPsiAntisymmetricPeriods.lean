import NLS.ZakharovShabat.EvenDiscriminantCanonicalRoot
import NLS.ZakharovShabat.SourceTheorem12_1
import NLS.ZakharovShabat.SourcePsiLemma12_10
import NLS.ComplexAnalysis.NegatedCircleIntegral

/-! # Exact periods of the antisymmetrized normalized numerator

The original circle reflected through zero is an actual isolating circle
at the opposite index. Oddness of the actual canonical root and the circle
change of variable give the difference of the two Kronecker periods.
-/
noncomputable section
open Set Metric Complex
open NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem SourceSpectralIsolationNeighborhood.nonempty_periodCircles
    {hp : p ≠ ⊤} {hp1 : 1 < p} {A : Set (CoeffPair p)}
    (hA : SourceSpectralIsolationNeighborhood hp hp1 A) (ψ : CoeffPair p) (hψ : ψ ∈ A) :
    Nonempty ((m : ℤ) → SourceCriticalRootPeriodCircle hp hp1 ψ m) := by
  obtain ⟨V,_,_,hψV,_,φ,N,ε,hε,_,_,hgap,hdisj⟩ := hA.2.2.2 ψ hψ
  let c := sourceIsolatingCenter hp hp1 φ N
  let r := sourceIsolatingRadius hp hp1 φ N ε
  have hc (k : ℤ) : ((c k).re:ℂ) = c k := by
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im] using
        (sourceIsolatingCenter_im_eq_zero hp hp1 φ N k).symm
  have hg (k : ℤ) : sourcePeriodicSegment hp hp1 ψ k ⊆ ball (c k) (r k) := by
    simpa only [sourceIsolatingDisc_eq_ball] using hgap ψ hψV k
  have hr (k : ℤ) : 0 < r k := sourceIsolatingRadius_pos hp hp1 φ N ε hε k
  refine ⟨fun m => ⟨(c m).re,r m,hr m,by rw [hc];exact hg m,?_⟩⟩
  intro k hkm z hz
  have hd : Disjoint (ball ((c m).re:ℂ) (r m)) (ball ((c k).re:ℂ) (r k)) := by
    rw [hc,hc]
    simpa only [sourceIsolatingDisc_eq_ball] using hdisj m k hkm.symm
  exact re_separated_of_disjoint_realCenteredBalls (hr m) (hr k) hd
    (by rw [hc];exact hg k hz)

def SourceCriticalRootPeriodCircle.neg_reflect
    {hp : p ≠ ⊤} {hp1 : 1 < p} {ψ : CoeffPair p} {m : ℤ}
    (D : SourceCriticalRootPeriodCircle hp hp1 ψ m)
    (heven : ∀ z, canonicalDiscriminant hp (periodOnePotential ψ) (-z) =
      canonicalDiscriminant hp (periodOnePotential ψ) z) :
    SourceCriticalRootPeriodCircle hp hp1 ψ (-m) where
  center := -D.center
  radius := D.radius
  radius_pos := D.radius_pos
  gap := by
    intro z hz
    have hn := (neg_mem_sourcePeriodicSegment_iff_of_discriminant_even hp hp1 ψ heven m z).mpr hz
    have hb := D.gap hn
    simp only [mem_ball,dist_eq_norm,ofReal_neg] at hb ⊢
    rw [show z- -(D.center:ℂ) = -(-z-(D.center:ℂ)) by ring,norm_neg]
    exact hb
  other := by
    intro k hk w hw
    have hkm : -k ≠ m := by intro h; apply hk; simpa only [neg_neg] using congrArg Neg.neg h
    have hn := (neg_mem_sourcePeriodicSegment_iff_of_discriminant_even hp hp1 ψ heven (-k) w).mpr
      (by simpa only [neg_neg] using hw)
    have he := D.other (-k) hkm (-w) hn
    simp only [neg_re] at he
    rcases he with h | h
    · exact Or.inr (by linarith)
    · exact Or.inl (by linarith)

namespace SourceTheorem12_1Data
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

theorem raw_period (H : SourceTheorem12_1Data hp hp1 W₀ W s)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (n m : ℤ)
    (D : SourceCriticalRootPeriodCircle hp hp1 ψ m) :
    (∮ z in C((D.center:ℂ),D.radius),
      sourcePsiCandidate n (z,(s n ψ : Coeff p))/sourceCanonicalRoot hp hp1 ψ z) =
        (2*Real.pi:ℂ)*(if m = n then 1 else 0) := by
  have hπ : (2*Real.pi:ℂ) ≠ 0 :=
    mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)
  have h := H.period ψ hψ n m D
  unfold sourcePsiContour sourcePsiContourIntegrandJoint at h
  have he := congrArg (fun w : ℂ => (2*Real.pi:ℂ)*w) h
  simpa only [← mul_assoc,mul_inv_cancel₀ hπ,one_mul] using he

theorem antisymmetric_raw_period (H : SourceTheorem12_1Data hp hp1 W₀ W s)
    (ψ : CoeffPair p) (hψ : ψ ∈ W)
    (heven : ∀ z, canonicalDiscriminant hp (periodOnePotential ψ) (-z) =
      canonicalDiscriminant hp (periodOnePotential ψ) z)
    (n m : ℤ) (D : SourceCriticalRootPeriodCircle hp hp1 ψ m) :
    (∮ z in C((D.center:ℂ),D.radius),
      (sourcePsiCandidate n (z,(s n ψ : Coeff p))-
        sourcePsiCandidate n (-z,(s n ψ : Coeff p)))/sourceCanonicalRoot hp hp1 ψ z) =
      (2*Real.pi:ℂ)*((if m = n then 1 else 0)-(if -m = n then 1 else 0)) := by
  let f : ℂ → ℂ := fun z => sourcePsiCandidate n (z,(s n ψ : Coeff p))/sourceCanonicalRoot hp hp1 ψ z
  let g : ℂ → ℂ := fun z => sourcePsiCandidate n (-z,(s n ψ : Coeff p))/sourceCanonicalRoot hp hp1 ψ z
  have hf : CircleIntegrable f (D.center:ℂ) D.radius :=
    ((analyticOnNhd_sourcePsiContourIntegrand_fixed hp hp1 n (s n ψ : Coeff p) ψ).continuousOn.mono
      D.sphere_subset_rootDomain).circleIntegrable D.radius_pos.le
  have hg : CircleIntegrable g (D.center:ℂ) D.radius := by
    apply ContinuousOn.circleIntegrable D.radius_pos.le
    intro z hz
    have ha := ((analyticOnNhd_sourcePsiCandidate hp hp1 n (-z,(s n ψ : Coeff p)) (mem_univ _)).comp
      (f := fun w : ℂ => (-w,(s n ψ : Coeff p))) (analyticAt_id.neg.prod analyticAt_const))
    exact (ha.div (sourceCanonicalRoot_analyticOnNhd hp hp1 ψ z (D.sphere_subset_rootDomain hz))
      (sourceCanonicalRoot_ne_zero_off_gaps hp hp1 ψ z (D.sphere_subset_rootDomain hz))).continuousAt.continuousWithinAt
  have he : g = fun z => -f (-z) := by
    funext z
    simp only [f,g,sourceCanonicalRoot_neg_of_discriminant_even hp hp1 ψ heven,div_neg,neg_neg]
  have hneg : (∮ z in C((D.center:ℂ),D.radius), g z) =
      ∮ z in C(((-D.center:ℝ):ℂ),D.radius), f z := by
    rw [he]
    have hm : (fun z => -f (-z)) = fun z => (-1:ℂ)*f (-z) := by funext z;ring
    rw [hm,circleIntegral.integral_const_mul,circleIntegral_comp_neg]
    simp only [neg_one_mul,neg_neg,ofReal_neg]
  have hsplit : (fun z => (sourcePsiCandidate n (z,(s n ψ : Coeff p))-
      sourcePsiCandidate n (-z,(s n ψ : Coeff p)))/sourceCanonicalRoot hp hp1 ψ z) =
        fun z => f z-g z := by funext z; dsimp [f,g];ring
  have ho := H.raw_period ψ hψ n (-m) (D.neg_reflect heven)
  change (∮ z in C(((-D.center:ℝ):ℂ),D.radius), f z) = _ at ho
  rw [hsplit,circleIntegral.integral_sub hf hg,hneg,H.raw_period ψ hψ n m D,ho]
  ring

end SourceTheorem12_1Data
end NLS.ZakharovShabat
