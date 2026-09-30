import NLS.ZakharovShabat.SourcePsiIsolatingFiniteGeometry
import NLS.ZakharovShabat.SourcePsiExteriorNormalization
import NLS.ZakharovShabat.SourcePsiGapRootMap

/-!
# Exact normalization of the real psi gap solutions

The actual large-circle limit and the finite decomposition give the
omitted period exactly one once all retained periods vanish. For real
gap solutions, contour comparison supplies those zeros on the circles
constructed from the actual isolating discs. A second comparison gives
the same exact normalization on every valid real-centered gap circle.
-/

noncomputable section
open Set Filter Topology Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

namespace SourcePsiIsolatingCircleFamily
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {φ ψ : CoeffPair p} {N : ℕ} {ε : ℝ}

/-- Vanishing retained periods force exact omitted normalization on
the actual all-index isolating family, also at complex sources. -/
theorem omitted_contour_eq_one_of_retained_zero
    (C : SourcePsiIsolatingCircleFamily hp hp1 φ ψ N ε) (n : ℤ) (a : Coeff p)
    (hzero : ∀ m, m ≠ n → sourcePsiContour hp hp1 n a ψ
      (sourceIsolatingCenter hp hp1 φ N m) (C.inner m) = 0) :
    sourcePsiContour hp hp1 n a ψ (sourceIsolatingCenter hp hp1 φ N n) (C.inner n) = 1 := by
  have heq : ∀ᶠ k : ℕ in atTop,
      sourcePsiContour hp hp1 n a ψ 0 (centralCircleRadius k) =
        sourcePsiContour hp hp1 n a ψ (sourceIsolatingCenter hp hp1 φ N n) (C.inner n) := by
    filter_upwards [C.eventually_finite_geometry,eventually_ge_atTop n.natAbs] with k hG hk
    have hn : n ∈ Finset.Icc (-(k : ℤ)) (k : ℤ) := by
      simp only [Finset.mem_Icc]
      omega
    exact hG.eq_omitted_of_retained_zero n hn a (fun m _ hmn => hzero m hmn)
  have hlim := (tendsto_centralCircle_sourcePsiContour hp hp1 n a ψ).congr' heq
  exact tendsto_nhds_unique tendsto_const_nhds hlim

end SourcePsiIsolatingCircleFamily

/-- Every retained contour of a real gap solution vanishes on every
valid real-centered family, independently of its equation chart. -/
theorem sourcePsiContour_zero_of_gapSolution
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (a : DeletedCoeff p n)
    (hsol : SourcePsiGapSolution hp hp1 n φ a)
    (c : ℤ → ℂ) (R : ℤ → ℝ)
    (hfamily : sourcePsiRealCenteredContourFamily hp hp1 φ c R)
    (m : ℤ) (hm : m ≠ n) :
    sourcePsiContour hp hp1 n (a : Coeff p) φ (c m) (R m) = 0 := by
  obtain ⟨_,c₀,R₀,hcenter₀,hgeom₀,hcoord₀,hzero₀⟩ := hsol
  have hcoord := hcoord₀ m
  rw [hzero₀] at hcoord
  have hF : sourcePsiEquationCoordinate hp hp1 n m (a : Coeff p) φ (c₀ m) (R₀ m) = 0 :=
    by simpa using hcoord.symm
  have hfactor : ((n-m : ℤ) : ℂ)*(2*Real.pi : ℂ) ≠ 0 := by
    apply mul_ne_zero
    · exact_mod_cast sub_ne_zero.mpr hm.symm
    · exact mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)
  have hzero : sourcePsiContour hp hp1 n (a : Coeff p) φ (c₀ m) (R₀ m) = 0 :=
    (mul_eq_zero.mp hF).resolve_left hfactor
  rw [sourcePsiContour_eq_of_realCentered_enclosingCircles hp hp1 n m (a : Coeff p) φ hφ
    (c m) (c₀ m) (R m) (R₀ m) (hfamily.1 m) (hcenter₀ m)
    (hfamily.2 m).1 (hgeom₀ m).1 (hfamily.2 m).2.1 (hgeom₀ m).2.1
    (hfamily.2 m).2.2.1 (hgeom₀ m).2.2]
  exact hzero

/-- The omitted contour of any real gap solution is exactly one on
every positive real-centered circle enclosing its gap and avoiding
all other gaps in its filled disc. -/
theorem sourcePsiContour_eq_one_of_gapSolution
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (a : DeletedCoeff p n)
    (hsol : SourcePsiGapSolution hp hp1 n φ a)
    (c : ℂ) (R : ℝ) (hc : c.im = 0) (hR : 0 < R)
    (hseg : sourcePeriodicSegment hp hp1 φ n ⊆ ball c R)
    (hother : closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 φ n) :
    sourcePsiContour hp hp1 n (a : Coeff p) φ c R = 1 := by
  obtain ⟨N,ε,_,_,U,_,hφU,hcluster,hdisj⟩ :=
    exists_local_source_pairwise_disjoint_isolating_discs hp hp1 φ hφ
  obtain ⟨C⟩ := nonempty_sourcePsiIsolatingCircleFamily hp hp1 φ φ N ε
    (fun m => sourcePeriodicSegment_subset_isolatingDisc hp hp1 φ φ N ε m (hcluster φ hφU m)) hdisj
  have hnorm := C.omitted_contour_eq_one_of_retained_zero n (a : Coeff p)
    (sourcePsiContour_zero_of_gapSolution hp hp1 n φ hφ a hsol _ _ C.contour_family)
  rw [sourcePsiContour_eq_of_realCentered_enclosingCircles hp hp1 n n (a : Coeff p) φ hφ
    c (sourceIsolatingCenter hp hp1 φ N n) R (C.inner n)
    hc (C.contour_family.1 n) hR (C.inner_pos n) hseg (C.gap_enclosed n)
    hother (C.contour_family.2 n).2.2.1]
  exact hnorm

/-- Exact real-type orthogonality for the canonical psi roots. -/
theorem sourcePsiGapRoot_contour_orthogonality
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (φ : realTypeSourceLocus p)
    (c : ℤ → ℂ) (R : ℤ → ℝ)
    (hfamily : sourcePsiRealCenteredContourFamily hp hp1 φ.val c R) (m : ℤ) :
    sourcePsiContour hp hp1 n (sourcePsiGapRoot hp hp1 n φ : Coeff p) φ.val (c m) (R m) =
      if m = n then 1 else 0 := by
  by_cases hmn : m = n
  · subst m
    rw [if_pos rfl]
    exact sourcePsiContour_eq_one_of_gapSolution hp hp1 n φ.val φ.property
      (sourcePsiGapRoot hp hp1 n φ) (sourcePsiGapRoot_solution hp hp1 n φ)
      (c n) (R n) (hfamily.1 n) (hfamily.2 n).1 (hfamily.2 n).2.1 (hfamily.2 n).2.2.1
  · rw [if_neg hmn]
    exact sourcePsiContour_zero_of_gapSolution hp hp1 n φ.val φ.property
      (sourcePsiGapRoot hp hp1 n φ) (sourcePsiGapRoot_solution hp hp1 n φ) c R hfamily m hmn

/-- The literal omitted raw contour integral of a real gap solution
has the dissertation's normalization 2 pi. -/
theorem sourcePsi_raw_integral_eq_two_pi_of_gapSolution
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (a : DeletedCoeff p n)
    (hsol : SourcePsiGapSolution hp hp1 n φ a)
    (c : ℂ) (R : ℝ) (hc : c.im = 0) (hR : 0 < R)
    (hseg : sourcePeriodicSegment hp hp1 φ n ⊆ ball c R)
    (hother : closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 φ n) :
    (∮ z in C(c,R), sourcePsiContourIntegrandJoint hp hp1 n (z,((a : Coeff p),φ))) =
      (2*Real.pi : ℂ) := by
  have hnorm := sourcePsiContour_eq_one_of_gapSolution hp hp1 n φ hφ a hsol c R hc hR hseg hother
  have hπ : (2*Real.pi : ℂ) ≠ 0 :=
    mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)
  unfold sourcePsiContour at hnorm
  have h := congrArg (fun w : ℂ => (2*Real.pi : ℂ)*w) hnorm
  simpa only [← mul_assoc,mul_inv_cancel₀ hπ,one_mul,mul_one] using h

end NLS.ZakharovShabat
