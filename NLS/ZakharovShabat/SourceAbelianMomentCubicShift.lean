import NLS.ZakharovShabat.SourceAbelianMomentQuadraticShift

/-! # The cubic shift of normalized psi moments

Expanding F₀ = Fₖ − iπk leaves the weighted second moment and the exact
zeroth period. Their finite sum has the H₄ free dispersion (2πn)^3.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}

/-- The cubic shift identity on any actual admissible circle. -/
theorem sourceAbelianMomentCircle_cubic_shift
    (n k : ℤ) (a : Coeff p) (ψ : CoeffPair p) (D : SourceAbelianSpectralChart hp hp1 W ψ)
    (c : ℂ) (R : ℝ) (hR : 0 ≤ R) (hcircle : sphere c R ⊆ sourceCanonicalRootDomain hp hp1 ψ) :
    sourceAbelianMomentCircle hp hp1 W n 0 3 a ψ c R =
      sourceAbelianMomentCircle hp hp1 W n k 3 a ψ c R-
        (3*I*(Real.pi:ℂ)*k)*sourceAbelianMomentCircle hp hp1 W n k 2 a ψ c R-
        (3*((Real.pi:ℂ)*k)^2)*sourceAbelianMomentCircle hp hp1 W n k 1 a ψ c R+
        (I*((Real.pi:ℂ)*k)^3)*sourceAbelianMomentCircle hp hp1 W n k 0 a ψ c R := by
  let f (m : ℕ) (z : ℂ) := sourceAbelianMomentIntegrand hp hp1 W n k m (z,(a,ψ))
  have hci (m : ℕ) : CircleIntegrable (f m) c R :=
    ((analyticOnNhd_sourceAbelianMomentIntegrand_fixed hp hp1 W n k m a ψ D).continuousOn.mono hcircle).circleIntegrable hR
  have he (z : ℂ) (hz : z ∈ sphere c R) :
      sourceAbelianMomentIntegrand hp hp1 W n 0 3 (z,(a,ψ)) =
        f 3 z-(3*I*(Real.pi:ℂ)*k)*f 2 z-(3*((Real.pi:ℂ)*k)^2)*f 1 z+
          (I*((Real.pi:ℂ)*k)^3)*f 0 z := by
    dsimp [f,sourceAbelianMomentIntegrand]
    rw [sourceFullAbelianPrimitive_index_shift D k z
      (sourceCanonicalRootDomain_subset_openGapComplement hp hp1 ψ (hcircle hz))]
    simp only [pow_one,pow_zero,one_mul]
    ring_nf
    simp only [I_sq,I_pow_three]
    ring
  have hci2 : CircleIntegrable (fun z => (3*I*(Real.pi:ℂ)*k)*f 2 z) c R := (hci 2).const_mul (3*I*(Real.pi:ℂ)*k)
  have hci1 : CircleIntegrable (fun z => (3*((Real.pi:ℂ)*k)^2)*f 1 z) c R := (hci 1).const_mul (3*((Real.pi:ℂ)*k)^2)
  have hci0 : CircleIntegrable (fun z => (I*((Real.pi:ℂ)*k)^3)*f 0 z) c R := (hci 0).const_mul (I*((Real.pi:ℂ)*k)^3)
  have hci32 : CircleIntegrable (fun z => f 3 z-(3*I*(Real.pi:ℂ)*k)*f 2 z) c R := (hci 3).sub hci2
  have hci321 : CircleIntegrable (fun z => f 3 z-(3*I*(Real.pi:ℂ)*k)*f 2 z-
      (3*((Real.pi:ℂ)*k)^2)*f 1 z) c R := hci32.sub hci1
  calc
    _ = ∮ z in C(c,R), f 3 z-(3*I*(Real.pi:ℂ)*k)*f 2 z-
        (3*((Real.pi:ℂ)*k)^2)*f 1 z+(I*((Real.pi:ℂ)*k)^3)*f 0 z :=
      circleIntegral.integral_congr hR he
    _ = _ := by
      rw [circleIntegral.integral_add hci321 hci0,
        circleIntegral.integral_sub hci32 hci1,
        circleIntegral.integral_sub (hci 3) hci2]
      simp only [circleIntegral.integral_const_mul]
      rfl

namespace SourceAbelianMomentAtlas
variable {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
variable (A : SourceAbelianMomentAtlas hp hp1 W s)

/-- Odd moments vanish on the actual local circles, including collapsed gaps. -/
theorem unshifted_cubic_circle (φ : realTypeSourceLocus p) (ψ : CoeffPair p)
    (hψ : ψ ∈ A.sourceBall φ) (n k : ℤ) :
    sourceAbelianMomentCircle hp hp1 W n 0 3 (s n ψ : Coeff p) ψ
      ((A.localChart φ).center k) ((A.localChart φ).contourRadius k) =
        -(3*I*(Real.pi:ℂ)*k)*A.moment n k 2 ψ+
          (I*((Real.pi:ℂ)*k)^3)*((2*Real.pi:ℂ)*(if k=n then 1 else 0)) := by
  obtain ⟨D⟩ := (A.localChart φ).charts ψ hψ
  have hfamily := (A.localChart φ).family ψ hψ
  have hψU : ψ ∈ A.domain := mem_iUnion.mpr ⟨φ,hψ⟩
  rw [sourceAbelianMomentCircle_cubic_shift n k (s n ψ : Coeff p) ψ D _ _
    (hfamily.2 k).1.le (hfamily.2 k).2.2.2]
  change A.localMoment φ n k 3 ψ-(3*I*(Real.pi:ℂ)*k)*A.localMoment φ n k 2 ψ-
    (3*((Real.pi:ℂ)*k)^2)*A.localMoment φ n k 1 ψ+
    (I*((Real.pi:ℂ)*k)^3)*A.localMoment φ n k 0 ψ = _
  rw [← A.moment_eq_local n k 3 φ hψ,← A.moment_eq_local n k 2 φ hψ,
    ← A.moment_eq_local n k 1 φ hψ,← A.moment_eq_local n k 0 φ hψ,
    A.moment_odd ψ hψU n k 1,A.moment_odd ψ hψU n k 0,A.moment_zero_order ψ hψU n k]
  ring

/-- Finite gap support also supports every weighted positive moment sum. -/
theorem weighted_positive_moment_hasSum_of_gap_support (ψ : CoeffPair p) (hψ : ψ ∈ A.domain)
    (S : Finset ℤ)
    (hS : ∀ k ∉ S, canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) k = 0)
    (w : ℤ → ℂ) (n : ℤ) (m : ℕ) :
    HasSum (fun k => w k*A.moment n k (m+1) ψ) (∑ k ∈ S, w k*A.moment n k (m+1) ψ) := by
  apply hasSum_sum_of_ne_finset_zero
  intro k hk
  rw [A.moment_succ_of_collapsed ψ hψ n k (hS k hk) m,mul_zero]

/-- Fixed finite gap support permits weighted positive-moment sums to
pass through an arbitrary source limit, including collapsing gaps. -/
theorem weighted_positive_moment_sum_tendsto_of_eventually_fixed_gap_support
    {ι : Type*} {l : Filter ι} [l.NeBot] (ψ : ι → CoeffPair p) (φ : CoeffPair p)
    (hφ : φ ∈ A.domain) (hlim : Filter.Tendsto ψ l (nhds φ)) (S : Finset ℤ)
    (hS : ∀ᶠ i in l, ψ i ∈ A.domain ∧ ∀ k ∉ S,
      canonicalPeriodicGap hp hp1 (periodOnePotential (ψ i)) (periodOnePotential_mem (ψ i)) k = 0)
    (w : ℤ → ℂ) (n : ℤ) (m : ℕ) :
    Filter.Tendsto (fun i => ∑' k : ℤ, w k*A.moment n k (m+1) (ψ i)) l
      (nhds (∑' k : ℤ, w k*A.moment n k (m+1) φ)) := by
  have hterm (k : ℤ) : Filter.Tendsto (fun i => w k*A.moment n k (m+1) (ψ i)) l
      (nhds (w k*A.moment n k (m+1) φ)) :=
    ((A.analytic_moment n k (m+1) φ hφ).continuousAt.tendsto.comp hlim).const_mul (w k)
  have hzero (k : ℤ) (hk : k ∉ S) : w k*A.moment n k (m+1) φ = 0 := by
    have he : ∀ᶠ i in l, w k*A.moment n k (m+1) (ψ i) = 0 := hS.mono (fun i hi => by
      rw [A.moment_succ_of_collapsed (ψ i) hi.1 n k (hi.2 k hk) m,mul_zero])
    exact tendsto_nhds_unique (hterm k) (tendsto_const_nhds.congr' (he.mono (fun _ h => h.symm)))
  rw [tsum_eq_sum hzero]
  have hfinite := tendsto_finsetSum S (fun k _ => hterm k)
  apply hfinite.congr'
  filter_upwards [hS] with i hi
  exact (A.weighted_positive_moment_hasSum_of_gap_support (ψ i) hi.1 S hi.2 w n m).tsum_eq.symm

/-- The cubic contour contributes exactly the cubic free frequency and
−12 times the actual weighted second-moment sum. -/
theorem cubic_contour_sum_renormalization (φ : realTypeSourceLocus p) (ψ : CoeffPair p)
    (hψ : ψ ∈ A.sourceBall φ) (S : Finset ℤ)
    (hS : ∀ k ∉ S, canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) k = 0)
    (n : ℤ) (hn : n ∈ S) :
    -(4*I/Real.pi:ℂ)*(∑ k ∈ S, sourceAbelianMomentCircle hp hp1 W n 0 3
      (s n ψ : Coeff p) ψ ((A.localChart φ).center k) ((A.localChart φ).contourRadius k))-
      (2*(n:ℂ)*Real.pi)^3 = -12*(∑' k : ℤ, (k:ℂ)*A.moment n k 2 ψ) := by
  have hψU : ψ ∈ A.domain := mem_iUnion.mpr ⟨φ,hψ⟩
  have hsum := (A.weighted_positive_moment_hasSum_of_gap_support ψ hψU S hS
    (fun k => (k:ℂ)) n 1).tsum_eq
  simp_rw [A.unshifted_cubic_circle φ ψ hψ n]
  rw [Finset.sum_add_distrib,hsum]
  have hfirst : (∑ k ∈ S, -(3*I*(Real.pi:ℂ)*k)*A.moment n k 2 ψ) =
      -(3*I*(Real.pi:ℂ))*(∑ k ∈ S, (k:ℂ)*A.moment n k 2 ψ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hdelta : (∑ k ∈ S, (I*((Real.pi:ℂ)*k)^3)*((2*Real.pi:ℂ)*(if k=n then 1 else 0))) =
      (I*((Real.pi:ℂ)*n)^3)*(2*Real.pi:ℂ) := by simp [mul_ite,hn]
  rw [hfirst,hdelta]
  have hπ : (Real.pi:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp
  ring_nf
  simp only [I_sq]
  ring

end SourceAbelianMomentAtlas
end NLS.ZakharovShabat
