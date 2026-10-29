import NLS.ComplexAnalysis.WeightedArgumentPrinciple
import NLS.ZakharovShabat.SourceLemma10_2
import NLS.ZakharovShabat.SourceIsolatingMultiplicity

/-! The literal discriminant contours in the proof of Lemma 10.2.
Every original isolating family is retained, including its central discs.
Repeated endpoints contribute their actual algebraic multiplicity. -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Any common isolating family identifies multiplicity with the two
indexed endpoint slots, without requiring a particular choice of discs. -/
theorem SourceIsolatingNeighborhoods.periodicMultiplicity_eq_pair_count
    {hp : p ≠ ⊤} {hp1 : 1 < p} {V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {C : ℝ} (H : SourceIsolatingNeighborhoods hp hp1 V D C)
    (ψ : CoeffPair p) (hψ : ψ ∈ V) (n : ℤ) {z : ℂ}
    (hz : z ∈ D n) (hspec : z ∈ periodicSpectrum hp (periodOnePotential ψ)) :
    periodicAlgebraicMultiplicity hp (periodOnePotential ψ) z =
      ({canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n,
        canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n} : Multiset ℂ).count z := by
  classical
  let L := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ)
  let R := canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ)
  let K := max (canonicalPeriodicCutoff hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ)) n.natAbs
  have hlabel := (canonicalPeriodicEndpoints_spec hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ)).1
  have hcentral := hlabel.central_at_larger_cutoff K (le_max_left _ _)
  have hnK : n ∈ Finset.Icc (-(K : ℤ)) (K : ℤ) := by
    simp only [Finset.mem_Icc]
    have hnat : n.natAbs ≤ K := le_max_right _ _
    omega
  have hroot : z = L n ∨ z = R n := by
    obtain ⟨m,hm⟩ := (canonicalPeriodicEndpoints_exhaustive hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ) z).mp hspec
    have hzm : z ∈ D m := hm.elim
      (fun h => h ▸ H.cluster ψ hψ m (Or.inl rfl))
      (fun h => h ▸ H.cluster ψ hψ m (Or.inr (Or.inl rfl)))
    have hmn : m = n := by
      by_contra hne
      exact Set.disjoint_left.mp (H.disjoint n m (Ne.symm hne)) hz hzm
    subst m
    exact hm.imp Eq.symm Eq.symm
  have hzcentral : z ∈ centralPeriodicSpectrum hp (periodOnePotential ψ) K :=
    (hcentral.root_iff z).mp ⟨n,by omega,by simpa only [eq_comm] using hroot⟩
  have hzero (m : ℤ) (hmn : m ≠ n) : ({L m,R m} : Multiset ℂ).count z = 0 := by
    apply Multiset.count_eq_zero.mpr
    intro hm
    have hm' : z = L m ∨ z = R m := by simpa using hm
    have hzm : z ∈ D m := hm'.elim
      (fun h => h ▸ H.cluster ψ hψ m (Or.inl rfl))
      (fun h => h ▸ H.cluster ψ hψ m (Or.inr (Or.inl rfl)))
    exact Set.disjoint_left.mp (H.disjoint n m hmn.symm) hz hzm
  have hsum : (∑ m ∈ Finset.Icc (-(K : ℤ)) K, ({L m,R m} : Multiset ℂ).count z) =
      ({L n,R n} : Multiset ℂ).count z := by
    apply Finset.sum_eq_single n
    · intro m hm hmn
      exact hzero m hmn
    · intro hn
      exact False.elim (hn hnK)
  have hcount := hcentral.count_eq z
  rw [hsum,if_pos hzcentral] at hcount
  exact hcount.symm

/-- An analytic spectral weight recovers its two actual endpoint values
from the original fixed discriminant contour, also for a collapsed pair. -/
theorem SourceIsolatingNeighborhoods.weighted_discriminant_contour
    {hp : p ≠ ⊤} {hp1 : 1 < p} {V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {C : ℝ} (H : SourceIsolatingNeighborhoods hp hp1 V D C)
    (ψ : CoeffPair p) (hψ : ψ ∈ V) (n : ℤ) (c : ℂ) (r : ℝ)
    (hr : 0 < r) (hD : D n = ball c r) (q : ℂ → ℂ)
    (hq : AnalyticOnNhd ℂ q (closedBall c r)) :
    q (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)+
      q (canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n) =
      (2*Real.pi*I : ℂ)⁻¹ * (∮ z in C(c,r),
        (2*canonicalDiscriminant hp (periodOnePotential ψ) z*
          deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
          ((canonicalDiscriminant hp (periodOnePotential ψ) z)^2-4))*q z) := by
  classical
  let a := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n
  let b := canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n
  let Δ := canonicalDiscriminant hp (periodOnePotential ψ)
  let f := fun z : ℂ => (Δ z)^2-4
  have ha : a ∈ ball c r := hD ▸ H.cluster ψ hψ n (Or.inl rfl)
  have hb : b ∈ ball c r := hD ▸ H.cluster ψ hψ n (Or.inr (Or.inl rfl))
  have hΔ : AnalyticOnNhd ℂ Δ univ :=
    analyticOnNhd_canonicalDiscriminant hp hp1 _ (periodOnePotential_mem ψ)
  have hf : AnalyticOnNhd ℂ f (closedBall c r) := ((hΔ.pow 2).sub analyticOnNhd_const).mono (subset_univ _)
  have hroots (z : ℂ) (hz : z ∈ closedBall c r) (hfz : f z = 0) : z = a ∨ z = b := by
    have hspec := (canonicalDiscriminant_sq_eq_four_iff_finite hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ) z).mp (sub_eq_zero.mp hfz)
    obtain ⟨m,hm⟩ := (canonicalPeriodicEndpoints_exhaustive hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ) z).mp hspec
    have hzm : z ∈ D m := hm.elim
      (fun h => h ▸ H.cluster ψ hψ m (Or.inl rfl))
      (fun h => h ▸ H.cluster ψ hψ m (Or.inr (Or.inl rfl)))
    have hmn : m = n := by
      by_contra hne
      obtain ⟨u,s,_,hs⟩ := H.discs m
      have hopen : IsOpen (D m) := hs ▸ isOpen_ball
      have hzcl : z ∈ closure (D n) := by rw [hD,closure_ball _ hr.ne']; exact hz
      exact Set.disjoint_left.mp ((H.disjoint n m (Ne.symm hne)).closure_left hopen) hzcl hzm
    subst m
    exact hm.imp Eq.symm Eq.symm
  have hboundary (z : ℂ) (hz : z ∈ sphere c r) : f z ≠ 0 := by
    intro hzero
    rcases hroots z (sphere_subset_closedBall hz) hzero with rfl | rfl
    · exact sphere_disjoint_ball.le_bot ⟨hz,ha⟩
    · exact sphere_disjoint_ball.le_bot ⟨hz,hb⟩
  have hfinite (z : ℂ) (hz : z ∈ closedBall c r) : analyticOrderAt f z ≠ ⊤ := by
    rw [show analyticOrderAt f z = (periodicAlgebraicMultiplicity hp (periodOnePotential ψ) z : ℕ∞) from
      analyticOrderAt_canonicalDiscriminant_sq_sub_four hp hp1 _ (periodOnePotential_mem ψ) z]
    simp
  have hs : (({a,b} : Finset ℂ) : Set ℂ) ⊆ ball c r := by
    intro z hz
    simp only [Finset.coe_insert,Finset.coe_singleton,Set.mem_insert_iff,Set.mem_singleton_iff] at hz
    exact hz.elim (fun h => h ▸ ha) (fun h => h ▸ hb)
  have hcount (z : ℂ) (hz : z ∈ ({a,b} : Finset ℂ)) :
      analyticOrderNatAt f z = ({a,b} : Multiset ℂ).count z := by
    have hzball := hs hz
    have hspec : z ∈ periodicSpectrum hp (periodOnePotential ψ) := by
      simp only [Finset.mem_insert,Finset.mem_singleton] at hz
      obtain ⟨hL,hR⟩ := canonicalPeriodicEndpoints_mem_spectrum hp hp1
        (periodOnePotential ψ) (periodOnePotential_mem ψ) n
      exact hz.elim (fun h => h ▸ hL) (fun h => h ▸ hR)
    have hmul := H.periodicMultiplicity_eq_pair_count ψ hψ n (hD ▸ hzball) hspec
    have ho : (analyticOrderNatAt f z : ℕ∞) =
        (periodicAlgebraicMultiplicity hp (periodOnePotential ψ) z : ℕ∞) := by
      rw [Nat.cast_analyticOrderNatAt (hfinite z (ball_subset_closedBall hzball))]
      exact analyticOrderAt_canonicalDiscriminant_sq_sub_four hp hp1 _ (periodOnePotential_mem ψ) z
    have hon : analyticOrderNatAt f z = periodicAlgebraicMultiplicity hp (periodOnePotential ψ) z := by exact_mod_cast ho
    exact hon.trans hmul
  have hint := circleIntegral_weighted_logDeriv_eq_sum hr hf hq hboundary hfinite {a,b} hs
    (fun z hz hzero => by simpa only [Finset.mem_insert,Finset.mem_singleton] using hroots z hz hzero)
  have hsum : (∑ z ∈ ({a,b} : Finset ℂ), (analyticOrderNatAt f z : ℂ)*q z) = q a+q b := by
    trans ∑ z ∈ ({a,b} : Finset ℂ), (({a,b} : Multiset ℂ).count z : ℂ)*q z
    · exact Finset.sum_congr rfl (fun z hz => by rw [hcount z hz])
    · by_cases hab : a = b
      · rw [← hab]
        simp [two_mul]
      · simp [hab,Ne.symm hab]
  rw [hsum] at hint
  have hlog (z : ℂ) : logDeriv f z = 2*Δ z*deriv Δ z/f z := by
    have hd := (((hΔ z (mem_univ _)).differentiableAt.hasDerivAt.pow 2).sub_const (4 : ℂ)).deriv
    change deriv f z / f z = _
    have hd' : deriv f z = 2*Δ z*deriv Δ z := by
      change deriv f z = 2*Δ z^(1 : ℕ)*deriv Δ z at hd
      simpa only [pow_one] using hd
    rw [hd']
  have he : (∮ z in C(c,r), (2*Δ z*deriv Δ z/f z)*q z) = (2*Real.pi*I)*(q a+q b) := by
    convert hint using 1
    congr 1
    funext z
    rw [hlog]
    ring
  change q a+q b = (2*Real.pi*I : ℂ)⁻¹ * (∮ z in C(c,r), (2*Δ z*deriv Δ z/f z)*q z)
  rw [he,← mul_assoc,inv_mul_cancel₀ (by simp [Real.pi_ne_zero]),one_mul]

/-- The exact power-sum display of Lemma 10.2, valid also for exponent zero. -/
theorem SourceIsolatingNeighborhoods.power_sum_contour
    {hp : p ≠ ⊤} {hp1 : 1 < p} {V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {C : ℝ} (H : SourceIsolatingNeighborhoods hp hp1 V D C)
    (ψ : CoeffPair p) (hψ : ψ ∈ V) (n : ℤ) (c : ℂ) (r : ℝ)
    (hr : 0 < r) (hD : D n = ball c r) (k : ℕ) :
    (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)^k+
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)^k =
      (2*Real.pi*I : ℂ)⁻¹ * (∮ z in C(c,r),
        (2*canonicalDiscriminant hp (periodOnePotential ψ) z*
          deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
          ((canonicalDiscriminant hp (periodOnePotential ψ) z)^2-4))*z^k) :=
  H.weighted_discriminant_contour ψ hψ n c r hr hD (fun z => z^k) (analyticOnNhd_id.pow k)

end NLS.ZakharovShabat
