import NLS.KdV.HillHminusOriginalSheets
import NLS.KdV.HillHminusOneGapPolynomial
import NLS.KdV.HillCanonicalRealLabels

noncomputable section
set_option autoImplicit false
open Set Metric Complex
open NLS.ComplexAnalysis
namespace NLS.KdV

/-- Exact multiplicities identify a native complex pair with the original
physical real pair whenever its two physical endpoints lie in the disc.
Repeated endpoints are included; no open-gap hypothesis is used. -/
theorem HillHminusHighGapPair.multiset_eq_original_real_pair
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
    (n : ℕ+) (r : ℝ) (l u : ℂ)
    (h : HillHminusHighGapPair (hillOriginalHminusSource q) n r l u)
    (p : HillRealHighGapPair (SpectralWeight.one.toCoeff q) n)
    (hl : (p.left : ℂ)∈hillHminusGapSquareDisc n r)
    (hu : (p.right : ℂ)∈hillHminusGapSquareDisc n r) :
    ({l,u} : Multiset ℂ)={(p.left : ℂ),(p.right : ℂ)} := by
  have he : hillHminusRadicand (hillOriginalHminusSource q)=
      hillL2Radicand (SpectralWeight.one.toCoeff q) :=
    funext (hillHminusRadicand_original_source_agreement q hq)
  have hle : ({(p.left : ℂ),(p.right : ℂ)} : Multiset ℂ)≤{l,u} := by
    apply Multiset.le_iff_count.mpr
    intro z
    by_cases hz : z∈({(p.left : ℂ),(p.right : ℂ)} : Multiset ℂ)
    · have hm (w : ℂ) (hw : w∈closedBall (freeHillValue n : ℂ) (n : ℝ))
          (hwd : w∈hillHminusGapSquareDisc n r) :
          ({(p.left : ℂ),(p.right : ℂ)} : Multiset ℂ).count w=({l,u} : Multiset ℂ).count w := by
        rw [←p.orders w hw,←h.multiplicity w hwd,he]
      have hz' : z=(p.left : ℂ) ∨ z=(p.right : ℂ) := by simpa using hz
      rcases hz' with rfl | rfl
      · exact (hm _ p.left_mem hl).le
      · exact (hm _ p.right_mem hu).le
    · simp only [Multiset.count_eq_zero_of_notMem hz,Nat.zero_le]
  exact (Multiset.eq_of_le_of_card_le hle (by simp)).symm

/-- The existing original L2 endpoint localization places both physical
endpoints in the native disc at the explicit high-energy cutoff. -/
theorem HillRealHighGapPair.mem_hminus_gap_disc
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
    (n : ℕ+) (r : ℝ) (hcut : 8*‖q‖≤(n : ℝ))
    (hbound : 4*‖q‖≤Real.pi*(n : ℕ)*r)
    (p : HillRealHighGapPair (SpectralWeight.one.toCoeff q) n) :
    (p.left : ℂ)∈hillHminusGapSquareDisc n r ∧
      (p.right : ℂ)∈hillHminusGapSquareDisc n r := by
  have hc : ((Real.pi : ℂ)*(n : ℕ))^2=(freeHillValue n : ℂ) := by
    simp only [freeHillValue,Int.cast_natCast]
    push_cast
    ring
  have hb (x : ℝ) (hx : |x-freeHillValue n|≤4*‖q‖) :
      (x : ℂ)∈hillHminusGapSquareDisc n r := by
    change dist (x : ℂ) (((Real.pi : ℂ)*(n : ℕ))^2)≤Real.pi*(n : ℕ)*r
    rw [hc,dist_eq_norm,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
    exact hx.trans hbound
  have hl := p.localization q hq n n.property hcut
  exact ⟨hb p.left hl.1,hb p.right hl.2⟩

/-- Native unordered high pairs are the ORIGINAL canonically labelled
physical endpoints, with multiplicity retained at every collapsed gap. -/
theorem HillHminusHighGapPair.multiset_eq_original_labels
    (q : RealPeriodOneHillPotential) (n : ℕ+) (hn : 2≤(n : ℕ))
    (r : ℝ) (l u : ℂ)
    (h : HillHminusHighGapPair (hillOriginalHminusSource q.val) n r l u)
    (hcut : 8*‖q.val‖≤(n : ℝ)) (hbound : 4*‖q.val‖≤Real.pi*(n : ℕ)*r) :
    ({l,u} : Multiset ℂ)=
      {(hillRealLabels q.val q.property.1 q.property.2 (2*(n : ℕ)-1) : ℂ),
        (hillRealLabels q.val q.property.1 q.property.2 (2*(n : ℕ)) : ℂ)} := by
  obtain ⟨p,hleft,hright⟩ := hillRealLabels_high_pair q.val q.property.1 q.property.2 n hn hcut
  obtain ⟨hl,hu⟩ := p.mem_hminus_gap_disc q.val q.property.1 n r hcut hbound
  rw [h.multiset_eq_original_real_pair q.val q.property.1 n r l u p hl hu,hleft,hright]

/-- The intrinsic native analytic polynomial factors through the original
canonical physical endpoints at every explicit admissible high index. -/
theorem hillHminusGapPolynomial_original_labels
    (q : RealPeriodOneHillPotential) (n : ℕ+) (hn : 2≤(n : ℕ))
    (r : ℝ) (hr : 0<r) (l u : ℂ)
    (h : HillHminusHighGapPair (hillOriginalHminusSource q.val) n r l u)
    (hcut : 8*‖q.val‖≤(n : ℝ)) (hbound : 4*‖q.val‖≤Real.pi*(n : ℕ)*r) (z : ℂ) :
    hillHminusGapPolynomial n r (z,hillOriginalHminusSource q.val)=
      (z-(hillRealLabels q.val q.property.1 q.property.2 (2*(n : ℕ)-1) : ℂ))*
      (z-(hillRealLabels q.val q.property.1 q.property.2 (2*(n : ℕ)) : ℂ)) := by
  rw [h.gapPolynomial_eq hr z]
  have he := congrArg (fun s : Multiset ℂ => (s.map (fun w => z-w)).prod)
    (h.multiset_eq_original_labels q n hn r l u hcut hbound)
  simpa using he

/-- The native pair can be relabelled by the original physical endpoint
order, even when the original gap is collapsed. -/
theorem HillHminusHighGapPair.original_labelled_pair
    (q : RealPeriodOneHillPotential) (n : ℕ+) (hn : 2≤(n : ℕ))
    (r : ℝ) (l u : ℂ)
    (h : HillHminusHighGapPair (hillOriginalHminusSource q.val) n r l u)
    (hcut : 8*‖q.val‖≤(n : ℝ)) (hbound : 4*‖q.val‖≤Real.pi*(n : ℕ)*r) :
    HillHminusHighGapPair (hillOriginalHminusSource q.val) n r
      (hillRealLabels q.val q.property.1 q.property.2 (2*(n : ℕ)-1))
      (hillRealLabels q.val q.property.1 q.property.2 (2*(n : ℕ))) := by
  let L : ℂ := hillRealLabels q.val q.property.1 q.property.2 (2*(n : ℕ)-1)
  let U : ℂ := hillRealLabels q.val q.property.1 q.property.2 (2*(n : ℕ))
  have he : ({l,u} : Multiset ℂ)={L,U} := h.multiset_eq_original_labels q n hn r l u hcut hbound
  have hl : l=L ∨ l=U := by
    have hm : l∈({L,U} : Multiset ℂ) := he ▸ (by simp)
    simpa using hm
  rcases hl with rfl | rfl
  · have hu : u=U := by simpa using he
    rw [hu] at h
    exact h
  · have hu : u=L := by
      have he' := he.trans (Multiset.pair_comm L U)
      simpa using he'
    have hh := h.swap
    rw [hu] at hh
    exact hh

/-- The physical-label identification applies automatically at every
sufficiently high index for any fixed positive native radius. -/
theorem exists_hillHminus_original_label_matching_cutoff
    (q : RealPeriodOneHillPotential) (r : ℝ) (hr : 0<r) :
    ∃ N : ℕ, 2≤N ∧ ∀ n : ℕ+, N≤(n : ℕ) → ∀ l u : ℂ,
      HillHminusHighGapPair (hillOriginalHminusSource q.val) n r l u →
      ({l,u} : Multiset ℂ)=
        {(hillRealLabels q.val q.property.1 q.property.2 (2*(n : ℕ)-1) : ℂ),
          (hillRealLabels q.val q.property.1 q.property.2 (2*(n : ℕ)) : ℂ)} := by
  obtain ⟨N,hN⟩ := exists_nat_gt (max (8*‖q.val‖) (4*‖q.val‖/(Real.pi*r)))
  refine ⟨max 2 N,le_max_left _ _,?_⟩
  intro n hn l u h
  have hnn : (N : ℝ)≤(n : ℕ) := by exact_mod_cast (le_max_right 2 N).trans hn
  have hc : 8*‖q.val‖≤(n : ℕ) := (le_max_left _ _).trans (hN.le.trans hnn)
  have hd : 4*‖q.val‖/(Real.pi*r)≤(n : ℕ) := (le_max_right _ _).trans (hN.le.trans hnn)
  have hb : 4*‖q.val‖≤Real.pi*(n : ℕ)*r := by
    have hh := (div_le_iff₀ (mul_pos Real.pi_pos hr)).mp hd
    nlinarith
  exact h.multiset_eq_original_labels q n ((le_max_left _ _).trans hn) r l u hc hb

end NLS.KdV
