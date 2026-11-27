import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Tactic

/-! Exact enumeration of square-torus Rossby resonances at a prescribed output. -/
namespace Rossby

def sqNorm (z : GaussianInt) : ℤ := z.re ^ 2 + z.im ^ 2

def frequency (z : GaussianInt) : ℚ := (z.re : ℚ) / (sqNorm z : ℚ)

def Resonates (w z : GaussianInt) : Prop := frequency w = frequency z + frequency (w-z)

def circlePoint (w z : GaussianInt) : ℤ × ℤ :=
  let k := z * (w-z)
  (2 * w.re * k.re - w.re * sqNorm w, 2 * w.re * k.im - w.im * sqNorm w)

theorem norm_nonzero {z : GaussianInt} (h : z ≠ 0) : sqNorm z ≠ 0 := by
  contrapose! h
  change z.re ^ 2 + z.im ^ 2 = 0 at h
  apply Zsqrtd.ext <;> change _ = 0 <;> nlinarith [sq_nonneg z.re, sq_nonneg z.im]

theorem frequency_cross {w z : GaussianInt} (hw : w ≠ 0) (hz : z ≠ 0) (hy : w-z ≠ 0) :
    Resonates w z ↔
      w.re * sqNorm z * sqNorm (w-z) =
        sqNorm w * (z.re * sqNorm (w-z) + (w-z).re * sqNorm z) := by
  have hw' : (sqNorm w : ℚ) ≠ 0 := by exact_mod_cast norm_nonzero hw
  have hz' : (sqNorm z : ℚ) ≠ 0 := by exact_mod_cast norm_nonzero hz
  have hy' : (sqNorm (w-z) : ℚ) ≠ 0 := by exact_mod_cast norm_nonzero hy
  unfold Resonates frequency
  field_simp [hw', hz', hy']
  norm_cast
  constructor <;> intro h <;> simp only [Zsqrtd.sub_re] at * <;> linear_combination h

theorem circle_defect (w z : GaussianInt) :
    (circlePoint w z).1 ^ 2 + (circlePoint w z).2 ^ 2 - sqNorm w ^ 3 =
      4 * w.re * (w.re * sqNorm z * sqNorm (w-z) -
        sqNorm w * (z.re * sqNorm (w-z) + (w-z).re * sqNorm z)) := by
  simp only [circlePoint,sqNorm,Zsqrtd.mul_re,Zsqrtd.mul_im,Zsqrtd.sub_re,Zsqrtd.sub_im]
  ring

theorem resonates_iff_circle {w z : GaussianInt} (ha : w.re ≠ 0)
    (hz : z ≠ 0) (hy : w-z ≠ 0) :
    Resonates w z ↔ (circlePoint w z).1 ^ 2 + (circlePoint w z).2 ^ 2 = sqNorm w ^ 3 := by
  have hw : w ≠ 0 := fun h => ha (by simp [h])
  rw [frequency_cross hw hz hy, ← sub_eq_zero, ← sub_eq_zero (a :=
    (circlePoint w z).1 ^ 2 + (circlePoint w z).2 ^ 2), circle_defect]
  simp [ha]

/-- A Gaussian sum and product determine the unordered pair of summands. -/
theorem circle_fiber {w z v : GaussianInt} (ha : w.re ≠ 0) :
    circlePoint w z = circlePoint w v ↔ z = v ∨ z = w-v := by
  constructor
  · intro h
    have hr := congrArg Prod.fst h
    have hi := congrArg Prod.snd h
    simp only [circlePoint] at hr hi
    have he : z*(w-z) = v*(w-v) := by
      apply Zsqrtd.ext
      · exact mul_left_cancel₀ (mul_ne_zero (by norm_num : (2:ℤ)≠0) ha) (by linarith)
      · exact mul_left_cancel₀ (mul_ne_zero (by norm_num : (2:ℤ)≠0) ha) (by linarith)
    have : (z-v)*(z-(w-v))=0 := by linear_combination -he
    simpa [sub_eq_zero] using mul_eq_zero.mp this
  · rintro (rfl | rfl)
    · rfl
    · simp [circlePoint,mul_comm]

/-- Integer coordinates in a sum of two squares lie in a finite coordinate box. -/
def representations (m : ℤ) : Finset (ℤ × ℤ) :=
  ((Finset.Icc (-m) m) ×ˢ (Finset.Icc (-m) m)).filter fun p => p.1^2+p.2^2=m

theorem mem_representations (m : ℤ) (p : ℤ × ℤ) :
    p ∈ representations m ↔ p.1^2 + p.2^2 = m := by
  obtain ⟨x,y⟩ := p
  simp only [representations,Finset.mem_filter,Finset.mem_product,Finset.mem_Icc, and_iff_right_iff_imp]
  rintro rfl
  have ls (v : ℤ) : v ≤ v^2 := by
    by_cases hv : v ≤ 0
    · exact hv.trans (sq_nonneg _)
    · have hp : 0 ≤ v-1 := by omega
      nlinarith [mul_nonneg (show 0 ≤ v by omega) hp]
  have hx := ls x
  have hx' := ls (-x)
  have hy := ls y
  have hy' := ls (-y)
  constructor <;> constructor <;> nlinarith [sq_nonneg x,sq_nonneg y]

/-- Counts any finite collection of ordered first inputs, even without a box
bound. The finite circle contains all images and each fiber has at most two. -/
theorem card_le_twice_r₂ (w : GaussianInt) (ha : w.re ≠ 0) (s : Finset GaussianInt)
    (hs : ∀ z ∈ s, z ≠ 0 ∧ w-z ≠ 0 ∧ Resonates w z) :
    s.card ≤ 2 * (representations (sqNorm w ^ 3)).card := by
  classical
  let C := representations (sqNorm w ^ 3)
  have hm : ∀ z ∈ s, circlePoint w z ∈ C := by
    intro z hz
    obtain ⟨h₁,h₂,h₃⟩ := hs z hz
    exact (mem_representations _ _).2 ((resonates_iff_circle ha h₁ h₂).1 h₃)
  calc
    s.card = ∑ q ∈ C, (s.filter fun z => circlePoint w z = q).card :=
      Finset.card_eq_sum_card_fiberwise hm
    _ ≤ ∑ _q ∈ C, 2 := by
      apply Finset.sum_le_sum
      intro q _
      by_cases hp : (s.filter fun z => circlePoint w z = q).Nonempty
      · obtain ⟨v,hv⟩ := hp
        have sub : (s.filter fun z => circlePoint w z = q) ⊆ {v,w-v} := by
          intro z hz
          have := (circle_fiber ha).1 ((Finset.mem_filter.mp hz).2.trans (Finset.mem_filter.mp hv).2.symm)
          simpa using this
        exact (Finset.card_le_card sub).trans (Finset.card_le_two)
      · simp [Finset.not_nonempty_iff_eq_empty.mp hp]
    _ = _ := by simp [C,Nat.mul_comm]

/-- The quadratic and its discriminant describe the inverse without division. -/
theorem quadratic_recovery (w z k d : GaussianInt) (hd : 2*z = w+d) :
    z*(w-z) = k ↔ d^2 = w^2-4*k := by
  have he : d = 2*z-w := by linear_combination -hd
  rw [he]
  constructor
  · intro hk
    linear_combination -4*hk
  · intro hk
    apply mul_left_cancel₀ (show (4 : GaussianInt) ≠ 0 by norm_num)
    linear_combination -hk

/-- An unordered nonempty fiber is recovered from either one of its roots. -/
noncomputable def rootPair (w : GaussianInt) (q : ℤ × ℤ) : Finset GaussianInt := by
  classical
  exact if h : ∃ z, circlePoint w z = q then
    {Classical.choose h,w-Classical.choose h} else ∅

theorem mem_rootPair {w z : GaussianInt} (ha : w.re ≠ 0) (q : ℤ × ℤ) :
    z ∈ rootPair w q ↔ circlePoint w z = q := by
  classical
  unfold rootPair
  split
  next h =>
    constructor
    · intro hz
      exact ((circle_fiber ha).2 (by simpa using hz)).trans (Classical.choose_spec h)
    · intro hz
      simpa using (circle_fiber ha).1 (hz.trans (Classical.choose_spec h).symm)
  next h =>
    have hn : circlePoint w z ≠ q := fun hz => h ⟨z,hz⟩
    simp [hn]

noncomputable def allPartners (w : GaussianInt) : Finset GaussianInt := by
  classical
  exact ((representations (sqNorm w ^ 3)).biUnion (rootPair w)).filter fun z => z ≠ 0 ∧ w-z ≠ 0

theorem mem_allPartners {w z : GaussianInt} (ha : w.re ≠ 0) :
    z ∈ allPartners w ↔ z ≠ 0 ∧ w-z ≠ 0 ∧ Resonates w z := by
  classical
  simp only [allPartners,Finset.mem_filter,Finset.mem_biUnion,mem_rootPair ha]
  constructor
  · rintro ⟨⟨q,hq,hz⟩,h₁,h₂⟩
    exact ⟨h₁,h₂,(resonates_iff_circle ha h₁ h₂).2 ((mem_representations _ _).1 (hz ▸ hq))⟩
  · rintro ⟨h₁,h₂,hr⟩
    exact ⟨⟨_,(mem_representations _ _).2 ((resonates_iff_circle ha h₁ h₂).1 hr),rfl⟩,h₁,h₂⟩

theorem allPartners_card {w : GaussianInt} (ha : w.re ≠ 0) :
    (allPartners w).card ≤ 2 * (representations (sqNorm w ^ 3)).card :=
  card_le_twice_r₂ w ha _ fun _ hz => (mem_allPartners ha).1 hz

end Rossby
