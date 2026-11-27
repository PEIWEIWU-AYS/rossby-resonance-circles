import RossbyCircle
import Mathlib.Tactic
import Mathlib.Data.Real.Sqrt

namespace Rossby.Pell

/-- The positive Pell orbit is written in the order (n,t). -/
def orbit : ℕ → ℤ × ℤ
  | 0 => (1, 1)
  | i+1 => let (n,t) := orbit i
           (2*n+t, 3*n+2*t)

theorem orbit_spec (i : ℕ) : (i:ℤ)+1 ≤ (orbit i).1 ∧ 1 ≤ (orbit i).2 ∧
    (orbit i).2^2 = 3*(orbit i).1^2 - 2 ∧
    (orbit i).1 % 2 = 1 ∧ (orbit i).2 % 2 = 1 := by
  induction i with
  | zero => decide
  | succ i ih =>
    rcases h : orbit i with ⟨n,t⟩
    rw [h] at ih
    rcases ih with ⟨hn, ht, he, hno, hto⟩
    simp only [orbit, h, Nat.cast_succ, Prod.fst, Prod.snd] at *
    refine ⟨by omega, by omega, ?_, by omega, by omega⟩
    nlinarith [he]

def A (n t : ℤ) := 16*n^3*t
def B (n : ℤ) := 2*n
def X (n t : ℤ) := t*(2*n-1)*(4*n^2-2*n-1)
def Y (n : ℤ) := -(4*n^2-2*n-1)*(6*n^2+3*n-1)

/-- The two input modes and the output all have a positive zonal component. -/
theorem zonal (n t : ℤ) (hn : 1 ≤ n) (ht : 1 ≤ t) :
    0 < X n t ∧ X n t < A n t := by
  have h : 1 ≤ n^2 := by nlinarith [sq_nonneg (n-1)]
  have h₂ : 0 < 4*n^2-2*n-1 := by nlinarith [sq_nonneg (n-1)]
  have h₃ : 0 < (2*n-1) := by omega
  refine ⟨mul_pos (mul_pos (by omega) h₃) h₂, ?_⟩
  have hb : 0 < 8*n^3+8*n^2-1 := by nlinarith [show 0 ≤ n^3 by positivity]
  dsimp [X,A]
  nlinarith [mul_pos (show 0<t by omega) hb]

/-- Equality after multiplying the three nonzero frequency denominators. -/
theorem resonance_identity (n t : ℤ) (h : t^2 = 3*n^2-2) :
    A n t * (X n t ^2 + Y n ^2) *
        ((A n t-X n t)^2+(B n-Y n)^2) =
    X n t * (A n t^2+B n^2) * ((A n t-X n t)^2+(B n-Y n)^2) +
    (A n t-X n t) * (A n t^2+B n^2) * (X n t^2+Y n^2) := by
  unfold A B X Y
  linear_combination (-16*n^3*t*(2*n-1)*(2*n+1)*(4*n^2-2*n-1)*(4*n^2+2*n-1)*
    (1728*n^8 + 192*n^6*t^2 - 1728*n^6 + 64*n^4*t^2 + 432*n^4 -
      16*n^2*t^2 - 23*n^2 + t^2)) * h

/-- Bezout's identity detects primitivity even when the two components of the output
    mode share a large common divisor. -/
theorem primitive (n t d : ℤ) (ht : t%2=1)
    (hb : d ∣ B n) (hx : d ∣ X n t) (hy : d ∣ Y n) : d ∣ 1 := by
  have id : Y n + 1 = n*(-24*n^3+16*n+1) := by unfold Y; ring
  have hi : d ∣ 2*(Y n+1) := by
    rw [id]
    convert dvd_mul_of_dvd_left hb (-24*n^3+16*n+1) using 1
    unfold B
    ring
  have hyy : d ∣ 2*Y n := dvd_mul_of_dvd_right hy 2
  have htwo : d ∣ 2 := by
    convert dvd_sub hi hyy using 1
    ring
  have modx : X n t % 2 = 1 := by
    have hxid : X n t = t+2*(t*(4*n^3-4*n^2)) := by unfold X; ring
    omega
  have hrem := Int.emod_add_ediv (X n t) 2
  have hdq : d ∣ 2*(X n t / 2) := dvd_mul_of_dvd_left htwo _
  have hd := dvd_sub hx hdq
  convert hd using 1
  omega

theorem ratio_square (n t : ℤ) (hn : 1 ≤ n) (h : t^2 = 3*n^2-2) :
    ((A n t : ℝ)/(B n : ℝ)^4)^2 = 3 - 2/(n:ℝ)^2 := by
  have hn' : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have he : (t:ℝ)^2=3*(n:ℝ)^2-2 := by exact_mod_cast h
  simp only [A,B, Int.cast_mul,Int.cast_ofNat,Int.cast_pow]
  field_simp
  linear_combination (n:ℝ)^8 * 256 * he

/-- For every smaller coefficient and every meridional cutoff the family gives
    a larger ratio. The square identity gives its matching upper limit. -/
theorem arbitrarily_close (c : ℝ) (hc : c < Real.sqrt 3) (K : ℕ) :
    ∃ n t : ℤ, 1 ≤ n ∧ 1 ≤ t ∧ (K:ℤ) < B n ∧ t^2=3*n^2-2 ∧ t%2=1 ∧
      c < (A n t : ℝ)/(B n : ℝ)^4 := by
  let d := max 0 c
  have hs := Real.sq_sqrt (show (0:ℝ)≤3 by norm_num)
  have hd : d < Real.sqrt 3 := max_lt (Real.sqrt_pos.2 (by norm_num)) hc
  have hdn : 0 ≤ d := le_max_left _ _
  have hsum : 0 < Real.sqrt 3 + d := by linarith
  have gap : 0 < 3-d^2 := by nlinarith [mul_pos (sub_pos.mpr hd) hsum]
  obtain ⟨i,hi⟩ := exists_nat_gt (max (K:ℝ) (2/(3-d^2)))
  rcases h : orbit i with ⟨n,t⟩
  have spec := orbit_spec i
  rw [h] at spec
  rcases spec with ⟨hn,ht,he,_,ho⟩
  change (i:ℤ)+1 ≤ n at hn
  change 1 ≤ t at ht
  have hn1 : 1 ≤ n := by omega
  have hr : (i:ℝ)+1 ≤ n := by exact_mod_cast hn
  have hK : (K:ℝ) < i := lt_of_le_of_lt (le_max_left _ _) hi
  have hKi : K < i := by exact_mod_cast hK
  refine ⟨n,t,hn1,ht,by unfold B; omega,he,ho,?_⟩
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn1
  have H : 2/(3-d^2) < (n:ℝ)^2 := by
    have h0 := lt_of_le_of_lt (le_max_right _ _) hi
    nlinarith [sq_nonneg ((n:ℝ)-1)]
  have H' : (2:ℝ) < (n:ℝ)^2*(3-d^2) := (div_lt_iff₀ gap).mp H
  have ns : (0:ℝ)<(n:ℝ)^2 := by positivity
  have hh : 2/(n:ℝ)^2 < 3-d^2 := (div_lt_iff₀ ns).mpr (by linarith)
  have rr := ratio_square n t hn1 he
  have pos : (0:ℝ) ≤ (A n t:ℝ)/(B n:ℝ)^4 := by
    apply div_nonneg _ (by positivity)
    exact_mod_cast (show 0 ≤ A n t by unfold A; positivity)
  apply lt_of_le_of_lt (le_max_right 0 c)
  by_contra! hle
  nlinarith [mul_nonneg (sub_nonneg.mpr hle) (add_nonneg hdn pos)]

def output (n t : ℤ) : GaussianInt := ⟨A n t, B n⟩
def input (n t : ℤ) : GaussianInt := ⟨X n t, Y n⟩

theorem resonant_family (n t : ℤ) (hn : 1 ≤ n) (ht : 1 ≤ t) (h : t^2=3*n^2-2) :
    Rossby.Resonates (output n t) (input n t) := by
  obtain ⟨hx, hax⟩ := zonal n t hn ht
  have hw : output n t ≠ 0 := by
    intro e
    have h0 : A n t = 0 := congrArg Zsqrtd.re e
    omega
  have hz : input n t ≠ 0 := by
    intro e
    have h0 : X n t = 0 := congrArg Zsqrtd.re e
    omega
  have hwz : output n t - input n t ≠ 0 := by
    intro e
    have h0 : A n t-X n t = 0 := congrArg Zsqrtd.re e
    omega
  apply (Rossby.frequency_cross hw hz hwz).mpr
  change A n t * (X n t^2+Y n^2) * ((A n t-X n t)^2+(B n-Y n)^2) =
    (A n t^2+B n^2) * (X n t*((A n t-X n t)^2+(B n-Y n)^2) +
      (A n t-X n t)*(X n t^2+Y n^2))
  linear_combination resonance_identity n t h

/-- Primitive, nonzonal square-torus resonances approach the coefficient sqrt(3)
    above every meridional cutoff. -/
theorem primitive_sharpness (c : ℝ) (hc : c < Real.sqrt 3) (K : ℕ) :
    ∃ w z : GaussianInt, Rossby.Resonates w z ∧
      0 < z.re ∧ z.re < w.re ∧ (K:ℤ) < w.im ∧
      (∀ d : ℤ, d ∣ w.re → d ∣ w.im → d ∣ z.re → d ∣ z.im → d ∣ 1) ∧
      c < (w.re:ℝ)/(w.im:ℝ)^4 ∧ (w.re:ℝ)/(w.im:ℝ)^4 < Real.sqrt 3 := by
  obtain ⟨n,t,hn,ht,hb,he,ho,hc'⟩ := arbitrarily_close c hc K
  obtain ⟨hp,hp'⟩ := zonal n t hn ht
  refine ⟨output n t,input n t,resonant_family n t hn ht he,hp,hp',hb,
    (fun d _ hb hx hy => primitive n t d ho hb hx hy),hc',?_⟩
  change (A n t:ℝ)/(B n:ℝ)^4 < Real.sqrt 3
  have hs := Real.sq_sqrt (show (0:ℝ)≤3 by norm_num)
  have hn' : (0:ℝ)<n := by exact_mod_cast (by omega : 0<n)
  have hsmall : 0 < 2/(n:ℝ)^2 := by positivity
  have hr := ratio_square n t hn he
  by_contra! hle
  have hroot : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg _
  have hadd : 0 ≤ (A n t:ℝ)/(B n:ℝ)^4+Real.sqrt 3 := by linarith
  nlinarith [mul_nonneg (sub_nonneg.mpr hle) hadd]

end Rossby.Pell
