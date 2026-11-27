import Mathlib.Tactic

namespace Rossby

/-- Local prime-power comparison for τ(n) τ(n³) ≤ d₈(n). -/
theorem divisor_eight_local (e : ℕ) : (e+1)*(3*e+1) ≤ (e+7).choose 7 := by
  rw [← Nat.choose_symm_add (a := e) (b := 7)]
  induction e with
  | zero => decide
  | succ e ih =>
    have h := Nat.succ_mul_choose_eq (e+7) e
    have hi := Nat.mul_le_mul_left (e+8) ih
    apply Nat.le_of_mul_le_mul_right (c := e+1) _ (by omega)
    change (e+1+1)*(3*(e+1)+1)*(e+1) ≤ (e+1+7).choose (e+1)*(e+1)
    change (e+7+1)*(e+7).choose e = (e+7+1).choose (e+1)*(e+1) at h
    have eq : e+1+7 = e+7+1 := by omega
    rw [eq,← h]
    nlinarith

/-- Kopp's inverse parameters (s,t,s−2u) are quadratically bounded in a wave box. -/
theorem inverse_parameter_bound (a b x y N : ℤ)
    (ha : |a| ≤ N) (hb : |b| ≤ N) (hx : |x| ≤ N) (hy : |y| ≤ N)
    (hz : |a-x| ≤ N) (hk : |b-y| ≤ N) :
    |a^2+b^2| ≤ 2*N^2 ∧ |b*x-a*y| ≤ 2*N^2 ∧
    |a^2+b^2-2*(a*x+b*y)| ≤ 2*N^2 := by
  have hp (r v : ℤ) (hr : |r| ≤ N) (hv : |v| ≤ N) : |r*v| ≤ N^2 := by
    rw [abs_mul,pow_two]
    exact mul_le_mul hr hv (abs_nonneg _) ((abs_nonneg _).trans hr)
  have hq (r : ℤ) (hr : |r| ≤ N) : r^2 ≤ N^2 := by
    simpa [← sq,abs_of_nonneg (sq_nonneg r)] using hp r r hr hr
  have l1 := hq a ha
  have l2 := hq b hb
  have l3 := hq x hx
  have l4 := hq y hy
  have l5 := hq _ hz
  have l6 := hq _ hk
  constructor
  · rw [abs_of_nonneg (by positivity)]
    linarith
  constructor
  · exact (abs_sub _ _).trans (by linarith [hp b x hb hx,hp a y ha hy])
  · rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (a-x),sq_nonneg (b-y),sq_nonneg x,sq_nonneg y]

end Rossby
