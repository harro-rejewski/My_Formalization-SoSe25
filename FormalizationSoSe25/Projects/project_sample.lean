-- Here is a first `import Mathlib.Tactic` to get things started.
-- Based on the definitions you need, you can add more imports right below.
/- `source`:
Buckley, S. M., & MacHale, D. (2013).
Variations on a theme: rings satisfying x 3= x are commutative.
The American Mathematical Monthly, 120(5), 430-440.
-/

import Mathlib.Tactic
import Mathlib.Algebra.Ring.Basic

lemma pow_2_ring_thing {R : Type*} [Ring R] (a : R) (h : ∀ a : R, a ^ 2 = a) : a + a = 0 := by
  have h1 : a + a = a + a + (a + a) := by{ calc
   a + a = (a + a) ^ 2 := by rw [h]
    _ = (a + a) * (a + a) := by rw [pow_two]
    _ = (a + a) * a + (a + a)*a  := by rw [mul_add]
    _ = a * a + a * a + a * a + a * a := by rw [add_mul, ←add_assoc]
    _ = a ^ 2 + a ^ 2 + a ^ 2 + a ^ 2 := by rw [← pow_two]
    _ = a + a + a + a := by rw [h]
    _ = (a + a) + (a + a) := by rw [add_assoc]
  }
  rw[left_eq_add] at h1
  exact h1

#check pow_2_ring_thing

theorem pow_2_ring_commutativ {R : Type*} [Ring R] (h : ∀ x : R, x ^ 2 = x) : ∀ x y : R, x * y = y * x := by
  intros x y
  have h1 : x + y = (x + y) ^ 2 := by rw [h]
  have h2 : (x + y) ^ 2 = x ^ 2 + y * x + x * y + y^2 := by{
    calc
      (x + y) ^ 2 = (x + y) * (x + y):= by rw [pow_two]
      _ = (x + y) * x + (x + y)*y  := by rw [mul_add]
      _ = x * x + y * x + x * y + y * y  := by rw [add_mul, add_mul, ←add_assoc]
      _ = x ^ 2 + y * x + x * y + y^2 := by rw [← pow_two,← pow_two]
  }
  have h3 : x + y = x + y * x + x * y + y:= by {
    calc
      x + y = (x + y) ^ 2 := h1
      (x + y) ^ 2 = x ^ 2 + y * x + x * y + y^2 := h2
      _ = x + y * x + x * y + y := by rw[h,h]
  }
  have h4: y * x + x * y = 0 := by {
    calc
      y * x + x * y = x - x + y - y + y * x + x * y := by simp
      _ = x + y * x + x * y + y - y - x := by{
        simp
        rw [add_assoc, add_comm]
        rw [add_comm  x (x*y+y*x)]
        simp
      }
      _ = x + y - y - x := by rw[←h3]
      _ = x - x := by simp
      _ = 0 := by simp
  }
  have h5 : y * x + y * x = 0 := pow_2_ring_thing (y * x) h
  rw [← h5] at h4
  simp at h4
  exact h4


-- Eigentlicher Beweis den ich zeigen will: 
lemma pow_3_ring_thing {R : Type*} [Ring R] (h : ∀ x : R, x ^ 3 = x) : ∀ x : R, x^2 = 0 → x = 0:= by
  intro x i
  have h1 : x^3 = 0 := by {
    calc
      x^3 = x * x * x := by rw [pow_three,mul_assoc]
      _ = x^2 * x := by rw [pow_two]
      _ = 0 * x := by rw [i]
      _ = 0 := by simp
  }
  rw [h] at h1
  exact h1

#check pow_mul
#check pow_succ

lemma pow_3_ring_pow2_is_idemp {R : Type*} [Ring R] (h : ∀ x : R, x ^ 3 = x) : ∀ x : R, IsIdempotentElem (x^2) := by
  intro x
  unfold IsIdempotentElem
  rw [← pow_two,←pow_mul,pow_succ]
  rw [h]
  rw [pow_two]


-- warum hab ich erst jetzt gelesen dass es noncomm ring tactic gibt? ahhhhhhh
-- (e * y - e * y * e)^2 = (y * e - e * y * e)^2
-- lemma 6
lemma ring_idemp_property_1 {R : Type*} [Ring R] (e y : R) (h: IsIdempotentElem e) : (e * y - e * y * e)^2 = 0 := by
  unfold IsIdempotentElem at h -- dann seh ichs nochmal schön
  have h_help : (y * (e * e) * y) =  (y * e * y) := by rw[h]
  have h1 : (e * y - e * y * e)^2 = 0 := by {
    calc
      (e * y - e * y * e)^2 = (e * y + - e * y * e)^2 := by noncomm_ring
      _ = (e * y)^2 + (e * y) * (- e * y * e) + (- e * y * e) * (e * y) + (e * y * e)^2  := by noncomm_ring
      _ = (e * y)^2 - ((e * y) * (e * y * e)) - (( e * y * e) * (e * y)) + (e * y * e)^2  := by noncomm_ring
      _ = (e * y)^2 - (e * (y * e * y) * e) - (e * y * (e * e) * y) + (e * y * e)^2 := by noncomm_ring
      _ = (e * y)^2 - (e * (y * e * y) * e) - (e * y * e * y) + (e * y * e)^2 := by rw[h]
      _ = (e * y)^2 - (e * (y * (e * e) * y) * e) - (e * y * e * y) + (e * y * e)^2 := by rw[h_help]
      _ = 0 := by noncomm_ring
  }
  exact h1

lemma ring_idemp_property_2 {R : Type*} [Ring R] (e y : R) (h: IsIdempotentElem e) : (y * e - e * y * e)^2 = 0 := by
  have h_help : (y * (e * e) * y) =  (y * e * y) := by rw[h]
  have h1 : (y * e - e * y * e)^2 = 0 := by {
    calc
      (y * e - e * y * e)^2 = (y * e + - e * y * e)^2 := by noncomm_ring
      _ = (y * e)^2 + (y * e) * (- e * y * e) + (- e * y * e) * (y * e) + (e * y * e)^2  := by noncomm_ring
      _ = (y * e)^2 - ((y * e) * (e * y * e)) - (( e * y * e) * (y * e)) + (e * y * e)^2  := by noncomm_ring
      _ = (y * e)^2 - (y * (e * e) * y * e) - (e * (y * e * y) * e) + (e * y * e)^2 := by noncomm_ring
      _ = (y * e)^2 - (y * e * y * e) - (e * (y * e * y) * e) + (e * y * e)^2 := by rw[h]
      _ = (y * e)^2 - (y * e * y * e) - (e * (y * (e * e) * y) * e) + (e * y * e)^2 := by rw[h_help]
      _ = 0 := by noncomm_ring
  }
  exact h1

lemma ring_idemp_center_property {R : Type*} [Ring R] (e : R) (g: ∀ x : R, x^2 = 0 → x = 0) (h: e * e = e) : ∀ y : R, y * e = e * y := by
  intro y
  have h1 : (y * e - e * y * e)^2 = 0 := ring_idemp_property_2 e y h
  apply g at h1
  have h2 : (e * y - e * y * e)^2 = 0 := ring_idemp_property_1 e y h
  apply g at h2
  rw [← h2] at h1
  simp at h1
  exact h1

lemma pow3_ring_idemp_center_property {R : Type*} [Ring R] (x : R) (h: ∀ x : R, x^3 = x) : ∀ y : R, y * x^2 = x^2 * y := by
  intro y
  have h1 := pow_3_ring_pow2_is_idemp h
  have h1_app := h1 x
  have h2 := pow_3_ring_thing h
  have h2_app := h2 x
  have h3 := ring_idemp_center_property (x^2) h2 h1_app
  exact h3 y

theorem pow3_ring_is_commutative {R : Type*} [Ring R] (h : ∀ x : R, x ^ 3 = x) : ∀ x y : R, x * y = y * x := by
  intro x y
  have h1 := pow3_ring_idemp_center_property (y * x) h x
  have h2 := pow3_ring_idemp_center_property x h y
  have h3 := pow3_ring_idemp_center_property y h x
  calc
    x * y = (x * y)^3 := by rw [h]
    _ = x * y * ((x * y) * (x * y)) := by rw [pow_three]
    _ = x * y * x * y * x * y := by noncomm_ring
    _ = x * (y * x)^2 * y := by noncomm_ring
    _ = (y * x)^2 * x * y := by rw[h1]
    _ = (y * x) * (y * x) * x * y := by noncomm_ring
    _ = (y * x) * (y * x^2) * y := by noncomm_ring
    _ = (y * x) * (x^2 * y) * y := by rw[h2]
    _ = y * x^3 * y * y := by noncomm_ring
    _ = y * x * y * y := by rw [h]
    _ = y * (x * y^2) := by noncomm_ring
    _ = y * (y^2 * x) := by rw[h3]
    _ = y^3 * x :=  by noncomm_ring
    _ = y * x := by rw [h]


-- Theoretically, you could just write `import Mathlib`, but this will be somewhat slower.
/- Remember we can open namespaces to shorten names and enable notation.




For example (feel free to change it): -/

/- Remember if many new definitions require a `noncomputable` either in the `section` or definition.

For example (feel free to change it): -/

/- You can now start writing definitions and theorems. -/
