import Mathlib.Data.Int.Basic
import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Tactic.GCongr
import Mathlib
--import other .lean file


@[ext]
structure eisensteinInt where
  re : ℤ
  im : ℤ

namespace eisensteinInt

instance : Zero eisensteinInt :=
  ⟨⟨0, 0⟩⟩

instance : One eisensteinInt :=
  ⟨⟨1, 0⟩⟩

instance : Add eisensteinInt :=
  ⟨fun x y ↦ ⟨x.re + y.re, x.im + y.im⟩⟩

instance : Neg eisensteinInt :=
  ⟨fun x ↦ ⟨-x.re, -x.im⟩⟩

instance : Mul eisensteinInt :=
  ⟨fun x y ↦ ⟨x.re * y.re - x.im * y.im, x.re * y.im + x.im * y.re + x.im * y.im⟩⟩

theorem zero_def : (0 : eisensteinInt) = ⟨0, 0⟩ :=
  rfl

theorem one_def : (1 : eisensteinInt) = ⟨1, 0⟩ :=
  rfl

theorem add_def (x y : eisensteinInt) : x + y = ⟨x.re + y.re, x.im + y.im⟩ :=
  rfl

theorem neg_def (x : eisensteinInt) : -x = ⟨-x.re, -x.im⟩ :=
  rfl

theorem mul_def (x y : eisensteinInt) :
    x * y = ⟨x.re * y.re - x.im * y.im, x.re * y.im + x.im * y.re + x.im * y.im⟩ :=
  rfl

@[simp]
theorem zero_re : (0 : eisensteinInt).re = 0 :=
  rfl

@[simp]
theorem zero_im : (0 : eisensteinInt).im = 0 :=
  rfl

@[simp]
theorem one_re : (1 : eisensteinInt).re = 1 :=
  rfl

@[simp]
theorem one_im : (1 : eisensteinInt).im = 0 :=
  rfl

@[simp]
theorem add_re (x y : eisensteinInt) : (x + y).re = x.re + y.re :=
  rfl

@[simp]
theorem add_im (x y : eisensteinInt) : (x + y).im = x.im + y.im :=
  rfl

@[simp]
theorem neg_re (x : eisensteinInt) : (-x).re = -x.re :=
  rfl

@[simp]
theorem neg_im (x : eisensteinInt) : (-x).im = -x.im :=
  rfl

@[simp]
theorem mul_re (x y : eisensteinInt) : (x * y).re = x.re * y.re - x.im * y.im :=
  rfl

@[simp]
theorem mul_im (x y : eisensteinInt) : (x * y).im = x.re * y.im + x.im * y.re + x.im * y.im :=
  rfl

instance instCommRing : CommRing eisensteinInt where
  zero := 0
  one := 1
  add := (· + ·)
  neg x := -x
  mul := (· * ·)
  add_assoc := by
    intros
    ext <;> simp <;> ring
  zero_add := by
    intro
    ext <;> simp
  add_zero := by
    intro
    ext <;> simp
  add_left_neg := by
    intro
    ext <;> simp
  add_comm := by
    intros
    ext <;> simp <;> ring
  mul_assoc := by
    intros
    ext <;> simp <;> ring
  one_mul := by
    intro
    ext <;> simp
  mul_one := by
    intro
    ext <;> simp
  left_distrib := by
    intros
    ext <;> simp <;> ring
  right_distrib := by
    intros
    ext <;> simp <;> ring
  mul_comm := by
    intros
    ext <;> simp <;> ring
  zero_mul := by
    intro
    ext <;> simp
  mul_zero := by
    intro
    ext <;> simp

@[simp]
theorem sub_re (x y : eisensteinInt) : (x - y).re = x.re - y.re :=
  rfl

@[simp]
theorem sub_im (x y : eisensteinInt) : (x - y).im = x.im - y.im :=
  rfl

instance : Nontrivial eisensteinInt := by
  use 0, 1
  rw [Ne, eisensteinInt.ext_iff]
  simp

end eisensteinInt
-----need to change
namespace Int

def div' (a b : ℤ) :=
  (a + b / 2) / b

def mod' (a b : ℤ) :=
  (a + b / 2) % b - b / 2

theorem div'_add_mod' (a b : ℤ) : b * div' a b + mod' a b = a := by
  rw [div', mod']
  linarith [Int.ediv_add_emod (a + b / 2) b]

theorem abs_mod'_le (a b : ℤ) (h : 0 < b) : |mod' a b| ≤ b / 2 := by
  rw [mod', abs_le]
  constructor
  · linarith [Int.emod_nonneg (a + b / 2) h.ne']
  have := Int.emod_lt_of_pos (a + b / 2) h
  have := Int.ediv_add_emod b 2
  have := Int.emod_lt_of_pos b zero_lt_two
  revert this; intro this -- FIXME, this should not be needed
  linarith

theorem mod'_eq (a b : ℤ) : mod' a b = a - b * div' a b := by linarith [div'_add_mod' a b]

end Int

private theorem aux {α : Type*} [LinearOrderedRing α] {x y : α} (h : x ^ 2 + y ^ 2 = 0) : x = 0 :=
  haveI h' : x ^ 2 = 0 := by
    apply le_antisymm _ (sq_nonneg x)
    rw [← h]
    apply le_add_of_nonneg_right (sq_nonneg y)
  pow_eq_zero h'

theorem sq_add_sq_eq_zero {α : Type*} [LinearOrderedRing α] (x y : α) :
    x ^ 2 + y ^ 2 = 0 ↔ x = 0 ∧ y = 0 := by
  constructor
  · intro h
    constructor
    · exact aux h
    rw [add_comm] at h
    exact aux h
  rintro ⟨rfl, rfl⟩
  norm_num

namespace eisensteinInt

def norm (x : eisensteinInt) :=
  x.re ^ 2 + x.im ^ 2 + x.re * x.im

lemma nonneg_divide_by_two {a : ℤ} (h : 0 ≤ 2 *a) : 0 ≤ a := by
  by_contra h'
  have _ : 2 * a < 0 := by linarith
  linarith

@[simp]
theorem norm_nonneg (x : eisensteinInt) : 0 ≤ norm x := by
  have h : 2 * norm x = (x.re+x.im)^2 + x.re^2 + x.im^2 := by
    simp [norm]
    ring
  apply nonneg_divide_by_two
  rw [h]
  apply add_nonneg
  apply add_nonneg
  apply sq_nonneg
  apply sq_nonneg
  apply sq_nonneg
  --apply add_nonneg <;>
  --apply sq_nonneg

theorem norm_eq_zero (x : eisensteinInt) : norm x = 0 ↔ x = 0 := by
have g : norm x = 0 ↔ 2 * norm x = 0 := by simp
have h : 2 * norm x = (x.re+x.im)^2 + x.re^2 + x.im^2 := by
  simp [norm]
  ring
rw [g, h]
constructor
have h1 : (x.re + x.im)^2 ≥ 0 := by apply sq_nonneg
have h2 : x.re^2 ≥ 0 := by apply sq_nonneg
have h3 : x.im^2 ≥ 0 := by apply sq_nonneg
have h4 : x.re^2 + x.im^2 ≥ 0 := by apply add_nonneg h2 h3
intro h5
rw [add_assoc] at h5
have h6 : _ :=  (add_eq_zero_iff' h2 h3).mp ((add_eq_zero_iff' h1 h4).mp h5).2
have h7 : x.re^2 = 0 := by tauto
have h8 : x.im^2 = 0 := by tauto
have h9 : x.re = 0 := by
  apply sq_eq_zero_iff.mp h7
have h10 : x.im = 0 := by
  apply sq_eq_zero_iff.mp h8
apply eisensteinInt.ext
simp [h9, h10]
simp [h10]
rintro h11
have h12 : x.re = 0 := by simp [h11]
have h13 : x.im = 0 := by simp [h11]
simp [h12, h13]
  --rw [norm, sq_add_sq_eq_zero, eisensteinInt.ext_iff]
  --rfl

theorem norm_pos (x : eisensteinInt) : 0 < norm x ↔ x ≠ 0 := by
  rw [lt_iff_le_and_ne, ne_comm, Ne, norm_eq_zero]
  simp [norm_nonneg]

theorem norm_mul (x y : eisensteinInt) : norm (x * y) = norm x * norm y := by
  simp [norm]
  ring

def conj (x : eisensteinInt) : eisensteinInt :=
  ⟨x.re + x.im, -x.im⟩

@[simp]
theorem conj_re (x : eisensteinInt) : (conj x).re = x.re + x.im :=
  rfl

@[simp]
theorem conj_im (x : eisensteinInt) : (conj x).im = -x.im :=
  rfl

theorem norm_conj (x : eisensteinInt) : norm (conj x) = norm x := by
  simp [norm]
  ring

instance : Div eisensteinInt :=
  ⟨fun x y ↦ ⟨Int.div' (x * conj y).re (norm y), Int.div' (x * conj y).im (norm y)⟩⟩

instance : Mod eisensteinInt :=
  ⟨fun x y ↦ x - y * (x / y)⟩


---def x / y to be ⟨(x.re * y.re + x.im * y.im + x.re * y.im) / (y.re^2 + y.im^2 + y.re * y.im)的最近整数, (x.im * y.re -x.re * y.im) / (y.re^2 + y.im^2 + y.re * y.im)的最近整数⟩

theorem div_def (x y : eisensteinInt) :
    x / y = ⟨Int.div' (x * conj y).re (norm y), Int.div' (x * conj y).im (norm y)⟩ :=
  rfl

theorem mod_def (x y : eisensteinInt) : x % y = x - y * (x / y) :=
  rfl

theorem norm_mod_lt (x : eisensteinInt) {y : eisensteinInt} (hy : y ≠ 0) :
    (x % y).norm < y.norm := by
  have norm_y_pos : 0 < norm y := by rwa [norm_pos]
  have H1 : x % y * conj y = ⟨Int.mod' (x * conj y).re (norm y), Int.mod' (x * conj y).im (norm y)⟩
  · ext <;> simp [Int.mod'_eq, mod_def, div_def, norm] <;> ring
  have H2 : 4 * norm (x % y) * norm y ≤ 3 * norm y * norm y
  · calc
      4 * (norm (x % y) * norm y) = 4 * norm (x % y * conj y) := by simp only [norm_mul, norm_conj]
      _ = 4 * |Int.mod' (x.re * y.re + x.im * y.im + x.re * y.im) (norm y)| ^ 2
          + 4 * |Int.mod' (-(x.re * y.im) + x.im * y.re) (norm y)| ^ 2
          + 4 * (Int.mod' (x.re * y.re + x.im * y.im + x.re * y.im) (norm y)) * (Int.mod' (-(x.re * y.im) + x.im * y.re) (norm y)):= by
          simp [H1, norm, sq_abs]
          ring_nf
      _ ≤ 4 * ((y.norm / 2) ^ 2) + 4 * ((y.norm / 2) ^ 2) + 4 * ((y.norm / 2) ^ 2):= by
        gcongr ?_ + ?_ + ?_
        gcongr <;> apply Int.abs_mod'_le _ _ norm_y_pos
        sorry
      _ ≤ 3 * norm y * norm y := by
          have h'' : (norm y / 2) * 4 ≤ norm y  := by
            simp only [norm, div_def, norm_mul, norm_conj]
            ring_nf
            apply Int.ediv_mul_le
            sorry
      -----apply Int.ediv_lt_of_lt_mul
      ----simp [div_def, norm]; ring ;
  calc norm (x % y) < norm y := by
        apply Int.ediv_lt_of_lt_mul
        · norm_num
        · linarith

theorem coe_natAbs_norm (x : eisensteinInt) : (x.norm.natAbs : ℤ) = x.norm :=
  Int.natAbs_of_nonneg (norm_nonneg _)

theorem natAbs_norm_mod_lt (x y : eisensteinInt) (hy : y ≠ 0) :
    (x % y).norm.natAbs < y.norm.natAbs := by
  apply Int.ofNat_lt.1
  simp only [Int.coe_natAbs, abs_of_nonneg, norm_nonneg]
  apply norm_mod_lt x hy

theorem not_norm_mul_left_lt_norm (x : eisensteinInt) {y : eisensteinInt} (hy : y ≠ 0) :
    ¬(norm (x * y)).natAbs < (norm x).natAbs := by
  apply not_lt_of_ge
  rw [norm_mul, Int.natAbs_mul]
  apply le_mul_of_one_le_right (Nat.zero_le _)
  apply Int.ofNat_le.1
  rw [coe_natAbs_norm]
  exact Int.add_one_le_of_lt ((norm_pos _).mpr hy)

instance : EuclideanDomain eisensteinInt :=
  { eisensteinInt.instCommRing with
    quotient := (· / ·)
    remainder := (· % ·)
    quotient_mul_add_remainder_eq :=
      fun x y ↦ by simp only; rw [mod_def, add_comm, sub_add_cancel]
    quotient_zero := fun x ↦ by
      simp [div_def, norm, Int.div']
      rfl
    r := (measure (Int.natAbs ∘ norm)).1
    r_wellFounded := (measure (Int.natAbs ∘ norm)).2
    remainder_lt := natAbs_norm_mod_lt
    mul_left_not_lt := not_norm_mul_left_lt_norm }

instance : IsPrincipalIdealRing eisensteinInt := inferInstance

end eisensteinInt
open Polynomial
open BigOperators
noncomputable section
def fq:ℚ[X]:=(X^2+C 3)


structure K_eq_eisenstein (K : Type u_7) (eisensteinInt : Type u_8) [Mul K] [Mul eisensteinInt] [Add K] [Add eisensteinInt] extends Equiv :
  Type (max u_7 u_8)
toFun : K → eisensteinInt :=
  fun (x : K) =>
  have ⟨ α , β , h⟩  :=K_basis_sum X
  ⟨⟨α - β , 2 * β ⟩⟩
invFun : eisensteinInt → K :=
  fun (x : eisensteinInt) => (x.re : Q) + (x.im : Q) / 2 + ( (x.im : Q) / 2 ) * AdjointRoot.root fq
left_inv : Function.LeftInverse self.invFun self.toFun
right_inv : Function.RightInverse self.invFun self.toFun
map_mul' : ∀ (x y : K), Equiv.toFun self.toEquiv (x * y) = Equiv.toFun self.toEquiv x * Equiv.toFun self.toEquiv y := by
  intros
  ext <;> simp <;> ring
map_add' : ∀ (x y : K), Equiv.toFun self.toEquiv (x + y) = Equiv.toFun self.toEquiv x + Equiv.toFun self.toEquiv y := by
  intros
  ext <;> simp <;> ring

instance : IsPrincipalIdealRing K := inferInstance ---OK?
