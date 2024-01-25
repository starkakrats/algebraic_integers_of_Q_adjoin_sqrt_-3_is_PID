import Mathlib.Data.Real.Basic
import MIL.Common
import Mathlib.Data.Nat.Prime
import Mathlib.Algebra.Divisibility.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Data.Polynomial.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Data.Polynomial.Basic
import Mathlib.RingTheory.IsAdjoinRoot
import Mathlib.FieldTheory.Minpoly.Basic
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.Data.Polynomial.Basic
import Mathlib.Data.Polynomial.Div
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.IsAdjoinRoot
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Polynomial.Degree.Definitions
import Mathlib.Data.Int.Basic
import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Tactic.GCongr

section

open Polynomial
noncomputable section

----
def fz : ℤ[X] := X^2 + C 3
def fq : ℚ[X] := X^2 + C 3

def S := ({(3 : Int)} : Set Int)
def I := Ideal.span S

lemma deg_fz : natDegree fz = 2 := by
  unfold fz
  compute_degree
  norm_num

lemma deg_fq : natDegree fq = 2 := by
  unfold fq
  compute_degree
  norm_num

lemma non_zero_fq : fq ≠ 0 := by
  intro con
  have con_deg : natDegree 0 = 2 := by rw [<-con, deg_fq]
  rw [natDegree_zero] at con_deg
  contradiction

lemma I3_prime : Ideal.IsPrime I := by
  apply Ideal.isPrime_iff.mpr
  constructor
  · apply Ideal.span_singleton_ne_top
    intro h
    apply Int.isUnit_iff.mp at h
    rcases h with h | h <;> revert h <;> norm_num
  · intro x y hxy
    apply Ideal.mem_span_singleton'.mp at hxy
    rcases hxy with ⟨a,ha⟩
    have : Int.natAbs (a * 3) = Int.natAbs (x * y) := by congr
    simp [Int.natAbs_mul] at this
    rw[(by simp [Int.natAbs] : Int.natAbs 3 = 3)] at this
    have h : 3 ∣ Int.natAbs x * Int.natAbs y := by
      rw [←this]
      norm_num
    obtain h := (Nat.Prime.dvd_mul Nat.prime_three).mp h
    rw [I, S]
    rcases h with (h1 | h2)
    · left
      apply Ideal.mem_span_singleton'.mpr
      rw [←(by simp [Int.natAbs] : Int.natAbs 3 = 3)] at h1
      obtain h1 := Int.natAbs_dvd_natAbs.mp h1
      dsimp [Dvd.dvd] at h
      rcases h1 with ⟨a, ha⟩
      use a
      rw [mul_comm, ha]
    · right
      apply Ideal.mem_span_singleton'.mpr
      rw [←(by simp [Int.natAbs] : Int.natAbs 3 = 3)] at h2
      obtain h1 := Int.natAbs_dvd_natAbs.mp h2
      dsimp [Dvd.dvd] at h2
      rcases h1 with ⟨a, ha⟩
      use a
      rw [mul_comm, ha]

def fz_ess : IsEisensteinAt fz I where
  leading := by
    simp only [Polynomial.leadingCoeff,deg_fz]
    simp [fz]
    intro h
    apply Ideal.mem_span_singleton'.mp at h
    rcases h with ⟨a, ha⟩
    apply Int.mul_eq_one_iff_eq_one_or_neg_one.mp at ha
    rcases ha with (ha1 | ha2)
    · linarith
    · linarith

  mem := by
    intro n hn
    rw[deg_fz] at hn
    apply Nat.le_of_lt_succ at hn
    rcases Nat.of_le_succ hn with (h1 | h2)
    · simp at h1
      rw [h1]
      simp [fz]
      rw [I,S]
      apply Ideal.mem_span_singleton'.mpr
      use 1
      ring
    · rw [h2]
      simp [fz]

  not_mem := by
    simp [fz,pow_two,I]
    intro h
    rw [Ideal.span_mul_span] at h
    rw [S] at h
    simp [Set.mem_iUnion] at h
    apply Ideal.mem_span_singleton'.mp at h
    rcases h with ⟨a, ha⟩
    norm_num at ha
    have : ( a * 9 ).natAbs = 3 := by
      congr
      rw [ha]
      simp [Int.natAbs]
    simp [Int.natAbs_mul] at this
    rw [(by simp [Int.natAbs] : Int.natAbs 9 = 9)] at this
    have h : 9 ∣ Int.natAbs a * 9 := by apply Nat.dvd_mul_left
    rw [this] at h
    apply Nat.le_of_dvd at h <;> linarith

lemma fz_monic : Polynomial.Monic fz := by
  simp only [Monic,Polynomial.leadingCoeff]
  rw [deg_fz]
  have h1 : Polynomial.coeff fz 2 = 1 := by
    simp [fz]
  rw [h1]

lemma fq_monic :Polynomial.Monic fq := by
  simp only [Monic,Polynomial.leadingCoeff]
  rw [deg_fq]
  have h1 : Polynomial.coeff fq 2 = 1 := by
    simp [fq]
  rw [h1]

lemma fz_Irr: Irreducible fz := by
  apply IsEisensteinAt.irreducible
  pick_goal 5
  · apply I
  pick_goal 2
  · apply I3_prime
  pick_goal 3
  · have : natDegree fz = 2 := by
      unfold fz
      compute_degree
      norm_num
    rw [this]
    linarith
  · apply fz_ess
  · apply Polynomial.Monic.isPrimitive
    apply fz_monic


instance : Fact (Irreducible fz) := ⟨fz_Irr⟩

lemma fq_Irr : Irreducible fq := by
  have hzq : fq = map (algebraMap ℤ ℚ) fz := by
    ext n
    · by_cases hd: n ≤ 2
      · rcases Nat.of_le_succ hd with (h1 | h2)
        · rcases Nat.of_le_succ h1 with (h11 | h12)
          · simp at *
            rw [h11]
            simp [fq,fz]
            rw [←Rat.coe_int_num 3]
            congr
          · rw [h12]
            simp [fq,fz]
        · rw [h2]
          simp [fq, fz]
      · push_neg at hd
        simp [fz, fq]
    · by_cases hd: n ≤ 2
      · rcases Nat.of_le_succ hd with (h1 | h2)
        · rcases Nat.of_le_succ h1 with (h11 | h12)
          · simp at *
            rw [h11]
            simp [fq, fz]
            norm_num
            show 1 = 1
            rfl
          · rw [h12]
            simp [fq, fz]
        · rw [h2]
          simp [fq, fz]
      · push_neg at hd
        simp [fz, fq]
  rw [hzq]
  apply (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map fz_monic).mp
  apply fz_Irr

@[reducible]
def K := @AdjoinRoot _ _ fq

#check K


example : natDegree fz = 2 := by
  unfold fz
  compute_degree
  norm_num

example : (Polynomial.coeff fz 0) = 3 := by
  simp [fz]

#check K

theorem K_ringOfIntegers [hf : Fact (Irreducible fq)] (x : K) :
  x ∈ NumberField.ringOfIntegers K ↔ IsIntegral ℤ x := by
  apply NumberField.mem_ringOfIntegers

lemma InZ_of_monic_dvdMinpoly  (f : ℤ[X]) (hf : Polynomial.Monic f) (g : ℚ[X]) (hg : Polynomial.Monic g) (h : g ∣ fq ) : ∃ g₁ : ℤ[X], g = map (algebraMap ℤ ℚ) g₁ := by sorry

theorem Integral_iff_minpolyInZ [hf : Fact (Irreducible fq)] (x : K)  : IsIntegral ℤ x ↔ (∀ n : ℕ, ∃ m : ℤ, (Polynomial.coeff (minpoly ℚ x) n) = m) := by sorry
--- ↔ 2 * x ∈ Z [x]
theorem MinpolyOfmem :∀ a b: ℚ, (minpoly ℚ (AdjoinRoot.mk fq ((C a : ℚ[X]) + (C b * (X : ℚ[X]))))) = (X ^ 2 - monomial 1 (2 * a) + C (a ^ 2 + 3 * b ^ 2) : ℚ[X]) := by sorry

theorem main_thm_ringOfIntegers [hf : Fact (Irreducible fq)] (x : K) :
x ∈ NumberField.ringOfIntegers K ↔ ∃ (a b :ℤ ), AdjoinRoot.mk fq (monomial 1 (b / 2 : ℚ) + C (a + b / 2 : ℚ)) = x := by sorry



----------



-- 由a+b√-3为（代数）整数可推出以下关系式
def a_b_int (a b : ℚ) := ∃ n₁ n₂ : ℤ, (2 * a = n₁) ∧ (a ^ 2 + 3 * b ^ 2 = n₂)

lemma FormOfmem (x : K) : ∃ a b : ℚ, (AdjoinRoot.mk fq) ((monomial 1) b + C a) = x ∧ (a_b_int a b) := by
  set K_powbasis := AdjoinRoot.powerBasis non_zero_fq with eq₁
  have K_dim : K_powbasis.dim = 2 := by rw [eq₁, AdjoinRoot.powerBasis_dim non_zero_fq, deg_fq]
  set K_basis := K_powbasis.basis with eq₂
  have type_same : Basis (Fin K_powbasis.dim) ℚ (AdjoinRoot fq) = Basis (Fin 2) ℚ (AdjoinRoot fq) := by rw [K_dim]
  rw [K_dim] at K_basis
  rw [<-Basis.sum_equivFun K_basis x]
  use K_basis.repr x 0, K_basis.repr x 1
  constructor
  · simp [Finset.univ, Fintype.elems, List.map]
    have zero_base : (⇑K_basis 0) = 1 := by sorry
    have one_base : ⇑K_basis 1 = AdjoinRoot.root fq := by sorry
    rw [zero_base, one_base]
    have mul_x : ∀ (β : ℚ), ((monomial 1) β) = ((monomial 0) β) * Polynomial.X := by
      intro t
      calc
        (monomial 1) t = (monomial (0 + 1) t) := by norm_num
        (monomial (0 + 1) t) = ((monomial 0) t) * Polynomial.X := by rw [<-Polynomial.monomial_mul_X 0]
    rw [mul_x (K_basis.repr x 1)]
    simp
    have K_mul_one₀ : ((K_basis.repr x) 0) = ((K_basis.repr x) 0) • 1 := by simp
    have K_mul_one₁ : ((K_basis.repr x) 1) = ((K_basis.repr x) 1) • 1 := by simp
    rw [K_mul_one₀, K_mul_one₁]
    rw [<-AdjoinRoot.smul_of, <-AdjoinRoot.smul_of]
    simp
    rw [add_comm]
  · sorry

lemma K_basis_sum (m : K) : ∃ α β : ℚ, m = α + β * (AdjoinRoot.root fq) := by
  have ⟨a, b, hab⟩ := FormOfmem m
  use a, b
  rw [<-hab.1]
  simp
  have mul_x : ∀ (β : ℚ), ((monomial 1) β) = ((monomial 0) β) * Polynomial.X := by
    intro t
    calc
      (monomial 1) t = (monomial (0 + 1) t) := by norm_num
      (monomial (0 + 1) t) = ((monomial 0) t) * Polynomial.X := by rw [<-Polynomial.monomial_mul_X 0]
  rw [mul_x b]
  simp
  rw [add_comm]

lemma mem_K_minpoly (x : K) : ∃ a b : ℚ, minpoly ℚ x = (monomial 2 1 - monomial 1 (2 * a) + C (a ^ 2 + 3 * b ^ 2)) := by
  have ⟨a, b, hab⟩ := K_basis_sum x
  set fx : Polynomial ℚ := (monomial 2 1 - monomial 1 (2 * a) + C (a ^ 2 + 3 * b ^ 2)) with eq_fx
  use a, b
  rw [<-eq_fx]
  have fx_deg : natDegree fx = 2 := by
    rw [eq_fx]
    compute_degree
    norm_num
  symm
  apply minpoly.unique' ℚ x _ _ _
  rw [Monic.def]
  unfold leadingCoeff
  rw [fx_deg]
  rw [eq_fx]
  simp
  rw [Polynomial.coeff_monomial]
  simp
  sorry
  · sorry
  · sorry



lemma ex_a_b_int_prove (x : K) (h : ∀ n : ℕ ,∃ m : ℤ , (Polynomial.coeff (minpoly ℚ x) n) = m) : ∃ a b : ℚ, a_b_int a b := by
  have ⟨a, b, hab⟩ := mem_K_minpoly x
  have ⟨n₀, nh₀⟩ := h 0
  have ⟨n₁, nh₁⟩ := h 1
  rw [hab] at nh₀ nh₁
  simp at nh₀ nh₁
  use a, b
  repeat' rw [<-Polynomial.monomial_zero_left] at nh₁
  repeat' rw [pow_two] at nh₁
  repeat' rw [Polynomial.coeff_monomial] at nh₁
  simp at nh₁
  have co₀ : coeff (C a ^ 2) 0 + 3 * coeff (C b ^ 2) 0 = a ^ 2 + 3 * b ^ 2 := by rw [pow_two, pow_two]; simp; ring
  rw [co₀] at nh₀
  use -n₁, n₀
  constructor
  · simp
    rw [<-nh₁]
    simp
  rw [<-nh₀]

-- 由以上关系式推出-3*(2*b)^2是整数
lemma two_b_sq_mul_neg_three_in_z {a b : ℚ} (h : a_b_int a b) : ∃ n : ℤ, 3 * (2 * b) ^ 2 = n := by
  have ⟨n₁, n₂, h₁, h₂⟩ := h
  have h' : (2 * a) ^ 2 + 3 * (2 * b) ^ 2 = 4 * n₂ := by
    rw [mul_pow, mul_pow, <-h₂]
    simp only [<-mul_assoc, mul_add]
    norm_num
  use (- n₁ ^ 2 + 4 * n₂)
  simp
  rw [<-h', <-h₁]
  simp

-- 设2*b（有理数）为q，写成分子（整数）除分母（自然数）的形式（由定义）
-- 再将分母乘至等式另一侧，得到在ℤ中关于分子和分母的等式
lemma den_mul_right {q : ℚ} (h : ∃ n : ℤ, 3 * q ^ 2 = n) : ∃ n : ℤ, 3 * q.num ^ 2 = n * ↑q.den ^ 2 := by
  rw [<-Rat.num_div_den q, div_pow, mul_div] at h
  have qden_nz : (↑q.den : ℚ) ≠ (↑(0 : ℕ) : ℚ) := by norm_cast; exact q.den_nz
  have q_pow_nz : (↑q.den : ℚ) ^ (2 : ℤ) ≠ (0 : ℤ) := by norm_cast; apply pow_ne_zero 2 q.den_nz
  have ⟨n, hn⟩ := h
  use n
  apply (div_eq_iff q_pow_nz).1 at hn
  norm_cast at *

-- 通过分析整除关系，得出上述等式中的n可被3整除
lemma n_of_fac_three {q : ℚ} {n : ℤ} : (3 * q.num ^ 2 = n * ↑q.den ^ 2) → 3 ∣ n := by
  intro nh
  have int_to_nat : (3 : ℕ) = (3 : ℤ) := by norm_num    -- 自然数的3（通过强制类型转换）等于整数的3
  have three_dvd_left : ((3 : ℕ) : ℤ) ∣ (3 * q.num ^ 2) := by rw [int_to_nat]; apply dvd_mul_right
  rw [nh] at three_dvd_left
  have three_pr : Nat.Prime 3 := by norm_num
  rcases Int.Prime.dvd_mul' three_pr three_dvd_left with h' | h'
  · rw [int_to_nat] at h'
    exact h'
  by_contra   -- 由条件即可得出矛盾，无需假设原结论为假
  rw [pow_two] at h'
  rcases Int.Prime.dvd_mul' three_pr h' with h'' | h'' <;> (
    -- 括号后进行分情况讨论，但是两个情况相同
  rw [dvd_def] at h''
  have ⟨c, ch⟩ :=h''
  ---- 代入由整除引入的等式，化简 ----
  rw [ch, mul_pow, <-int_to_nat] at nh
  have nh' : ↑3 * q.num ^ 2 = ↑3 * (↑3 * n * c ^ 2) := by
    repeat' rw [<-int_to_nat]
    calc
      _ = n * (↑3 ^ 2 * c ^ 2) := by rw [nh]; rfl
      _ = ↑3 * (↑3 * n * c ^ 2) := by ring
  have nh'' : q.num ^ 2 = 3 * n * c ^ 2 := by apply (Int.eq_of_mul_eq_mul_left _ nh'); norm_num
  ---- 化简结束 ----
  symm at nh''
  have three_dvd_left' : ((3 : ℕ) : ℤ) ∣ (3 * n * c ^ 2) := by rw [int_to_nat, mul_assoc]; apply dvd_mul_right
  rw [nh''] at three_dvd_left'
  rcases Int.Prime.dvd_mul' three_pr three_dvd_left' with h''' | h''' <;> (
    -- 括号后进行分情况讨论，但是两个情况相同
  simp at h'''
  rw [<-dvd_def] at h''
  apply Int.ofNat_dvd_left.1 at h'''
  apply Int.ofNat_dvd_left.1 at h''
  -- 接下来通过3分别整除分子和分母，得到矛盾
  simp at h''
  apply (Nat.dvd_gcd h''') at h''
  have cop : Nat.Coprime (Int.natAbs q.num) q.den := q.reduced
  rw [cop] at h''
  contradiction
  ))

--将n表示成n'和3的乘积，等式两边约去3，接着证明分母整除分子，再有分子分母互质知分母为1，因此q是整数
lemma q_in_z {q : ℚ}  : (∃ n : ℤ, 3 * q.num ^ 2 = n * ↑q.den ^ 2) → ∃ n : ℤ, q = ↑n := by
  rintro ⟨n, nh⟩
  have n_fac_three : 3 ∣ n := n_of_fac_three nh
  have ⟨c, ch⟩ := n_fac_three
  rw [ch] at nh
  rw [mul_assoc] at nh
  have nh' : q.num ^ 2 = c * ↑q.den ^ 2 := by apply (Int.eq_of_mul_eq_mul_left _ nh); norm_num
  have sq_dvd : (q.den : ℤ) ^ 2∣q.num ^ 2 := by rw [nh']; apply dvd_mul_left
  have two_gt_zero : 0 < 2 := by norm_num
  have den_dvd_num : (q.den : ℤ) ∣ q.num := by apply (Int.pow_dvd_pow_iff two_gt_zero).1; exact sq_dvd
  apply Int.ofNat_dvd_left.1 at den_dvd_num
  have den_dvd_self : q.den ∣ q.den := by rfl
  apply (Nat.dvd_gcd den_dvd_num) at den_dvd_self
  have cop : Nat.Coprime (Int.natAbs q.num) q.den := q.reduced
  rw [cop] at den_dvd_self
  rw [Nat.dvd_one] at den_dvd_self
  use q.num
  rw [<-Rat.num_div_den q]
  rw [den_dvd_self]
  simp

--还原q为2 * b，既有2 * b是整数
lemma two_b_in_z {a b : ℚ} (h : a_b_int a b) : ∃ n : ℤ, 2 * b = n := by
  have ⟨n, hn⟩ := (q_in_z (den_mul_right (two_b_sq_mul_neg_three_in_z h)))
  use n

-- 知2 * a和2 * b都是整数，通过关系式2得到2 * a和2 * b对模4同余
lemma asque_eq_bsqu {a b :ℚ} (h : a_b_int a b) :
    (∃ n₁ n₂ : ℤ , 2 * a = n₁ ∧ 2 * b = n₂ ∧ ∃ n : ℤ, n₁ * n₁ - n₂ * n₂ = 4 * n) := by
  -- 把2 * a和2 * b分别化为n₁和n₂
  have ⟨n₁, n, hn₁, hn⟩ := h
  have hn₁ := hn₁
  have ⟨n₂, hn₂⟩ := two_b_in_z h
  use n₁, n₂
  constructor
  · exact hn₁
  constructor
  · exact hn₂
  have h' : (2 * a) ^ 2 + 3 * (2 * b) ^ 2 = 4 * n := by
    rw [mul_pow, mul_pow, <-hn]
    simp only [<-mul_assoc, mul_add]
    norm_num
  rw [hn₁, hn₂, pow_two, pow_two] at h'
  norm_cast at h'
  use n - n₂ * n₂
  rw [mul_sub, <-h']
  ring

#check AdjoinRoot.aeval_eq
-- 通过2 * a和2 * b对模4同余，得知2 * a - 2 * b是偶数
-- 在本定理中，用a代表2 * a，用b代表2 * b
lemma quadratic_four_mod_eq {a b : ℤ} (asque_eq_bsqu: ∃ n : ℤ , a * a - b * b = 4 * n) :
  Even (a - b) := by
obtain ha := Int.even_or_odd a
have ⟨n, hn⟩ := asque_eq_bsqu
have hn' : b * b = a * a - 4 * n := by rw [← hn]; ring
have eq : Even (4 : ℤ) := by
  apply Int.even_iff.2
  simp
  norm_num
have h4 : Even (4 * n) := Int.even_mul.mpr (Or.inl eq)
have pow_mul : b * b = b ^ 2 := by ring
have hne : 2 ≠ 0 := by norm_num
rcases ha with haeven | haodd
· have ha' : Even (a * a) := Int.even_mul.mpr (Or.inl haeven)
  have hb  : Even (b * b) := by
    rw[hn']
    apply Int.even_sub.2
    tauto
  have hb' : Even b := by
    rw[pow_mul] at hb
    apply (Int.even_pow' hne).1
    assumption
  have : (Even a ↔ Even b) := by tauto
  have g1 : Even (a - b) := Int.even_sub.2 this
  exact g1
· have ha' : Odd (a * a) := by
    apply Int.odd_mul.2
    exact ⟨haodd , haodd⟩
  have hb  : Odd (b * b) := by
    rw[hn']
    apply Int.odd_sub.2
    tauto
  have hb' : Odd b := by
      rw[pow_mul] at hb
      apply (Int.odd_pow' hne).1
      assumption
  have :(Odd a ↔ Odd b) := by tauto
  have g1  : Even (a - b) := Int.even_sub'.2 this
  exact g1






lemma pre [hf : Fact (Irreducible fq)] (x : K)
(hab : ∃ (a b : ℤ), AdjoinRoot.mk fq (monomial 1 (b / 2 : ℚ) + C (a + b / 2 : ℚ)) = x):
(∀ n : ℕ ,∃ m : ℤ, (Polynomial.coeff (minpoly ℚ x) n) = m) := by
  have ⟨a , b , hab'⟩ := hab
  have : minpoly ℚ x = map (algebraMap ℤ ℚ) (monomial 2 1 - monomial 1 (2 * a + b) + C (a ^ 2 + a * b + b ^ 2)) := by
    let p := map (algebraMap ℤ ℚ) (monomial 2 1 - monomial 1 (2 * a + b) + C ( a ^ 2 + a * b + b ^ 2) )
    have deg_p : Polynomial.degree p = 2 := by sorry
    have hm : Polynomial.Monic p := by sorry
    have hp : (Polynomial.aeval x) p = 0 := by
      rw[← hab']
      simp only [map_add, map_intCast, AdjoinRoot.mk_C, eq_ratCast, Rat.cast_div, Rat.cast_coe_int,
        Rat.cast_ofNat, Polynomial.map_add, algebraMap_int_eq, Polynomial.map_sub, map_monomial,
        map_one, map_mul, map_ofNat, eq_intCast, map_pow, Polynomial.map_pow, map_int_cast,
        Polynomial.map_mul, map_sub, aeval_monomial, AdjoinRoot.algebraMap_eq, one_mul, pow_one]
      --simp
      sorry
    have hl : ∀ (q : Polynomial ℚ), Polynomial.degree q < Polynomial.degree p →
        q = 0 ∨ (Polynomial.aeval x) q ≠ 0 := by
      rw[deg_p]
      intro q h
      have two_eq_succ_one : (2 : WithBot ℕ) = Nat.succ 1 := by simp; norm_num
      by_contra! h'
      have : natDegree q ≤ 1 := by
        rw [degree_eq_natDegree _, two_eq_succ_one] at h
        norm_cast at h
        rw [Nat.lt_succ] at h
        exact h
        exact h'.1
      obtain ⟨c1, c0, rfl⟩ := exists_eq_X_add_C_of_natDegree_le_one this
      subst hab'
      simp at h'
      have : AdjoinRoot.mk fq ((c1 • (monomial 1 (↑b / 2 : ℚ) + C (↑a + ↑b / 2 : ℚ))) + C c0 : ℚ[X]) = 0
      · rw [map_add, ← AdjoinRoot.smul_mk, map_add, Algebra.smul_def]
        convert h'.2
        norm_cast
      absurd this
      apply AdjoinRoot.mk_ne_zero_of_degree_lt
      · apply fq_monic
      · sorry
      · suffices : degree (c1 • ((monomial 1) (↑b / 2 : ℚ) + C (↑a + ↑b / 2 : ℚ)) + C c0) ≤ 1
        · --rw[deg_fq']
          sorry
        compute_degree
    obtain ans := minpoly.unique' ℚ x hm hp hl
    symm
    exact ans
  rw[this]
  intro n
  cases' n with d1
  · use a ^ 2 + a * b + b ^ 2
    --simp
    sorry
  · cases' d1 with d2
    · use -(2 * a + b)
      --simp
      sorry
    · cases' d2 with d3
      · use 1
        --simp
        sorry
      · sorry

theorem Integral_Of_Form_iff [hf : Fact (Irreducible fq)] (x : K) :
    (∀ n : ℕ ,∃ m : ℤ , (Polynomial.coeff (minpoly ℚ x) n) = m) ↔
    ∃ (a b : ℤ ), AdjoinRoot.mk fq (monomial 1 (b / 2 : ℚ) + C (a + b / 2 : ℚ)) = x := by
  constructor
  · intro _
    have ⟨a, b, Adjoin_Root, a_b_int'⟩ := FormOfmem x
    have a_b_int'' := ex_a_b_int_prove x h
    have ⟨_, _⟩ := two_b_in_z a_b_int'
    have ⟨n₁', n₂', ah, bh, asque_eq_bsqu'⟩ := asque_eq_bsqu a_b_int'
    have ⟨n'', nh''⟩ := quadratic_four_mod_eq asque_eq_bsqu'
    use n'', n₂'
    have new_nh'' : 2 * (a - b) = 2 * ↑n'' := by
      symm; rw [two_mul]
      norm_cast; rw [<-nh'']; simp
      rw [<-ah, <-bh]; ring
    simp at new_nh''
    have rw_n : ((monomial 1) (n₂' / 2 : ℚ)) + C (↑n'' + ↑n₂' / 2 : ℚ) = ((monomial 1) b) + C a := by
      rw [<-bh, <-new_nh'']
      ring
    rw [rw_n]
    rw [Adjoin_Root]
  · apply pre
/--
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


structure K_eq_eisenstein  (eisensteinInt : Type u_8) [Mul K] [Mul eisensteinInt] [Add K] [Add eisensteinInt] extends Equiv :
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
--/
