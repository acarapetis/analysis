import Mathlib.Tactic
import Mathlib.Algebra.Group.MinimalAxioms

/-!
# Analysis I, Section 4.1: The integers

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Definition of the "Section 4.1" integers, `Section_4_1.Int`, as formal differences `a —— b` of
  natural numbers `a b:ℕ`, up to equivalence.  (This is a quotient of a scaffolding type
  `Section_4_1.PreInt`, which consists of formal differences without any equivalence imposed.)

- ring operations and order these integers, as well as an embedding of ℕ.

- Equivalence with the Mathlib integers `_root_.Int` (or `ℤ`), which we will use going forward.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

namespace Section_4_1

structure PreInt where
  minuend : ℕ
  subtrahend : ℕ

/-- Definition 4.1.1 -/
instance PreInt.instSetoid : Setoid PreInt where
  r a b := a.minuend + b.subtrahend = b.minuend + a.subtrahend
  iseqv := {
    refl := by intro x; rfl
    symm := by intro x y h; exact h.symm
    trans := by
      -- This proof is written to follow the structure of the original text.
      intro ⟨ a,b ⟩ ⟨ c,d ⟩ ⟨ e,f ⟩ h1 h2; simp_all
      have h3 := congrArg₂ (· + ·) h1 h2; simp at h3
      have : (a + f) + (c + d) = (e + b) + (c + d) := calc
        (a + f) + (c + d) = a + d + (c + f) := by abel
        _ = c + b + (e + d) := h3
        _ = (e + b) + (c + d) := by abel
      exact Nat.add_right_cancel this
    }

@[simp]
theorem PreInt.eq (a b c d:ℕ) : (⟨ a,b ⟩: PreInt) ≈ ⟨ c,d ⟩ ↔ a + d = c + b := by rfl

abbrev Int := Quotient PreInt.instSetoid

abbrev Int.formalDiff (a b:ℕ)  : Int := Quotient.mk PreInt.instSetoid ⟨ a,b ⟩

infix:100 " —— " => Int.formalDiff

/-- Definition 4.1.1 (Integers) -/
theorem Int.eq (a b c d:ℕ): a —— b = c —— d ↔ a + d = c + b :=
  ⟨ Quotient.exact, by intro h; exact Quotient.sound h ⟩

/-- Decidability of equality -/
instance Int.decidableEq : DecidableEq Int := by
  intro a b
  have : ∀ (n:PreInt) (m: PreInt),
      Decidable (Quotient.mk PreInt.instSetoid n = Quotient.mk PreInt.instSetoid m) := by
    intro ⟨ a,b ⟩ ⟨ c,d ⟩
    rw [eq]
    exact decEq _ _
  exact Quotient.recOnSubsingleton₂ a b this

/-- Definition 4.1.1 (Integers) -/
theorem Int.eq_diff (n:Int) : ∃ a b, n = a —— b := by apply n.ind _; intro ⟨ a, b ⟩; use a, b

/-- Lemma 4.1.3 (Addition well-defined) -/
instance Int.instAdd : Add Int where
  add := Quotient.lift₂ (fun ⟨ a, b ⟩ ⟨ c, d ⟩ ↦ (a+c) —— (b+d) ) (by
    intro ⟨ a, b ⟩ ⟨ c, d ⟩ ⟨ a', b' ⟩ ⟨ c', d' ⟩ h1 h2
    simp [Setoid.r] at *
    calc
      _ = (a+b') + (c+d') := by abel
      _ = (a'+b) + (c'+d) := by rw [h1,h2]
      _ = _ := by abel)

/-- Definition 4.1.2 (Definition of addition) -/
theorem Int.add_eq (a b c d:ℕ) : a —— b + c —— d = (a+c)——(b+d) := Quotient.lift₂_mk _ _ _ _

/-- Lemma 4.1.3 (Multiplication well-defined) -/
theorem Int.mul_congr_left (a b a' b' c d : ℕ) (h: a —— b = a' —— b') :
    (a*c+b*d) —— (a*d+b*c) = (a'*c+b'*d) —— (a'*d+b'*c) := by
  simp only [eq] at *
  calc
    _ = c*(a+b') + d*(a'+b) := by ring
    _ = c*(a'+b) + d*(a+b') := by rw [h]
    _ = _ := by ring

/-- Lemma 4.1.3 (Multiplication well-defined) -/
theorem Int.mul_congr_right (a b c d c' d' : ℕ) (h: c —— d = c' —— d') :
    (a*c+b*d) —— (a*d+b*c) = (a*c'+b*d') —— (a*d'+b*c') := by
  simp only [eq] at *
  calc
    _ = a*(c+d') + b*(c'+d) := by ring
    _ = a*(c'+d) + b*(c+d') := by rw [h]
    _ = _ := by ring

/-- Lemma 4.1.3 (Multiplication well-defined) -/
theorem Int.mul_congr {a b c d a' b' c' d' : ℕ} (h1: a —— b = a' —— b') (h2: c —— d = c' —— d') :
  (a*c+b*d) —— (a*d+b*c) = (a'*c'+b'*d') —— (a'*d'+b'*c') := by
  rw [mul_congr_left a b a' b' c d h1, mul_congr_right a' b' c d c' d' h2]

instance Int.instMul : Mul Int where
  mul := Quotient.lift₂ (fun ⟨ a, b ⟩ ⟨ c, d ⟩ ↦ (a * c + b * d) —— (a * d + b * c)) (by
    intro ⟨ a, b ⟩ ⟨ c, d ⟩ ⟨ a', b' ⟩ ⟨ c', d' ⟩ h1 h2; simp at h1 h2
    convert mul_congr _ _ <;> simpa
    )

/-- Definition 4.1.2 (Multiplication of integers) -/
theorem Int.mul_eq (a b c d:ℕ) : a —— b * c —— d = (a*c+b*d) —— (a*d+b*c) := Quotient.lift₂_mk _ _ _ _

instance Int.instOfNat {n:ℕ} : OfNat Int n where
  ofNat := n —— 0

instance Int.instNatCast : NatCast Int where
  natCast n := n —— 0

theorem Int.ofNat_eq (n:ℕ) : ofNat(n) = n —— 0 := rfl

theorem Int.natCast_eq (n:ℕ) : (n:Int) = n —— 0 := rfl

@[simp]
theorem Int.natCast_ofNat (n:ℕ) : ((ofNat(n):ℕ): Int) = ofNat(n) := by rfl

@[simp]
theorem Int.ofNat_inj (n m:ℕ) : (ofNat(n) : Int) = (ofNat(m) : Int) ↔ ofNat(n) = ofNat(m) := by
  simp only [ofNat_eq, eq, add_zero]; rfl

@[simp]
theorem Int.natCast_inj (n m:ℕ) : (n : Int) = (m : Int) ↔ n = m := by
  simp only [natCast_eq, eq, add_zero]

example : 3 = 3 —— 0 := rfl

example : 3 = 4 —— 1 := by rw [Int.ofNat_eq, Int.eq]

/-- (Not from textbook) 0 is the only natural whose cast is 0 -/
lemma Int.cast_eq_0_iff_eq_0 (n : ℕ) : (n : Int) = 0 ↔ n = 0 := by
  rw [natCast_eq, ofNat_eq, Int.eq]
  exact Nat.add_left_inj

/-- Definition 4.1.4 (Negation of integers) / Exercise 4.1.2 -/
instance Int.instNeg : Neg Int where
  neg := Quotient.lift (fun ⟨ a, b ⟩ ↦ b —— a) (by
    intro a b h
    rw [Int.eq]
    rw [PreInt.eq] at h
    omega
  )


theorem Int.neg_eq (a b:ℕ) : -(a —— b) = b —— a := rfl

example : -(3 —— 5) = 5 —— 3 := rfl

abbrev Int.IsPos (x:Int) : Prop := ∃ (n:ℕ), n > 0 ∧ x = n
abbrev Int.IsNeg (x:Int) : Prop := ∃ (n:ℕ), n > 0 ∧ x = -n

/-- Lemma 4.1.5 (trichotomy of integers )-/
theorem Int.trichotomous (x:Int) : x = 0 ∨ x.IsPos ∨ x.IsNeg := by
  -- This proof is slightly modified from that in the original text.
  obtain ⟨ a, b, rfl ⟩ := eq_diff x
  obtain h_lt | rfl | h_gt := _root_.trichotomous (r := LT.lt) a b
  . obtain ⟨ c, rfl ⟩ := Nat.exists_eq_add_of_lt h_lt
    right; right; refine ⟨ c+1, by linarith, ?_ ⟩
    simp_rw [natCast_eq, neg_eq, eq]; abel
  . left; simp_rw [ofNat_eq, eq, add_zero, zero_add]
  obtain ⟨ c, rfl ⟩ := Nat.exists_eq_add_of_lt h_gt
  right; left; refine ⟨ c+1, by linarith, ?_ ⟩
  simp_rw [natCast_eq, eq]; abel

/-- Lemma 4.1.5 (trichotomy of integers)-/
theorem Int.not_pos_zero (x:Int) : x = 0 ∧ x.IsPos → False := by
  rintro ⟨ rfl, ⟨ n, _, _ ⟩ ⟩; simp_all [←natCast_ofNat]

/-- Lemma 4.1.5 (trichotomy of integers)-/
theorem Int.not_neg_zero (x:Int) : x = 0 ∧ x.IsNeg → False := by
  rintro ⟨ rfl, ⟨ n, _, hn ⟩ ⟩; simp_rw [←natCast_ofNat, natCast_eq, neg_eq, eq] at hn
  linarith

/-- Lemma 4.1.5 (trichotomy of integers)-/
theorem Int.not_pos_neg (x:Int) : x.IsPos ∧ x.IsNeg → False := by
  rintro ⟨ ⟨ n, _, rfl ⟩, ⟨ m, _, hm ⟩ ⟩; simp_rw [natCast_eq, neg_eq, eq] at hm
  linarith

/-- Proposition 4.1.6 (laws of algebra) / Exercise 4.1.4 -/
instance Int.instAddGroup : AddGroup Int :=
  AddGroup.ofLeftAxioms (by 
    intro a b c
    obtain ⟨a1, a2, rfl⟩ := eq_diff a
    obtain ⟨b1, b2, rfl⟩ := eq_diff b
    obtain ⟨c1, c2, rfl⟩ := eq_diff c
    repeat rw [add_eq]
    rw [eq]
    linarith
  ) (by 
    intro a
    obtain ⟨a1, a2, rfl⟩ := eq_diff a
    rw [ofNat_eq, add_eq, eq]
    linarith
  ) (by 
    intro a
    obtain ⟨a1, a2, rfl⟩ := eq_diff a
    rw [neg_eq, add_eq, ofNat_eq, eq]
    linarith
  )

/-- Proposition 4.1.6 (laws of algebra) / Exercise 4.1.4 -/
instance Int.instAddCommGroup : AddCommGroup Int where
  add_comm := by
    intro a b
    obtain ⟨a1, a2, rfl⟩ := eq_diff a
    obtain ⟨b1, b2, rfl⟩ := eq_diff b
    rw [add_eq, add_eq, eq]
    linarith

/-- Proposition 4.1.6 (laws of algebra) / Exercise 4.1.4 -/
instance Int.instCommMonoid : CommMonoid Int where
  mul_comm := by
    intro a b
    obtain ⟨a1, a2, rfl⟩ := eq_diff a
    obtain ⟨b1, b2, rfl⟩ := eq_diff b
    rw [mul_eq, mul_eq, eq]
    linarith

  mul_assoc := by
    -- This proof is written to follow the structure of the original text.
    intro x y z
    obtain ⟨ a, b, rfl ⟩ := eq_diff x
    obtain ⟨ c, d, rfl ⟩ := eq_diff y
    obtain ⟨ e, f, rfl ⟩ := eq_diff z
    simp_rw [mul_eq]; 
    congr 1 <;> ring
  one_mul := by
    intro a
    obtain ⟨a1, a2, rfl⟩ := eq_diff a
    rw [ofNat_eq, mul_eq, eq]
    linarith
  mul_one := by
    intro a
    obtain ⟨a1, a2, rfl⟩ := eq_diff a
    rw [ofNat_eq, mul_eq, eq]
    linarith

/-- Proposition 4.1.6 (laws of algebra) / Exercise 4.1.4 -/
lemma Int.left_distrib (a b c: Int):  a * (b + c) = a * b + a * c := by
    obtain ⟨a1, a2, rfl⟩ := eq_diff a
    obtain ⟨b1, b2, rfl⟩ := eq_diff b
    obtain ⟨c1, c2, rfl⟩ := eq_diff c
    repeat rw [add_eq]
    repeat rw [mul_eq]
    repeat rw [add_eq]
    repeat rw [eq]
    linarith

lemma Int.zero_mul (a : Int): 0 * a = 0 := by
    obtain ⟨a1, a2, rfl⟩ := eq_diff a
    rw [ofNat_eq, mul_eq, eq]
    linarith

instance Int.instCommRing : CommRing Int where
  left_distrib := Int.left_distrib
  right_distrib := by grind only [left_distrib, mul_comm]
  zero_mul := zero_mul
  mul_zero := by intro a; rw [mul_comm]; exact zero_mul a

/-- Definition of subtraction -/
theorem Int.sub_eq (a b:Int) : a - b = a + (-b) := by rfl

theorem Int.sub_eq_formal_sub (a b:ℕ) : (a:Int) - (b:Int) = a —— b := by
  rw [natCast_eq, natCast_eq, sub_eq, neg_eq, add_eq, eq]
  linarith

lemma mul_co {a b: ℕ}: (a:Int) * (b:Int) = ↑(a * b) := by simp

/-- Proposition 4.1.8 (No zero divisors) / Exercise 4.1.5 -/
theorem Int.mul_eq_zero {a b:Int} (h: a * b = 0) : a = 0 ∨ b = 0 := by
  obtain h0 | ha := trichotomous a
  . exact Or.inl h0
  obtain h0 | hb := trichotomous b
  . exact Or.inr h0
  obtain ⟨α,hα⟩ | ⟨α,hα⟩ := ha <;> {
    rw [hα.2] at h ⊢ 
    obtain ⟨β,hβ⟩ | ⟨β,hβ⟩:= hb <;> {
      rw [hβ.2] at h ⊢ 
      try simp only [mul_neg, neg_mul, neg_eq_zero] at h
      rw [mul_co, cast_eq_0_iff_eq_0, Nat.mul_eq_zero] at h
      simpa [cast_eq_0_iff_eq_0] using h
    }
  }

/-- Corollary 4.1.9 (Cancellation law) / Exercise 4.1.6 -/
theorem Int.mul_right_cancel₀ (a b c:Int) (h: a*c = b*c) (hc: c ≠ 0) : a = b := by
  have hz : (a-b)*c = 0 := by grind only
  have := mul_eq_zero hz
  grind only

/-- Definition 4.1.10 (Ordering of the integers) -/
instance Int.instLE : LE Int where
  le n m := ∃ a:ℕ, m = n + a

/-- Definition 4.1.10 (Ordering of the integers) -/
instance Int.instLT : LT Int where
  lt n m := n ≤ m ∧ n ≠ m

theorem Int.le_iff (a b:Int) : a ≤ b ↔ ∃ t:ℕ, b = a + t := by rfl

theorem Int.lt_iff (a b:Int): a < b ↔ (∃ t:ℕ, b = a + t) ∧ a ≠ b := by rfl

/-- Lemma 4.1.11(a) (Properties of order) / Exercise 4.1.7 -/
theorem Int.lt_iff_exists_positive_difference (a b:Int) : a < b ↔ ∃ n:ℕ, n ≠ 0 ∧ b = a + n := by
  rw [lt_iff, <-exists_and_right, exists_congr]
  intro n
  constructor <;> simp_all [cast_eq_0_iff_eq_0]

/-- Lemma 4.1.11(b) (Addition preserves order) / Exercise 4.1.7 -/
theorem Int.add_lt_add_right {a b:Int} (c:Int) (h: a < b) : a+c < b+c := by
  rw [lt_iff_exists_positive_difference] at *
  grind

/-- Lemma 4.1.11(c) (Positive multiplication preserves order) / Exercise 4.1.7 -/
theorem Int.mul_lt_mul_of_pos_right {a b c:Int} (hab : a < b) (hc: 0 < c) : a*c < b*c := by
  rw [lt_iff_exists_positive_difference] at *
  obtain ⟨n, _⟩ := hab
  obtain ⟨cc, _⟩ := hc
  use n*cc
  simp_all [right_distrib]

/-- Lemma 4.1.11(d) (Negation reverses order) / Exercise 4.1.7 -/
theorem Int.neg_gt_neg {a b:Int} (h: b < a) : -a < -b := by
  rw [lt_iff_exists_positive_difference] at *
  peel h with n hnz heq
  simp_all

/-- Lemma 4.1.11(d) (Negation reverses order) / Exercise 4.1.7 -/
theorem Int.neg_ge_neg {a b:Int} (h: b ≤ a) : -a ≤ -b := by
  rw [le_iff] at *
  peel h with t heq
  simp_all

/-- Lemma 4.1.11(e) (Order is transitive) / Exercise 4.1.7 -/
theorem Int.lt_trans {a b c:Int} (hab: a < b) (hbc: b < c) : a < c := by
  rw [lt_iff_exists_positive_difference] at *
  obtain ⟨ba, hbanz, hbaeq⟩ := hab
  obtain ⟨cb, hcbnz, hcbeq⟩ := hbc
  use ba + cb
  simp_all [add_assoc]

lemma Int.pos_iff_gt_zero (a: Int): IsPos a ↔ a > 0 := by
  simp_rw [lt_iff_exists_positive_difference]
  simp_all [Nat.ne_zero_iff_zero_lt]

lemma Int.neg_iff_lt_zero (a: Int): IsNeg a ↔ a < 0 := by
  rw [<-gt_iff_lt]
  simp_rw [lt_iff_exists_positive_difference, Nat.ne_zero_iff_zero_lt]
  grind

lemma Int.sub_pos (a b: Int) : a > b ↔ a - b > 0 := by
  repeat rw [gt_iff_lt]
  simp_rw [lt_iff_exists_positive_difference, Nat.ne_zero_iff_zero_lt]
  grind

lemma Int.sub_neg (a b: Int) : a < b ↔ a - b < 0 := by
  simp_rw [lt_iff_exists_positive_difference, Nat.ne_zero_iff_zero_lt]
  grind


/-- Lemma 4.1.11(f) (Order trichotomy) / Exercise 4.1.7 -/
theorem Int.trichotomous' (a b:Int) : a > b ∨ a < b ∨ a = b := by
  rw [sub_pos, <-pos_iff_gt_zero]
  rw [sub_neg, <-neg_iff_lt_zero]
  rw [<-sub_eq_zero]
  have h := trichotomous (a-b)
  grind only [cases Or]

/-- Lemma 4.1.11(f) (Order trichotomy) / Exercise 4.1.7 -/
theorem Int.not_gt_and_lt (a b:Int) : ¬ (a > b ∧ a < b):= by
  rw [sub_pos, sub_neg, <-pos_iff_gt_zero, <-neg_iff_lt_zero]
  exact not_pos_neg (a-b)

/-- Lemma 4.1.11(f) (Order trichotomy) / Exercise 4.1.7 -/
theorem Int.not_gt_and_eq (a b:Int) : ¬ (a > b ∧ a = b):= by
  rw [sub_pos, <-sub_eq_zero, <-pos_iff_gt_zero]
  have := not_pos_zero (a-b)
  grind only

/-- Lemma 4.1.11(f) (Order trichotomy) / Exercise 4.1.7 -/
theorem Int.not_lt_and_eq (a b:Int) : ¬ (a < b ∧ a = b):= by
  rw [sub_neg, <-sub_eq_zero, <-neg_iff_lt_zero]
  have := not_neg_zero (a-b)
  grind only

/-- (Not from textbook) Establish the decidability of this order. -/
instance Int.decidableRel : DecidableRel (· ≤ · : Int → Int → Prop) := by
  intro n m
  have : ∀ (n:PreInt) (m: PreInt),
      Decidable (Quotient.mk PreInt.instSetoid n ≤ Quotient.mk PreInt.instSetoid m) := by
    intro ⟨ a,b ⟩ ⟨ c,d ⟩
    change Decidable (a —— b ≤ c —— d)
    cases (a + d).decLe (b + c) with
      | isTrue h =>
        apply isTrue
        rw [le_iff]
        obtain ⟨n, hn⟩ := le_iff_exists_add.mp h
        use n
        rw [natCast_eq, add_eq, eq]
        omega
      | isFalse h =>
        apply isFalse
        contrapose! h
        obtain ⟨n, hn⟩ := (le_iff ..).mp h
        rw [natCast_eq, add_eq, eq] at hn
        omega

  exact Quotient.recOnSubsingleton₂ n m this

/-- (Not from textbook) 0 is the only additive identity -/
lemma Int.is_additive_identity_iff_eq_0 (b : Int) : (∀ a, a = a + b) ↔ b = 0 := by
  simp only [left_eq_add, forall_const]

lemma Int.le_iff_eq_or_lt (a b: Int) : a ≤ b ↔ a < b ∨ a = b := by
  rw [le_iff, lt_iff_exists_positive_difference]
  constructor
  . intro ⟨n, hn⟩
    cases decEq n 0 <;> simp_all
  . intro h
    obtain ⟨n, hn⟩ | hab := h
    . exact ⟨n, hn.2⟩
    . exact ⟨0, by simp_all⟩ 

lemma Int.lt_iff_not_eq_or_gt (a b: Int) : a < b ↔ ¬ (a ≥ b) := by
  rw [ge_iff_le]
  constructor
  . grind only [not_gt_and_lt, le_iff_eq_or_lt, not_lt_and_eq]
  . grind only [le_iff_eq_or_lt, trichotomous']

lemma Int.le_of_lt {a b: Int} (h: a < b): a ≤ b := by
  rw [le_iff]
  rw [lt_iff_exists_positive_difference] at h
  obtain ⟨n, hn⟩ := h
  exact ⟨n, hn.2⟩

/-- (Not from textbook) Int has the structure of a linear ordering. -/
instance Int.instLinearOrder : LinearOrder Int where
  le_refl := by intro a; use 0; simp
  le_trans := by
    intro a b c hab hbc
    obtain ⟨ba, hbanz, hbaeq⟩ := hab
    obtain ⟨cb, hcbnz, hcbeq⟩ := hbc
    use ba + cb
    simp_all only [add_assoc, Nat.cast_add]
  lt_iff_le_not_ge := by grind [lt_iff_not_eq_or_gt, le_of_lt]
  le_antisymm := by
    intro a b hab hba
    obtain ⟨n, hn⟩ := hab
    obtain ⟨m, hm⟩ := hba
    subst hn
    have : ((n + m) : Int) = 0 := by grind only
    have : n + m = 0 := (cast_eq_0_iff_eq_0 (n+m)).mp this
    have := Nat.add_eq_zero.mp this
    simp_all
  le_total := by grind [trichotomous', le_iff_eq_or_lt]
  toDecidableLE := decidableRel

/-- Exercise 4.1.3 -/
theorem Int.neg_one_mul (a:Int) : -1 * a = -a := by
  rw [neg_mul, one_mul]

/-- Exercise 4.1.8 -/
theorem Int.no_induction : ∃ P: Int → Prop, (P 0 ∧ ∀ n, P n → P (n+1)) ∧ ¬ ∀ n, P n := by
  use fun n ↦ n ≥ 0
  constructor
  . constructor
    . rfl
    intro n hn
    rw [ge_iff_le, le_iff] at *
    obtain ⟨t, ht⟩ := hn
    use t+1
    simp_all
  push_neg
  use -1
  rw [lt_iff_exists_positive_difference]
  use 1
  simp_all

/-- A nonnegative number squared is nonnegative. This is a special case of 4.1.9 that's useful for proving the general case. --/
lemma Int.sq_nonneg_of_pos (n:Int) (h: 0 ≤ n) : 0 ≤ n*n := by
  obtain hpos | hz := le_iff_eq_or_lt 0 n |>.mp h
  . rw [<-zero_mul n]
    apply le_of_lt
    exact mul_lt_mul_of_pos_right hpos hpos
  . rw [<-hz]
    simp only [mul_zero, le_refl]

/-- Exercise 4.1.9. The square of any integer is nonnegative. -/
theorem Int.sq_nonneg (n:Int) : 0 ≤ n*n := by
  obtain hneg|hpos|hz := trichotomous' 0 n
  . set m := -n with hmn
    rw [show n*n = m*m by grind only]
    apply sq_nonneg_of_pos
    apply le_of_lt
    have := neg_gt_neg hneg
    simpa [gt_iff_lt, neg_zero]
  . exact le_of_lt hpos |> sq_nonneg_of_pos n
  . simp [<-hz]

/-- Exercise 4.1.9 -/
theorem Int.sq_nonneg' (n:Int) : ∃ (m:Nat), n*n = m := by
  have h := n.sq_nonneg
  set a := n*n
  obtain ⟨t, ht⟩ := le_iff 0 a |>.mp h
  use t
  simp_all only [zero_add]

/--
  Not in textbook: create an equivalence between Int and ℤ.
  This requires some familiarity with the API for Mathlib's version of the integers.
-/
abbrev Int.equivInt : Int ≃ ℤ where
  toFun := Quotient.lift (fun ⟨ a, b ⟩ ↦ a - b) (by
    intro ⟨a,b⟩ ⟨c,d⟩ h
    rw [PreInt.eq] at h
    linarith
  )
  invFun (n: ℤ) := if n ≥ 0 then n.toNat —— 0 else 0 —— n.natAbs
  left_inv n := by
    obtain hpos|hneg|hz := trichotomous' n 0
    . obtain ⟨a, b, hab⟩ := eq_diff n
      simp_rw [hab]
      simp only [Quotient.lift_mk, Int.sub_nonneg, Nat.cast_le, Int.toNat_sub', Int.toNat_natCast]
      have : b ≤ a := by
        rw [hab, gt_iff_lt, lt_iff_exists_positive_difference] at hpos
        obtain ⟨n, ⟨hnz, heq⟩⟩ := hpos
        rw [zero_add, natCast_eq, eq, add_zero] at heq
        grind only
      grind only [eq, cases Or]
    . obtain ⟨a, b, hab⟩ := eq_diff n
      simp_rw [hab]
      simp only [Quotient.lift_mk, Int.sub_nonneg, Nat.cast_le, Int.toNat_sub', Int.toNat_natCast]
      have : b ≥ a := by
        rw [hab, lt_iff_exists_positive_difference] at hneg
        obtain ⟨n, ⟨hnz, heq⟩⟩ := hneg
        rw [natCast_eq, add_eq, add_zero, ofNat_eq, eq] at heq
        grind only
      grind only [eq, cases Or]
    simp_rw [hz]
    have h0: (0: Int) = Quotient.mk _ ⟨0, 0⟩ := by rfl
    simp [h0, Quotient.lift_mk]
  right_inv n := by
    simp_rw [show n.toNat —— 0 = Quotient.mk _ ⟨n.toNat, 0⟩ by rfl]
    split_ifs with h <;> simp_all [Quotient.lift_mk]
    rw [neg_eq_iff_eq_neg, abs_eq_neg_self]
    grind only

lemma Int.le_preint (a b c d : ℕ) : a —— b ≤ c —— d ↔ a + d ≤ b + c := by
  rw [le_iff]
  constructor
  . intro ⟨t,ht⟩
    rw [natCast_eq, add_eq, eq] at ht
    linarith
  . intro h
    obtain ⟨n, hn⟩ := le_iff_exists_add.mp h
    use n
    rw [natCast_eq, add_eq, eq]
    linarith

/-- Not in textbook: equivalence preserves order and ring operations -/
abbrev Int.equivInt_ordered_ring : Int ≃+*o ℤ where
  toEquiv := equivInt
  map_add' := by
    intro x y
    apply x.ind; intro ⟨a,b⟩
    apply y.ind; intro ⟨c,d⟩
    rw [add_eq]
    simp_rw [Quotient.lift_mk]
    grind only
  map_mul' := by
    intro x y
    apply x.ind; intro ⟨a,b⟩
    apply y.ind; intro ⟨c,d⟩
    rw [mul_eq]
    simp_rw [Quotient.lift_mk]
    grind only
  map_le_map_iff' := by
    intro x y
    apply x.ind; intro ⟨a,b⟩
    apply y.ind; intro ⟨c,d⟩
    rw [le_preint]
    simp_rw [Quotient.lift_mk]
    grind only [cases Or]

end Section_4_1
