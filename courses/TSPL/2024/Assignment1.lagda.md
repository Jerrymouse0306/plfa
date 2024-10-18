---
title     : "Assignment1: TSPL Assignment 1"
permalink : /TSPL/2024/Assignment1/
---

```agda
module Assignment1 where
```

## YOUR NAME AND EMAIL GOES HERE

name: Yunqi Zhao
email: s2723319

## Introduction

You must do _all_ the exercises labelled "(recommended)".

Exercises labelled "(stretch)" are there to provide an extra challenge.
You don't need to do all of these, but should attempt at least a few.

Exercises labelled "(practice)" are included for those who want extra practice.

Submit your homework using Gradescope. Go to the course page under Learn.
Select `Assessment`, then select `Assignment Submission`.
Please ensure your files execute correctly under Agda!


## Good Scholarly Practice.

Please remember the University requirement as
regards all assessed work. Details about this can be found at:

> [https://web.inf.ed.ac.uk/infweb/admin/policies/academic-misconduct](https://web.inf.ed.ac.uk/infweb/admin/policies/academic-misconduct)

You are required to take reasonable measures to protect
your assessed work from unauthorised access. For example, if you put
any such work on a public repository then you must set access
permissions appropriately (generally permitting access only to
yourself). Do not publish solutions to the coursework.

## Deadline and late policy

The deadline and late policy for this assignment are specified on
Learn in the "Coursework Planner". There are no extensions and
no ETAs. Coursework is marked best three out of four. Guidance
on late submissions is at

> [https://web.inf.ed.ac.uk/node/4533](https://web.inf.ed.ac.uk/node/4533)


## Naturals

```agda
module Naturals where
  import Relation.Binary.PropositionalEquality as Eq
  open Eq using (_≡_; refl)
  open Eq.≡-Reasoning using (begin_; step-≡-∣; _∎)
  open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)
```

#### Exercise `seven` (practice) {#seven}

Write out `7` in longhand.

```agda
  seven : ℕ
  seven = suc (suc (suc (suc (suc (suc (suc zero))))))
```

You will need to give both a type signature and definition for the
variable `seven`. Type `C-c C-l` in Emacs to instruct Agda to re-load.


#### Exercise `+-example` (practice) {#plus-example}

Compute `3 + 4`, writing out your reasoning as a chain of equations, using the equations for `+`.

```agda
  +-example : 3 + 4 ≡ 7
  +-example =
    begin
      3 + 4
    ≡⟨⟩
      (suc (suc (suc zero))) + (suc (suc (suc (suc zero))))
    ≡⟨⟩
      suc ((suc (suc zero)) + (suc (suc (suc (suc zero)))))
    ≡⟨⟩
      suc (suc ((suc zero) + (suc (suc (suc (suc zero))))))
    ≡⟨⟩
      suc (suc (suc (zero + (suc (suc (suc (suc zero)))))))
    ≡⟨⟩
      suc (suc (suc (suc (suc (suc (suc zero))))))
    ≡⟨⟩
      7
    ∎
```


#### Exercise `*-example` (practice) {#times-example}

Compute `3 * 4`, writing out your reasoning as a chain of equations, using the equations for `*`.
(You do not need to step through the evaluation of `+`.)

```agda
  *-example : 3 * 4 ≡ 12
  *-example =
    begin
      3 * 4
    ≡⟨⟩
      4 + (2 * 4)
    ≡⟨⟩
      4 + (4 + (1 * 4))
    ≡⟨⟩
      4 + (4 + (4 + (0 * 4)))
    ≡⟨⟩ 
      4 + (4 + (4 + 0))
    ≡⟨⟩
      12
    ∎
```


#### Exercise `_^_` (recommended) {#power}

Define exponentiation, which is given by the following equations:

```agda
  _^_ : ℕ → ℕ → ℕ
  m ^ 0        =  1
  m ^ (suc n)  =  m * (m ^ n)
```

Check that `3 ^ 4` is `81`.

```agda
  ^-example : 3 ^ 4 ≡ 81
  ^-example = 
    begin
      3 ^ 4
    ≡⟨⟩
      3 * (3 ^ 3)
    ≡⟨⟩
      3 * (3 * (3 ^ 2))
    ≡⟨⟩
      3 * (3 * (3 * (3 ^ 1)))
    ≡⟨⟩
      3 * (3 * (3 * (3 * (3 ^ 0))))
    ≡⟨⟩
      3 * (3 * (3 * (3 * 1)))
    ≡⟨⟩
      81
    ∎
```



#### Exercise `∸-example₁` and `∸-example₂` (recommended) {#monus-examples}

Compute `5 ∸ 3` and `3 ∸ 5`, writing out your reasoning as a chain of equations.

```agda
  ∸-example₁ : 5 ∸ 3 ≡ 2
  ∸-example₁ =
    begin
      5 ∸ 3
    ≡⟨⟩
      4 ∸ 2
    ≡⟨⟩
      3 ∸ 1
    ≡⟨⟩
      2 ∸ 0
    ≡⟨⟩
      2
    ∎
```
```agda
  ∸-example₂ : 3 ∸ 5 ≡ 0
  ∸-example₂ =
    begin
      3 ∸ 5
    ≡⟨⟩
      2 ∸ 4
    ≡⟨⟩
      1 ∸ 3
    ≡⟨⟩
      0 ∸ 2
    ≡⟨⟩
      0
    ∎
```


#### Exercise `Bin` (stretch) {#Bin}

A more efficient representation of natural numbers uses a binary
rather than a unary system.  We represent a number as a bitstring:
```agda
  data Bin : Set where
    ⟨⟩ : Bin
    _O : Bin → Bin
    _I : Bin → Bin
```
For instance, the bitstring

    1011

standing for the number eleven is encoded as

    ⟨⟩ I O I I
 
Representations are not unique due to leading zeros.
Hence, eleven is also represented by `001011`, encoded as:

    ⟨⟩ O O I O I I

Define a function

    inc : Bin → Bin

that converts a bitstring to the bitstring for the next higher
number.  For example, since `1100` encodes twelve, we should have:

    inc (⟨⟩ I O I I) ≡ ⟨⟩ I I O O

Confirm that this gives the correct answer for the bitstrings
encoding zero through four.

Using the above, define a pair of functions to convert
between the two representations.

    to   : ℕ → Bin
    from : Bin → ℕ

For the former, choose the bitstring to have no leading zeros if it
represents a positive natural, and represent zero by `⟨⟩ O`.
Confirm that these both give the correct answer for zero through four.

```agda
  inc : Bin → Bin
  inc ⟨⟩ = ⟨⟩ I
  inc (m O) = m I
  inc (m I) = inc m O 

  to : ℕ → Bin
  to (zero) = ⟨⟩ O
  to (suc m) = inc (to (m))

  from : Bin → ℕ
  from (⟨⟩) = zero
  from (m O) = 2 * from m
  from (m I) = suc (2 * from m)

  _from_zero : from (⟨⟩ O) ≡ 0
  _from_zero = refl
  _to_zero : to 0 ≡ (⟨⟩ O)
  _to_zero = refl

  _from_one : from (⟨⟩ I) ≡ 1
  _from_one = refl
  _to_one : to 1 ≡ (⟨⟩ I)
  _to_one = refl

  _from_two : from (⟨⟩ I O) ≡ 2
  _from_two = refl
  _to_two : to 2 ≡ (⟨⟩ I O)
  _to_two = refl

  _from_three : from (⟨⟩ I I) ≡ 3
  _from_three = refl
  _to_three : to 3 ≡ (⟨⟩ I I)
  _to_three = refl

  _from_four : from (⟨⟩ I O O) ≡ 4
  _from_four = refl
  _to_four : to 4 ≡ (⟨⟩ I O O)
  _to_four = refl
```



## Induction

```
module Induction where
```

## Imports

We require equality as in the previous chapter, plus the naturals
and some operations upon them.  We also require a couple of new operations,
`cong`, `sym`, and `_≡⟨_⟩_`, which are explained below:
```agda
  import Relation.Binary.PropositionalEquality as Eq
  open Eq using (_≡_; refl; cong; sym)
  open Eq.≡-Reasoning using (begin_; step-≡-∣; step-≡-⟩; _∎)
  open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _^_)
  open import Data.Nat.Properties using (+-assoc; +-identityʳ; +-suc; +-comm)
```
(Importing `step-≡` defines `_≡⟨_⟩_`.)


```
  open import plfa.part1.Induction
    hiding (+-assoc; +-comm; +-identityʳ; +-suc)
```

#### Exercise `operators` (practice) {#operators}

Give another example of a pair of operators that have an identity
and are associative, commutative, and distribute over one another.
(You do not have to prove these properties.)

intersection and union(⋂ and ⋃)

Give an example of an operator that has an identity and is
associative but is not commutative.
(You do not have to prove these properties.)

matrix multiplication


#### Exercise `finite-+-assoc` (stretch) {#finite-plus-assoc}

Write out what is known about associativity of addition on each of the
first four days using a finite story of creation, as
[earlier](/Naturals/#finite-creation).

  0: ℕ 
  1: ℕ 0 + (0 + 0) = (0 + 0) + 0
  2: ℕ 1 + (0 + 0) = (1 + 0) + 0, 0 + (1 + 0) = (0 + 1) + 0, 0 + (0 + 1) = (0 + 0) + 1
  3: ℕ 2 + (0 + 0) = (2 + 0) + 0, 0 + (2 + 0) = (0 + 2) + 0, 0 + (0 + 2) = (0 + 0) + 2
       1 + (1 + 0) = (1 + 1) + 0, 1 + (0 + 1) = (1 + 0) + 1, 0 + (1 + 1) = (0 + 1) + 1

#### Exercise `+-swap` (recommended) {#plus-swap}

Show

    m + (n + p) ≡ n + (m + p)

for all naturals `m`, `n`, and `p`. No induction is needed,
just apply the previous results which show addition
is associative and commutative.

```agda
  +-swap : ∀ (n m p : ℕ) → m + (n + p) ≡ n + (m + p)
  +-swap n m p = 
    begin
      m + (n + p)
    ≡⟨ sym (+-assoc m n p) ⟩
      (m + n) + p
    ≡⟨ cong (_+ p) (+-comm m n) ⟩ 
      (n + m) + p
    ≡⟨ +-assoc n m p ⟩
      n + (m + p)
    ∎
```


#### Exercise `*-distrib-+` (recommended) {#times-distrib-plus}

Show multiplication distributes over addition, that is,

    (m + n) * p ≡ m * p + n * p

for all naturals `m`, `n`, and `p`.

```agda
  *-distrib-+ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
  *-distrib-+ m zero p =
    begin
      (m + zero) * p
    ≡⟨ cong (_* p) (+-identityʳ m) ⟩
      m * p
    ≡⟨ sym ( +-identityʳ (m * p)) ⟩
      m * p + zero
    ≡⟨⟩
      m * p + zero * p
    ∎
  *-distrib-+ m (suc n) p =
    begin
      (m + suc n) * p
    ≡⟨ cong (_* p) ( +-suc m n) ⟩
      suc (m + n) * p
    ≡⟨⟩
      p + (m + n) * p
    ≡⟨ cong (p +_) (*-distrib-+ m n p) ⟩
      p + (m * p + n * p)
    ≡⟨ sym (+-assoc p (m * p) (n * p)) ⟩
      p + m * p + n * p
    ≡⟨ cong (_+ (n * p)) (+-comm p (m * p)) ⟩
      m * p + p + n * p
    ≡⟨ +-assoc (m * p) p (n * p) ⟩
      m * p + (p + n * p)
    ≡⟨⟩
      m * p + suc n * p
    ∎
``` 


#### Exercise `*-assoc` (recommended) {#times-assoc}

Show multiplication is associative, that is,

    (m * n) * p ≡ m * (n * p)

for all naturals `m`, `n`, and `p`.

```agda
  *-assoc : ∀ (m n p : ℕ) → (m * n) * p ≡ m * (n * p)
  *-assoc zero n p =
    begin
      (zero * n) * p
    ≡⟨⟩
      zero * p
    ≡⟨⟩
      zero
    ≡⟨⟩
      zero * (n * p)
    ∎
  *-assoc (suc m) n p = 
    begin
      (suc m * n) * p
    ≡⟨⟩
      (n + m * n) * p
    ≡⟨ *-distrib-+ n (m * n) p ⟩
      n * p + (m * n) * p
    ≡⟨ cong ((n * p) +_) (*-assoc m n p) ⟩
      n * p + m * (n * p)
    ≡⟨⟩
      suc m * (n * p)
    ∎
```


#### Exercise `*-comm` (practice) {#times-comm}

Show multiplication is commutative, that is,

    m * n ≡ n * m

for all naturals `m` and `n`.  As with commutativity of addition,
you will need to formulate and prove suitable lemmas.

```agda
  *-zero : ∀ (m : ℕ) → m * zero ≡ zero
  *-zero zero =
    begin
      zero * zero
    ≡⟨⟩
      zero
    ∎
  *-zero (suc m) = 
    begin
      suc m * zero
    ≡⟨⟩
      zero + m * zero
    ≡⟨ cong (zero +_) (*-zero m) ⟩
      zero + zero
    ≡⟨⟩
      zero
    ∎
  *-suc : ∀ (m n : ℕ) → m * suc n ≡ m + m * n
  *-suc zero n = 
    begin
      zero * suc n
    ≡⟨⟩
      zero
    ≡⟨⟩
      zero + zero
    ≡⟨⟩
      zero + zero * n
    ∎
  *-suc (suc m) n =
    begin
      suc m * suc n
    ≡⟨⟩
      suc n + (m * suc n)
    ≡⟨ cong ((suc n) +_) (*-suc m n)⟩
      suc n + (m + m * n)
    ≡⟨ sym (+-assoc (suc n) m (m * n)) ⟩
      suc n + m + m * n
    ≡⟨⟩
      suc (n + m) + m * n
    ≡⟨ cong (_+ (m * n)) (cong suc (+-comm n m))⟩
      suc (m + n) + m * n
    ≡⟨⟩
      suc m + n + m * n
    ≡⟨ +-assoc (suc m) n (m * n) ⟩
      suc m + (n + m * n)
    ≡⟨⟩
      suc m + suc m * n
    ∎ 
  *-comm : ∀ (m n : ℕ) → m * n ≡ n * m
  *-comm zero n =
    begin 
      zero * n
    ≡⟨⟩
      zero
    ≡⟨ sym (*-zero n) ⟩
      n * zero
    ∎
  *-comm (suc m) n =
    begin
      suc m * n
    ≡⟨⟩
      n + m * n
    ≡⟨ cong (n +_) (*-comm m n) ⟩ 
      n + n * m
    ≡⟨ sym (*-suc n m) ⟩
      n * suc m
    ∎
```


#### Exercise `0∸n≡0` (practice) {#zero-monus}

Show

    zero ∸ n ≡ zero

for all naturals `n`. Did your proof require induction?

```agda
  0∸n≡0 : ∀ (n : ℕ) → zero ∸ n ≡ zero
  0∸n≡0 zero =
    begin
      zero ∸ zero
    ≡⟨⟩
      zero
    ∎
  0∸n≡0 (suc n) =
    begin 
      zero ∸ suc n
    ≡⟨⟩
      zero
    ∎
  0∸n≡0' : ∀ (n : ℕ) → zero ∸ n ≡ zero
  0∸n≡0' zero = refl
  0∸n≡0' (suc n) = refl
```


#### Exercise `∸-+-assoc` (practice) {#monus-plus-assoc}

Show that monus associates with addition, that is,

    m ∸ n ∸ p ≡ m ∸ (n + p)

for all naturals `m`, `n`, and `p`.

```agda
  ∸-+-assoc : ∀ (m n p : ℕ) → m ∸ n ∸ p ≡ m ∸ (n + p)
  ∸-+-assoc zero n p rewrite 0∸n≡0 n | 0∸n≡0 p | 0∸n≡0 (n + p) = refl
  ∸-+-assoc (suc m) zero p = refl
  ∸-+-assoc (suc m) (suc n) p rewrite ∸-+-assoc m n p = refl
```


#### Exercise `+*^` (stretch)

Show the following three laws

     m ^ (n + p) ≡ (m ^ n) * (m ^ p)  (^-distribˡ-+-*)
     (m * n) ^ p ≡ (m ^ p) * (n ^ p)  (^-distribʳ-*)
     (m ^ n) ^ p ≡ m ^ (n * p)        (^-*-assoc)

for all `m`, `n`, and `p`.

```
  *-identityʳ : ∀ (m : ℕ) → m * 1 ≡ m
  *-identityʳ zero = refl
  *-identityʳ (suc m) rewrite *-identityʳ m = refl
  ^-distribˡ-+-* : ∀ (m n p : ℕ) → m ^ (n + p) ≡ (m ^ n) * (m ^ p)
  ^-distribˡ-+-* m n zero rewrite +-identityʳ n | *-identityʳ (m ^ n) = refl
  ^-distribˡ-+-* m n (suc p) rewrite +-suc n p | ^-distribˡ-+-* m n p | sym (*-assoc m (m ^ n) (m ^ p)) | *-comm m (m ^ n) | *-assoc (m ^ n) m (m ^ p) = refl
  ^-distribʳ-* : ∀ (m n p : ℕ) → (m * n) ^ p ≡ (m ^ p) * (n ^ p)
  ^-distribʳ-* m n zero rewrite *-identityʳ 1 = refl
  ^-distribʳ-* m n (suc p) rewrite ^-distribʳ-* m n p | sym (*-assoc (m * n) (m ^ p) (n ^ p)) | *-assoc m n (m ^ p) | *-comm n (m ^ p) | sym (*-assoc m (m ^ p) n) | *-assoc (m * m ^ p) n (n ^ p) = refl -- ques: cong (m *_) (sym (*-assoc n (m ^ p) (n ^ p)))
  ^-*-assoc : ∀ (m n p : ℕ) → (m ^ n) ^ p ≡ m ^ (n * p)
  ^-*-assoc m n zero rewrite *-zero n = refl
  ^-*-assoc m n (suc p) rewrite ^-*-assoc m n p | sym (^-distribˡ-+-* m n (n * p)) | sym (*-suc n p) = refl
```


#### Exercise `Bin-laws` (stretch) {#Bin-laws}

Recall that
Exercise [Bin](/Naturals/#Bin)
defines a datatype `Bin` of bitstrings representing natural numbers,
and asks you to define functions

    inc   : Bin → Bin
    to    : ℕ → Bin
    from  : Bin → ℕ

Consider the following laws, where `n` ranges over naturals and `b`
over bitstrings:

    from (inc b) ≡ suc (from b)
    to (from b) ≡ b
    from (to n) ≡ n

For each law: if it holds, prove; if not, give a counterexample.

```agda
  *-identityˡ : ∀ (n : ℕ) → 1 * n ≡ n
  *-identityˡ zero = refl
  *-identityˡ (suc n) rewrite *-identityˡ n = refl
```
```agda
  open Naturals using (Bin; to; from; inc; ⟨⟩; _I; _O)

  from_inc : ∀ (b : Bin) → from (inc b) ≡ suc (from b)
  from_inc ⟨⟩ = refl
  from_inc (b O) = refl
  from_inc (b I) =
    begin 
      from (inc (b I))
    ≡⟨⟩
      from (inc b O)
    ≡⟨⟩
      2 * from (inc b)
    ≡⟨ cong (2 *_) (from_inc b) ⟩
      2 * suc (from b)
    ≡⟨⟩
      suc (from b) + 1 * suc (from b)
    ≡⟨ cong ((suc (from b)) +_) (*-identityˡ (suc (from b))) ⟩
      suc (from b) + suc (from b)
    ≡⟨⟩
      suc (from b + suc (from b))
    ≡⟨ cong suc (+-suc (from b) (from b)) ⟩
      suc ( suc (from b + from b))
    ≡⟨ cong suc (cong suc (cong ((from b) +_)( sym (*-identityˡ (from b))))) ⟩
      suc ( suc (from b + 1 * (from b)))
    ≡⟨⟩
      suc ( suc (2 * from b))
    ≡⟨⟩
      suc (from (b I))
    ∎

  -- to (from b) ≡ b is not hold, because when b = ⟨⟩, to (from b) ≡ ⟨⟩ O

  from_to : ∀ (n : ℕ) → from (to n) ≡ n
  from_to zero = refl
  from_to (suc n) rewrite from_inc (to n) | from_to n = refl  
```



## Relations

```
module Relations where
```

## Imports

```agda
  import Relation.Binary.PropositionalEquality as Eq
  open Eq using (_≡_; refl; cong; sym)
  open Eq.≡-Reasoning using (begin_; step-≡-∣; step-≡-⟩; _∎)
  open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
  open import Data.Nat.Properties using (+-comm; +-identityʳ)
  open import Data.Nat using (_≤_; z≤n; s≤s)
  open import Data.Nat.Properties
    using (≤-refl; ≤-trans; ≤-antisym; ≤-total;
            +-monoʳ-≤; +-monoˡ-≤; +-mono-≤; +-assoc; +-identityʳ; +-suc; +-comm)
```

```agda
  open Induction
    hiding ()
  open Naturals
```

#### Exercise `orderings` (practice) {#orderings}

Give an example of a preorder that is not a partial order.

congruence, for example 8 mod 3 = 2 and 5 mod 3 = 2, so 8 and 5 is congruence in 3.

Give an example of a partial order that is not a total order.

subset ⊆

#### Exercise `≤-antisym-cases` (practice) {#leq-antisym-cases}

The above proof omits cases where one argument is `z≤n` and one
argument is `s≤s`.  Why is it ok to omit them?

```agda
  ≤-antisym-cases : ∀ {m : ℕ}
    → m ≤ zero
    ---------
    → m ≡ zero
  ≤-antisym-cases z≤n = refl
-- If one is zero, the other must be zero.
```


#### Exercise `*-mono-≤` (stretch)

Show that multiplication is monotonic with regard to inequality.

```agda
  *-mono-≤ʳ : ∀ (m n q : ℕ)
    → m ≤ n
      ---------
    → m * q ≤ n * q
  *-mono-≤ʳ m n zero m≤n rewrite *-zero m = z≤n
  *-mono-≤ʳ m n (suc q) m≤n rewrite *-suc m q | *-suc n q =  +-mono-≤ m≤n (*-mono-≤ʳ m n q m≤n)
  *-mono-≤ˡ : ∀ (m p q : ℕ)
    → p ≤ q
      ---------
    → m * p ≤ m * q
  *-mono-≤ˡ zero p q p≤q = z≤n
  *-mono-≤ˡ (suc m) p q p≤q rewrite *-suc p m = +-mono-≤ p≤q (*-mono-≤ˡ m p q p≤q)
  *-mono-≤ : ∀ (m n p q : ℕ)
    → m ≤ n
    → p ≤ q
      ----------
    → m * p ≤ n * q
  *-mono-≤ m n p q m≤n p≤q = ≤-trans (*-mono-≤ˡ m p q p≤q) (*-mono-≤ʳ m n q m≤n)
```


#### Exercise `<-trans` (recommended) {#less-trans}

Show that strict inequality is transitive. Use a direct proof. (A later
exercise exploits the relation between < and ≤.)

```agda
  open import plfa.part1.Relations using (_<_; z<s; s<s)
```

```agda
  <-trans : ∀ {m n p : ℕ}
    → m < n
    → n < p
      --------
    → m < p
  <-trans z<s (s<s _) = z<s
  <-trans (s<s m<n) (s<s n<p) = s<s (<-trans m<n n<p)
```

#### Exercise `trichotomy` (practice) {#trichotomy}

Show that strict inequality satisfies a weak version of trichotomy, in
the sense that for any `m` and `n` that one of the following holds:
* `m < n`,
* `m ≡ n`, or
* `m > n`.

Define `m > n` to be the same as `n < m`.
You will need a suitable data declaration,
similar to that used for totality.
(We will show that the three cases are exclusive after we introduce
[negation](/Negation/).)

```agda
  data trichotomy (m n : ℕ) : Set where
    tri_< :
      m < n
      → trichotomy m n
    tri_≡ :
      m ≡ n
      → trichotomy m n
    tri_> : 
      n < m 
      → trichotomy m n

  <-total : ∀ (m n : ℕ) → trichotomy m n
  <-total zero (suc n)                    = tri_< z<s
  <-total zero zero                       = tri_≡ refl
  <-total (suc m) zero                    = tri_> z<s
  <-total (suc m) (suc n) with <-total m n
  ...                       | tri_< m<n   = tri_< (s<s m<n)
  ...                       | tri_≡ refl  = tri_≡ refl
  ...                       | tri_> n<m   = tri_> (s<s n<m)
```

#### Exercise `+-mono-<` (practice) {#plus-mono-less}

Show that addition is monotonic with respect to strict inequality.
As with inequality, some additional definitions may be required.

```agda
  +-mono-<ʳ : ∀ (n p q : ℕ)
    → p < q
    → n + p < n + q
  +-mono-<ʳ zero p q p<q = p<q
  +-mono-<ʳ (suc n) p q p<q = s<s (+-mono-<ʳ n p q p<q)
  +-mono-<ˡ : ∀ (m n p : ℕ)
    → m < n
    → m + p < n + p
  +-mono-<ˡ m n zero m<n rewrite +-identityʳ m | +-identityʳ n = m<n 
  +-mono-<ˡ m n (suc p) m<n rewrite +-suc m p | +-suc n p = s<s (+-mono-<ˡ m n p m<n)
  +-mono-< : ∀ (m n p q : ℕ)
    → m < n
    → p < q
    → m + p < n + q
  +-mono-< m n p q m<n p<q = <-trans (+-mono-<ˡ m n p m<n) (+-mono-<ʳ n p q p<q)
```

#### Exercise `≤→<, <→≤` (recommended) {#leq-iff-less}

Show that `suc m ≤ n` implies `m < n`, and conversely.

```agda
  ≤→< : ∀ {m n : ℕ} 
    → suc m ≤ n 
    → m < n
  ≤→< {zero} (s≤s _) = z<s
  ≤→< {suc m} (s≤s suc_m≤n) = s<s (≤→< suc_m≤n)
  <→≤ : ∀ {m n : ℕ}
    → m < n
    → suc m ≤ n
  <→≤ z<s = (s≤s z≤n)
  <→≤ (s<s m<n) = s≤s (<→≤ m<n)
```

#### Exercise `<-trans-revisited` (practice) {#less-trans-revisited}

Give an alternative proof that strict inequality is transitive,
using the relation between strict inequality and inequality and
the fact that inequality is transitive.

```agda
  ≤-suc : ∀ (m : ℕ) → m ≤ suc m
  ≤-suc zero = z≤n
  ≤-suc (suc m) = s≤s (≤-suc m)
  <-trans-revisited : ∀ (m n p : ℕ)
    → m < n
    → n < p
    → m < p
  <-trans-revisited m n p m<n n<p = ≤→< (≤-trans (≤-trans (<→≤ m<n) (≤-suc n)) (<→≤ n<p))
```


#### Exercise `o+o≡e` (stretch) {#odd-plus-odd}

Show that the sum of two odd numbers is even.

```agda
  data even : ℕ → Set
  data odd  : ℕ → Set

  data even where

    zero :
        ---------
        even zero

    suc  : ∀ {n : ℕ}
      → odd n
        ------------
      → even (suc n)

  data odd where

    suc  : ∀ {n : ℕ}
      → even n
        -----------
      → odd (suc n)
```

```agda
  e+o≡o : ∀ {m n : ℕ}
    → even m
    → odd n
    → odd (m + n)
  o+o≡e : ∀ {m n : ℕ}
    → odd m
    → odd n
    → even (m + n)
  e+o≡o zero on = on
  e+o≡o (suc om) on = suc (o+o≡e om on)
  o+o≡e (suc em) on = suc (e+o≡o em on)
```

#### Exercise `Bin-predicates` (stretch) {#Bin-predicates}

Recall that
Exercise [Bin](/Naturals/#Bin)
defines a datatype `Bin` of bitstrings representing natural numbers.
Representations are not unique due to leading zeros.
Hence, eleven may be represented by both of the following:

    ⟨⟩ I O I I
    ⟨⟩ O O I O I I

Define a predicate

    Can : Bin → Set

over all bitstrings that holds if the bitstring is canonical, meaning
it has no leading zeros; the first representation of eleven above is
canonical, and the second is not.  To define it, you will need an
auxiliary predicate

    One : Bin → Set

that holds only if the bitstring has a leading one.  A bitstring is
canonical if it has a leading one (representing a positive number) or
if it consists of a single zero (representing zero).

Show that increment preserves canonical bitstrings:

    Can b
    ------------
    Can (inc b)

Show that converting a natural to a bitstring always yields a
canonical bitstring:

    ----------
    Can (to n)

Show that converting a canonical bitstring to a natural
and back is the identity:

    Can b
    ---------------
    to (from b) ≡ b

Hint: For each of these, you may first need to prove related
properties of `One`. It may also help to prove the following:

    One b
    ----------
    1 ≤ from b

    1 ≤ n
    ---------------------
    to (2 * n) ≡ (to n) O

The hypothesis `1 ≤ n` is required for the latter, because
`to (2 * 0) ≡ ⟨⟩ O` but `(to 0) O ≡ ⟨⟩ O O`.

```agda
  open Naturals using (Bin; inc; to; from; ⟨⟩; _O; _I)
  open Induction using (from_inc; from_to)
  data One : Bin → Set where
    first : One (⟨⟩ I)
    add_O : ∀ {b : Bin} → One b → One (b O)
    add_I : ∀ {b : Bin} → One b → One (b I)
  data Can : Bin → Set where
    trans : ∀ {b : Bin} → One b → Can b
    czero : Can (⟨⟩ O)
  one_inc : ∀ {b : Bin} → One b → One (inc b)
  one_inc first = add_O first
  one_inc (add_O oneb) = add_I oneb
  one_inc (add_I oneb) = add_O (one_inc oneb)

  can_inc : ∀ {b : Bin} → Can b → Can (inc b)
  can_inc czero = trans first
  can_inc (trans oneb) = trans (one_inc oneb)

  one_to : ∀ (n : ℕ) → One (to (suc n))
  one_to zero = first
  one_to (suc n) = one_inc (one_to n)

  can_to : ∀ (n : ℕ) → Can (to n)
  can_to zero = czero 
  can_to (suc n) = trans (one_to n)

  to-2*n : ∀ (n : ℕ) → 1 ≤ n → to (2 * n) ≡ (to n) O
  to-2*n 1 _ = refl
  to-2*n (suc n) _ = 
    begin
      to (2 * (suc n))
    ≡⟨⟩ 
      to (suc n + 1 * suc n)
    ≡⟨ cong to (cong ((suc n) +_) (*-identityˡ (suc n))) ⟩
      to (suc n + suc n)
    ≡⟨⟩
      to (suc (n + suc n))
    ≡⟨⟩
      inc (to (n + suc n))
    ≡⟨ cong inc (cong to (+-suc n n)) ⟩ 
      inc (to (suc (n + n)))
    ≡⟨⟩
      inc (inc (to (n + n)))
    ≡⟨ cong inc (cong inc (cong to (cong (n +_) (sym (*-identityˡ n))))) ⟩
      inc (inc (to (n + 1 * n)))
    ≡⟨⟩
      inc (inc (to (2 * n)))
    ≡⟨ cong inc (cong inc (to-2*n n _)) ⟩
      inc (inc ((to n) O))
    ≡⟨⟩
      inc ((to n) I)
    ≡⟨⟩
      inc (to n) O
    ∎
  
  -- ≤-2*n : ∀ (n : ℕ) → n ≤ 2 * n
  -- ≤-2*n zero = z≤n
  -- ≤-2*n (suc n) rewrite +-identityʳ n | sym (*-suc 2 n) | sym (+-identityʳ n) = s≤s (+-mono-<ʳ n 0 (suc n) z≤n)

  -- ≤-fromb : ∀ {b : Bin} → One b → 1 ≤ from b
  -- ≤-fromb first = s≤s z≤n
  -- ≤-fromb (add_O oneb) = ≤-trans (≤-fromb oneb) 

  can_to_from : ∀ (b : Bin) → Can b → to (from b) ≡ b
  can_to_from (⟨⟩ O) czero = refl
  can_to_from (b O) canbO = _
  can_to_from (b I) canbI = _
```