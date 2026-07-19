{-# OPTIONS --without-K --exact-split --safe #-}

module book.03-natural-numbers where

import book.02-pi
open book.02-pi public

--------------------------------------------------------------------------------
--Revised by James Squires (2026)

-- Section 3.1 The formal specification of the type of natural numbers

data ℕ : UU lzero where
  zero-ℕ : ℕ
  succ-ℕ : ℕ → ℕ

{- We define the numbers one-ℕ to twenty-ℕ -}

one-ℕ : ℕ
one-ℕ = succ-ℕ zero-ℕ

two-ℕ : ℕ
two-ℕ = succ-ℕ one-ℕ

three-ℕ : ℕ
three-ℕ = succ-ℕ two-ℕ

four-ℕ : ℕ
four-ℕ = succ-ℕ three-ℕ

five-ℕ : ℕ
five-ℕ = succ-ℕ four-ℕ

six-ℕ : ℕ
six-ℕ = succ-ℕ five-ℕ

seven-ℕ : ℕ
seven-ℕ = succ-ℕ six-ℕ

eight-ℕ : ℕ
eight-ℕ = succ-ℕ seven-ℕ

nine-ℕ : ℕ
nine-ℕ = succ-ℕ eight-ℕ

ten-ℕ : ℕ
ten-ℕ = succ-ℕ nine-ℕ

eleven-ℕ : ℕ
eleven-ℕ = succ-ℕ ten-ℕ

twelve-ℕ : ℕ
twelve-ℕ = succ-ℕ eleven-ℕ

thirteen-ℕ : ℕ
thirteen-ℕ = succ-ℕ twelve-ℕ

fourteen-ℕ : ℕ
fourteen-ℕ = succ-ℕ thirteen-ℕ

fifteen-ℕ : ℕ
fifteen-ℕ = succ-ℕ fourteen-ℕ

sixteen-ℕ : ℕ
sixteen-ℕ = succ-ℕ fifteen-ℕ

seventeen-ℕ : ℕ
seventeen-ℕ = succ-ℕ sixteen-ℕ

eighteen-ℕ : ℕ
eighteen-ℕ = succ-ℕ seventeen-ℕ

nineteen-ℕ : ℕ
nineteen-ℕ = succ-ℕ eighteen-ℕ

twenty-ℕ : ℕ
twenty-ℕ = succ-ℕ nineteen-ℕ

-- Remark 3.1.2
ind-ℕ : {i : Level} {P : ℕ → UU i} → P zero-ℕ → ((n : ℕ) → P n → P(succ-ℕ n)) → ((n : ℕ) → P n)
ind-ℕ p0 pS zero-ℕ = p0 -- Computation base case
ind-ℕ p0 pS (succ-ℕ n) = pS n (ind-ℕ p0 pS n) -- Computation induction

--------------------------------------------------------------------------------

-- Section 3.2 Addition on the natural numbers

-- Definition 3.2.1 with computation rules
add-ℕ : ℕ → (ℕ → ℕ)
add-ℕ m zero-ℕ = m
add-ℕ m (succ-ℕ n) = succ-ℕ (add-ℕ m n)

--Remark 3.2.2 on addition operator
add-zeroℕ : ℕ → ℕ
add-zeroℕ m = m

add-succℕ : ℕ → (ℕ → ℕ) → (ℕ → ℕ)
add-succℕ = λ m f n → succ-ℕ (f n) -- f is the induction hypothesis
--------------------------------------------------------------------------------

--BONUS TEST
two-plus-two : add-ℕ two-ℕ two-ℕ ≡ four-ℕ
two-plus-two = refl

-- Exercise 3.1 (a)
mul-ℕ : ℕ → (ℕ → ℕ)
mul-ℕ m zero-ℕ = zero-ℕ
mul-ℕ m (succ-ℕ n) = add-ℕ m (mul-ℕ m n)

--TEST
two-times-one : mul-ℕ two-ℕ one-ℕ ≡ two-ℕ
two-times-one = refl

two-times-two : mul-ℕ two-ℕ two-ℕ ≡ four-ℕ
two-times-two = refl

-- Exercise 3.1 (b)
exp-ℕ : ℕ → (ℕ → ℕ)
exp-ℕ m zero-ℕ = one-ℕ
exp-ℕ m (succ-ℕ n) = (mul-ℕ (exp-ℕ m n) m)

--TEST
two-exp-one : exp-ℕ two-ℕ one-ℕ ≡ two-ℕ
two-exp-one = refl

two-exp-four : exp-ℕ two-ℕ four-ℕ ≡ sixteen-ℕ
two-exp-four = refl

-- Exercise 3.2
-- Max
-- Think nested induction, we eliminate the right side with the first clause, then we perform pattern matching for the left-side with the 2nd and 3rd clauses
max-ℕ : ℕ → (ℕ → ℕ)
max-ℕ zero-ℕ m = m
max-ℕ (succ-ℕ m) zero-ℕ  = succ-ℕ m
max-ℕ (succ-ℕ m) (succ-ℕ n) = succ-ℕ (max-ℕ m n)

-- TEST
max-three-seven : max-ℕ three-ℕ seven-ℕ ≡ seven-ℕ
max-three-seven = refl

-- Min
min-ℕ : ℕ → (ℕ → ℕ)
min-ℕ zero-ℕ m = zero-ℕ
min-ℕ (succ-ℕ n) zero-ℕ = zero-ℕ
min-ℕ (succ-ℕ n) (succ-ℕ m) = succ-ℕ (min-ℕ m n)

two-min-five : min-ℕ two-ℕ five-ℕ ≡ two-ℕ
two-min-five = refl

-- Exercise 3.3
-- (a)
triangle-number-ℕ : ℕ → ℕ
triangle-number-ℕ zero-ℕ = zero-ℕ
triangle-number-ℕ (succ-ℕ n) = add-ℕ (triangle-number-ℕ n) (succ-ℕ n)

-- Test
triangle-four : triangle-number-ℕ four-ℕ ≡ ten-ℕ
triangle-four = refl

-- (b)
factorial : ℕ → ℕ
factorial zero-ℕ = one-ℕ
factorial (succ-ℕ n) = mul-ℕ (factorial n) (succ-ℕ n)

-- Test
three-factorial : factorial three-ℕ ≡ six-ℕ
three-factorial = refl

-------------------------------------------
-- Exercise 3.4

_choose-ℕ_ : ℕ → ℕ → ℕ
zero-ℕ choose-ℕ zero-ℕ = one-ℕ
zero-ℕ choose-ℕ succ-ℕ k = zero-ℕ
(succ-ℕ n) choose-ℕ zero-ℕ = one-ℕ
(succ-ℕ n) choose-ℕ (succ-ℕ k) = add-ℕ (n choose-ℕ k) (n choose-ℕ (succ-ℕ k))


-- Exercise 3.5

Fibonacci-ℕ : ℕ → ℕ
Fibonacci-ℕ zero-ℕ = zero-ℕ
Fibonacci-ℕ (succ-ℕ zero-ℕ) = one-ℕ
Fibonacci-ℕ (succ-ℕ (succ-ℕ n)) = add-ℕ (Fibonacci-ℕ (succ-ℕ n)) (Fibonacci-ℕ n)

{- The above definition of the Fibonacci sequence uses Agda's rather strong
   pattern matching definitions. Below, we will give a definition of the 
   Fibonacci sequence in terms of ind-ℕ. In particular, the following is a
   solution that can be given in terms of the material in the book. 

   The problem with defining the Fibonacci sequence using ind-ℕ, is that ind-ℕ
   doesn't give us a way to refer to both (F n) and (F (succ-ℕ n)). So, we have
   to give a workaround, where we store two values in the Fibonacci sequence
   at once.

   The basic idea is that we define a sequence of pairs of integers, which will
   be consecutive Fibonacci numbers. This would be a function of type

   ℕ → ℕ².

   Such a function is easy to give with induction, using the map ℕ² → ℕ² that
   takes a pair (m,n) to the pair (n,n+m). Starting the iteration with (0,1)
   we obtain the Fibonacci sequence by taking the first projection.

   However, we haven't defined cartesian products or booleans yet. Therefore
   we mimic the above idea, using ℕ → ℕ instead of ℕ². -}

shift-one : ℕ → (ℕ → ℕ) → (ℕ → ℕ)
shift-one n f = ind-ℕ n (λ x y → f x)

shift-two : ℕ → ℕ → (ℕ → ℕ) → (ℕ → ℕ)
shift-two m n f = shift-one m (shift-one n f)

Fibo-zero-ℕ : ℕ → ℕ
Fibo-zero-ℕ = shift-two zero-ℕ one-ℕ (const ℕ ℕ zero-ℕ)

Fibo-succ-ℕ : (ℕ → ℕ) → (ℕ → ℕ)
Fibo-succ-ℕ f =
  shift-two (f one-ℕ) (add-ℕ (f one-ℕ) (f zero-ℕ)) (const ℕ ℕ zero-ℕ)

Fibo-function : ℕ → ℕ → ℕ
Fibo-function =
  ind-ℕ
    ( Fibo-zero-ℕ)
    ( λ n → Fibo-succ-ℕ)

Fibo : ℕ → ℕ
Fibo k = Fibo-function k zero-ℕ

-- Exercise 3.6

div-two-ℕ : ℕ → ℕ
div-two-ℕ zero-ℕ = zero-ℕ
div-two-ℕ (succ-ℕ zero-ℕ) = zero-ℕ
div-two-ℕ (succ-ℕ (succ-ℕ n)) = succ-ℕ (div-two-ℕ n)

div-two-zero-ℕ : ℕ → ℕ
div-two-zero-ℕ = const ℕ ℕ zero-ℕ

div-two-succ-ℕ : (ℕ → ℕ) → (ℕ → ℕ)
div-two-succ-ℕ f =
  shift-two (f one-ℕ) (succ-ℕ (f zero-ℕ)) (const ℕ ℕ zero-ℕ)

div-two-function : ℕ → ℕ → ℕ
div-two-function = ind-ℕ div-two-zero-ℕ (λ n → div-two-succ-ℕ)

div-two-ℕ' : ℕ → ℕ
div-two-ℕ' n = div-two-function n zero-ℕ
