module BinLists where

import Prelude hiding ((+), (*), (++), (&&),(||),not)

data Bin = One | ZeroAnd Bin | OneAnd Bin

data Nat = Z | S Nat

toNat' :: Bin -> Nat
toNat' = toNatFrom (S Z)

toNatFrom :: Nat -> Bin -> Nat
toNatFrom k One = k
toNatFrom k (ZeroAnd xs) = toNatFrom (k + k) xs
toNatFrom k (OneAnd xs) = k + toNatFrom (k + k) xs


toNat :: Bin -> Nat
toNat One = S Z
toNat (ZeroAnd xs) = toNat xs + toNat xs
toNat (OneAnd xs) = S (toNat xs + toNat xs)

infixl 6 +
infixl 7 *

(+) :: Nat -> Nat -> Nat
Z   + m = m
S n + m = S (n + m)

(*) :: Nat -> Nat -> Nat
Z * m = Z
S n * m = m + (n * m)

s :: Bin -> Bin
s One = ZeroAnd One
s (ZeroAnd xs) = OneAnd xs
s (OneAnd xs) = ZeroAnd (s xs)

plus :: Bin -> Bin -> Bin
plus One xs = s xs
plus xs@ZeroAnd{} One = s xs
plus xs@OneAnd{} One = s xs
plus (ZeroAnd xs) (ZeroAnd ys) = ZeroAnd (plus xs ys)
plus (ZeroAnd xs) (OneAnd ys) = OneAnd (plus xs ys)
plus (OneAnd xs) (ZeroAnd ys) = OneAnd (plus xs ys)
plus (OneAnd xs) (OneAnd ys) = ZeroAnd (s (plus xs ys))

