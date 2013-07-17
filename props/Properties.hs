module Properties where

import HipSpec.Prelude
import Prelude hiding (zipWith,curry,map,zip)

prop_compose f g h x = (f . (g . h)) x =:= ((f . g) . h) x

prop_let f x =
    (let twice g = f . g in twice (twice f)) x
    =:= (dbl (dbl f)) x
  where
    dbl g = g . f

prop_case xs =
    (case xs of { [] -> True; _ -> False }) =:=
    not (case xs of { [] -> False; _ -> True })

prop_assum x y = givenBool x (x =:= y ==> proveBool y)

prop_and x y = x && y =:= y && x

zipWith          :: (a->b->c) -> [a]->[b]->[c]
zipWith z (a:as) (b:bs)
                 =  z a b : zipWith z as bs
zipWith _ _ _    =  []

map :: (a -> b) -> [a] -> [b]
map f []     = []
map f (x:xs) = f x : map f xs

curry       :: ((a, b) -> c) -> a -> b -> c
curry f x y =  f (x, y)

zip               :: [a]->[b]->[(a,b)]
zip (a:as) (b:bs) = (a,b) : zip as bs
zip _ _           = []

prop_zw_map f xs ys = zipWith (curry f) xs ys =:= map f (zip xs ys)

prop_const :: a -> [b] -> Prop [a]
prop_const x xs = map (\ _ -> x) xs =:= zipWith (\ _ _ -> x) xs xs
