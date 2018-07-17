module Data.W 
-- W type , or well founded trees
-- https://github.com/agda/agda-stdlib/blob/master/src/Data/W.agda
-- https://mazzo.li/epilogue/index.html%3Fp=324.html
||| for more info,refer to the HoTT book on Inductive types->W type
data W : (A : Type)-> (B : A -> Type) -> Type where
  Sup : {A : Type}-> {B : A -> Type}->(x : A) -> (f : B x -> W A B) -> W A B

data Two : Type where
  T0 : Two
  T1 : Two
  
Nwf : Two -> Type
Nwf T0 = Void
Nwf T1 = Unit

-- type of Nat
Nw : Type
Nw = W Two Nwf


-- void : Void -> a,the elimitator of Empty(Void) type,which can be used to prove anything once you have sth : Void
||| zero of Nat
nw0 : Nw
nw0 = Sup T0 (\v => void v)

nw1 : Nw
nw1 = Sup T1 (\_ => nw0)
