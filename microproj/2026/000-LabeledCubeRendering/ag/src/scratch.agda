open import cqts

data DualZero : Set where
   d0 : DualZero
  ~d0 : DualZero
 
 data DualInt : Set where
  di0 : List DualZero
