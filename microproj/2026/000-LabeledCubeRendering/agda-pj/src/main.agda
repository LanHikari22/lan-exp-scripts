-- open import Library.Prelude
-- -- open import cqts.1--Type-Theory.1-1--Types-and-Functions
-- -- open import cqts.1--Type-Theory.1-2--Inductive-Types
-- -- open import cqts.1--Type-Theory.1-3--Universes-and-More-Inductive-Types
-- -- open import cqts.1--Type-Theory.1-5--Propositions-as-Types
-- -- open import cqts.2--Paths-and-Identifications.2-1--Paths
-- -- open import cqts.2--Paths-and-Identifications.2-2--Equivalences-and-Path-Algebra
-- -- open import cqts.2--Paths-and-Identifications.2-3--Substitution-and-J
-- -- open import cqts.2--Paths-and-Identifications.2-4--Composition-and-Filling
-- -- open import cqts.2--Paths-and-Identifications.2-5--Transport


{-# OPTIONS --guardedness #-}

module main where

open import IO

main : Main
main = run (putStrLn "Hello, World!")
