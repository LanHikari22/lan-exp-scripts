{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wno-overlapping-patterns #-}

module MAlonzo.Code.Qcqts where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Agda.Primitive

-- cqts.LevelUniv
d_LevelUniv_2 :: ()
d_LevelUniv_2 = erased
-- cqts.Level
d_Level_4 :: ()
d_Level_4 = erased
-- cqts.ℓ-zero
d_ℓ'45'zero_6 :: MAlonzo.Code.Agda.Primitive.T_Level_18
d_ℓ'45'zero_6 = coe MAlonzo.Code.Agda.Primitive.d_lzero_20
-- cqts.ℓ-suc
d_ℓ'45'suc_8 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18
d_ℓ'45'suc_8 = coe MAlonzo.Code.Agda.Primitive.d_lsuc_24
-- cqts.ℓ-max
d_ℓ'45'max_10 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18
d_ℓ'45'max_10 = coe MAlonzo.Code.Agda.Primitive.d__'8852'__30
-- cqts.Type
d_Type_12 :: ()
d_Type_12 = erased
-- cqts.ℕ
d_ℕ_14 :: ()
d_ℕ_14 = erased
-- cqts._∙_
d__'8729'__16 :: Integer -> Integer -> Integer
d__'8729'__16 = coe mulInt
-- cqts.Number
d_Number_22 a0 a1 = ()
newtype T_Number_22 = C_constructor_32 (Integer -> AgdaAny)
-- cqts.Number.fromNat
d_fromNat_30 :: T_Number_22 -> Integer -> AgdaAny
d_fromNat_30 v0
  = case coe v0 of
      C_constructor_32 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- cqts._.fromNat
d_fromNat_36 :: T_Number_22 -> Integer -> AgdaAny
d_fromNat_36 v0 = coe d_fromNat_30 (coe v0)
-- cqts.Negative
d_Negative_42 a0 a1 = ()
newtype T_Negative_42 = C_constructor_52 (Integer -> AgdaAny)
-- cqts.Negative.fromNeg
d_fromNeg_50 :: T_Negative_42 -> Integer -> AgdaAny
d_fromNeg_50 v0
  = case coe v0 of
      C_constructor_52 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- cqts._.fromNeg
d_fromNeg_56 :: T_Negative_42 -> Integer -> AgdaAny
d_fromNeg_56 v0 = coe d_fromNeg_50 (coe v0)
-- cqts.Number-ℕ
d_Number'45'ℕ_62 :: T_Number_22
d_Number'45'ℕ_62 = coe C_constructor_32 (coe (\ v0 -> v0))
-- cqts.Σ-syntax
d_Σ'45'syntax_74 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> ()) -> ()
d_Σ'45'syntax_74 = erased
-- cqts._×_
d__'215'__84 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> () -> ()
d__'215'__84 = erased
-- cqts.case_of_
d_case_of__100 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
d_case_of__100 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_case_of__100 v4 v5
du_case_of__100 :: AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
du_case_of__100 v0 v1 = coe v1 v0
-- cqts.Test-Id-Family
d_Test'45'Id'45'Family_112 a0 a1 a2 a3 = ()
data T_Test'45'Id'45'Family_112 = C_test'45'id'45'refl_120
-- cqts.Test-Identical
d_Test'45'Identical_126 a0 a1 = ()
data T_Test'45'Identical_126
  = C_test'45'identical_136 AgdaAny AgdaAny
-- cqts.Test-Type
d_Test'45'Type_140 a0 = ()
newtype T_Test'45'Type_140 = C_test'45'type_150 AgdaAny
-- cqts.double
d_double_152 :: Integer -> Integer
d_double_152 v0 = coe d__'8729'__16 (2 :: Integer) v0
-- cqts.idfunℕ
d_idfunℕ_156 :: Integer -> Integer
d_idfunℕ_156 v0 = coe v0
-- cqts.idfunᵉ
d_idfun'7497'_162 :: () -> AgdaAny -> AgdaAny
d_idfun'7497'_162 ~v0 v1 = du_idfun'7497'_162 v1
du_idfun'7497'_162 :: AgdaAny -> AgdaAny
du_idfun'7497'_162 v0 = coe v0
-- cqts.×-ump-to
d_'215''45'ump'45'to_174 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'215''45'ump'45'to_174 ~v0 ~v1 ~v2 v3 v4 v5
  = du_'215''45'ump'45'to_174 v3 v4 v5
du_'215''45'ump'45'to_174 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'215''45'ump'45'to_174 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0 v2) (coe v1 v2)
-- cqts.×-ump-fro
d_'215''45'ump'45'fro_188 ::
  () ->
  () ->
  () ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'215''45'ump'45'fro_188 ~v0 ~v1 ~v2 v3
  = du_'215''45'ump'45'fro_188 v3
du_'215''45'ump'45'fro_188 ::
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'215''45'ump'45'fro_188 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         (\ v1 -> MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v0 v1)))
      (coe
         (\ v1 -> MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v0 v1)))
-- cqts.×-mapⁱ
d_'215''45'map'8305'_204 ::
  () ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'215''45'map'8305'_204 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_'215''45'map'8305'_204 v4 v5 v6
du_'215''45'map'8305'_204 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'215''45'map'8305'_204 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe v0 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2)))
      (coe v1 (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v2)))
-- cqts.Bool
d_Bool_216 = ()
data T_Bool_216 = C_true_218 | C_false_220
-- cqts.not
d_not_222 :: T_Bool_216 -> T_Bool_216
d_not_222 v0
  = coe
      du_case_of__100 (coe v0)
      (coe
         (\ v1 ->
            case coe v1 of
              C_true_218 -> coe C_false_220
              C_false_220 -> coe C_true_218
              _ -> MAlonzo.RTE.mazUnreachableError))
-- cqts._and_
d__and__228 :: T_Bool_216 -> T_Bool_216 -> T_Bool_216
d__and__228 v0 v1
  = coe
      du_case_of__100 (coe v0)
      (coe
         (\ v2 ->
            case coe v2 of
              C_true_218 -> coe du_case_of__100 (coe v1) (coe (\ v3 -> v3))
              C_false_220 -> coe v2
              _ -> MAlonzo.RTE.mazUnreachableError))
-- cqts._xor_
d__xor__238 :: T_Bool_216 -> T_Bool_216 -> T_Bool_216
d__xor__238 v0 v1
  = coe
      du_case_of__100 (coe v0)
      (coe
         (\ v2 ->
            case coe v2 of
              C_true_218
                -> coe
                     du_case_of__100 (coe v1)
                     (coe
                        (\ v3 ->
                           case coe v3 of
                             C_true_218 -> coe C_false_220
                             C_false_220 -> coe v2
                             _ -> MAlonzo.RTE.mazUnreachableError))
              C_false_220 -> coe du_case_of__100 (coe v1) (coe (\ v3 -> v3))
              _ -> MAlonzo.RTE.mazUnreachableError))
-- cqts._or_
d__or__250 :: T_Bool_216 -> T_Bool_216 -> T_Bool_216
d__or__250 v0 v1
  = coe
      du_case_of__100 (coe v0)
      (coe
         (\ v2 ->
            case coe v2 of
              C_true_218 -> coe v2
              C_false_220 -> coe v1
              _ -> MAlonzo.RTE.mazUnreachableError))
-- cqts._implies_
d__implies__258 :: T_Bool_216 -> T_Bool_216 -> T_Bool_216
d__implies__258 v0 v1
  = case coe v0 of
      C_true_218 -> coe v1
      C_false_220 -> coe C_true_218
      _ -> MAlonzo.RTE.mazUnreachableError
-- cqts.⊤-ump-in-to
d_'8868''45'ump'45'in'45'to_262 ::
  () ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
d_'8868''45'ump'45'in'45'to_262 ~v0 ~v1 ~v2
  = du_'8868''45'ump'45'in'45'to_262
du_'8868''45'ump'45'in'45'to_262 ::
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
du_'8868''45'ump'45'in'45'to_262
  = coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
-- cqts.⊤-ump-in-fro
d_'8868''45'ump'45'in'45'fro_270 ::
  () ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6) ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
d_'8868''45'ump'45'in'45'fro_270 ~v0 ~v1
  = du_'8868''45'ump'45'in'45'fro_270
du_'8868''45'ump'45'in'45'fro_270 ::
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
du_'8868''45'ump'45'in'45'fro_270
  = coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
-- cqts.⊤-ump-out-to
d_'8868''45'ump'45'out'45'to_276 ::
  () ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 -> AgdaAny
d_'8868''45'ump'45'out'45'to_276 ~v0 v1 ~v2
  = du_'8868''45'ump'45'out'45'to_276 v1
du_'8868''45'ump'45'out'45'to_276 :: AgdaAny -> AgdaAny
du_'8868''45'ump'45'out'45'to_276 v0 = coe v0
-- cqts.⊤-ump-out-fro
d_'8868''45'ump'45'out'45'fro_284 ::
  () ->
  (MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 -> AgdaAny) -> AgdaAny
d_'8868''45'ump'45'out'45'fro_284 ~v0 v1
  = du_'8868''45'ump'45'out'45'fro_284 v1
du_'8868''45'ump'45'out'45'fro_284 ::
  (MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 -> AgdaAny) -> AgdaAny
du_'8868''45'ump'45'out'45'fro_284 v0
  = coe v0 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- cqts.isZero
d_isZero_288 :: Integer -> T_Bool_216
d_isZero_288 v0
  = case coe v0 of
      0 -> coe C_true_218
      _ -> coe C_false_220
