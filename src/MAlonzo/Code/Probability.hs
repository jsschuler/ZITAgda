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

module MAlonzo.Code.Probability where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.GCD
import qualified MAlonzo.Code.Data.Rational.Base
import qualified MAlonzo.Code.Data.Rational.Properties

-- Probability.Pointwise≤
d_Pointwise'8804'_2 a0 a1 = ()
data T_Pointwise'8804'_2
  = C_pw'45'nil_4 |
    C_pw'45'cons_14 MAlonzo.Code.Data.Rational.Base.T__'8804'__54
                    T_Pointwise'8804'_2
-- Probability.StrictAt
d_StrictAt_16 a0 a1 = ()
data T_StrictAt_16
  = C_here_26 MAlonzo.Code.Data.Rational.Base.T__'60'__62
              T_Pointwise'8804'_2 |
    C_there_36 MAlonzo.Code.Data.Rational.Base.T__'8804'__54
               T_StrictAt_16
-- Probability.sumQ
d_sumQ_38 ::
  [MAlonzo.Code.Data.Rational.Base.T_ℚ_6] ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6
d_sumQ_38 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Data.Rational.Base.d_0ℚ_178
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.Rational.Base.d__'43'__270 (coe v1)
             (coe d_sumQ_38 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Probability.0≤a+b
d_0'8804'a'43'b_48 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54
d_0'8804'a'43'b_48 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Rational.Properties.d_'43''45'mono'45''8804'_4360
      (coe
         MAlonzo.Code.Data.Rational.Base.C_mkℚ_24
         (coe
            MAlonzo.Code.Data.Nat.Base.du__'47'__318 (coe (0 :: Integer))
            (coe
               MAlonzo.Code.Data.Nat.GCD.d_gcd_152 (coe (0 :: Integer))
               (coe (1 :: Integer))))
         (0 :: Integer))
      (coe v0)
      (coe
         MAlonzo.Code.Data.Rational.Base.C_mkℚ_24
         (coe
            MAlonzo.Code.Data.Nat.Base.du__'47'__318 (coe (0 :: Integer))
            (coe
               MAlonzo.Code.Data.Nat.GCD.d_gcd_152 (coe (0 :: Integer))
               (coe (1 :: Integer))))
         (0 :: Integer))
      (coe v1) (coe v2) (coe v3)
-- Probability.sumQNonNeg
d_sumQNonNeg_64 ::
  [MAlonzo.Code.Data.Rational.Base.T_ℚ_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54
d_sumQNonNeg_64 v0 v1
  = case coe v0 of
      []
        -> coe
             seq (coe v1)
             (coe
                MAlonzo.Code.Data.Rational.Properties.d_'8804''45'refl_3606
                (coe MAlonzo.Code.Data.Rational.Base.d_0ℚ_178))
      (:) v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v6 v7
               -> coe
                    d_0'8804'a'43'b_48 (coe v2) (coe d_sumQ_38 (coe v3)) (coe v6)
                    (coe d_sumQNonNeg_64 (coe v3) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Probability.sumQMono
d_sumQMono_78 ::
  [MAlonzo.Code.Data.Rational.Base.T_ℚ_6] ->
  [MAlonzo.Code.Data.Rational.Base.T_ℚ_6] ->
  T_Pointwise'8804'_2 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54
d_sumQMono_78 v0 v1 v2
  = case coe v2 of
      C_pw'45'nil_4
        -> coe
             MAlonzo.Code.Data.Rational.Properties.d_'8804''45'refl_3606
             (coe d_sumQ_38 (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
      C_pw'45'cons_14 v7 v8
        -> case coe v0 of
             (:) v9 v10
               -> case coe v1 of
                    (:) v11 v12
                      -> coe
                           MAlonzo.Code.Data.Rational.Properties.d_'43''45'mono'45''8804'_4360
                           (coe v9) (coe v11) (coe d_sumQ_38 (coe v10))
                           (coe d_sumQ_38 (coe v12)) (coe v7)
                           (coe d_sumQMono_78 (coe v10) (coe v12) (coe v8))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Probability.sumQStrict
d_sumQStrict_88 ::
  [MAlonzo.Code.Data.Rational.Base.T_ℚ_6] ->
  [MAlonzo.Code.Data.Rational.Base.T_ℚ_6] ->
  T_StrictAt_16 -> MAlonzo.Code.Data.Rational.Base.T__'60'__62
d_sumQStrict_88 v0 v1 v2
  = case coe v2 of
      C_here_26 v7 v8
        -> case coe v0 of
             (:) v9 v10
               -> case coe v1 of
                    (:) v11 v12
                      -> coe
                           MAlonzo.Code.Data.Rational.Properties.d_'43''45'mono'45''60''45''8804'_4418
                           (coe v9) (coe v11) (coe d_sumQ_38 (coe v10))
                           (coe d_sumQ_38 (coe v12)) (coe v7)
                           (coe d_sumQMono_78 (coe v10) (coe v12) (coe v8))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_there_36 v7 v8
        -> case coe v0 of
             (:) v9 v10
               -> case coe v1 of
                    (:) v11 v12
                      -> coe
                           MAlonzo.Code.Data.Rational.Properties.d_'43''45'mono'45''8804''45''60'_4436
                           (coe v9) (coe v11) (coe d_sumQ_38 (coe v10))
                           (coe d_sumQ_38 (coe v12)) (coe v7)
                           (coe d_sumQStrict_88 (coe v10) (coe v12) (coe v8))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
